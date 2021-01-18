/**

<< "Please use this program the following way:" << '\n'
      << "bin [form] [strmlen] [b1]" << '\n'
      << "form should be 0 - 9" << '\n'
      << "strmlen, b1 are natural numbers" << '\n'
      << std::endl;

*/

extern crate signal_monitor;

use std::time::{ Instant, Duration };
use signal_monitor::utils::*;
use signal_monitor::utils::semiring::*;
use signal_monitor::eval::*;
use signal_monitor::query::*;
use signal_monitor::sink::*;
use signal_monitor::qmtl::*;

use std::env;
use std::process::exit;

pub fn measure<Q:Query<Float64,Float64>>(q: Q, strmlen : u32, desc: String){

    let buff = [ 0.3954132773952119 , 0.7802043456276684 , 0.9056838067459964 ,
                     0.9919627616090054 , 0.3153684746871873 , 0.868398327264566 ,
                     0.8470972988532026 , 0.7257287331532113 , 0.8272851976726383 ,
                     0.15529920818726972
                ];

    println!("Tool=semiring-monitor");
    println!("Formula={}",desc);
    println!("StreamLength={}",strmlen);

    let start: Instant = Instant::now();
	let mut snk = SLastCount::default();
	let mut eval = q.start(&mut snk);

    for iii in 0..strmlen{
        eval.next(Float64::new(buff[(iii as usize)%10]), &mut snk);
    }

    let now: Instant = Instant::now();
    let elapsed : Duration = now.duration_since(start);

    println!("TimeUnit={}","ms");
    println!("TimeElapsed={}", elapsed.as_millis());

    eval.end(&mut snk);
}

fn main() {
    fn over_half(x: Float64) -> Float64 { x - Float64::new(1.0 / 2.0) }
    fn over_zero(x: Float64) -> Float64 { x - Float64::new(0.0) }
    fn over_quarter(x: Float64) -> Float64 {x - Float64::new(1.0 / 4.0) }
    fn over_three_quarters (x: Float64) -> Float64 {x - Float64::new(3.0 / 4.0) }

    let p = prop::atomic::<Float64,SemiringFloat64>(over_half);
    let q = prop::atomic::<Float64,SemiringFloat64>(over_zero);
    let r = prop::atomic::<Float64,SemiringFloat64>(over_quarter);
    let s = prop::atomic::<Float64,SemiringFloat64>(over_three_quarters);

    // P1: (once[:2000]{q}) -> ((not{p}) since {q})
    let form0 = |b| prop::implies(past::sometime_up(b, q.clone()), past::since(prop::not(p.clone()), q.clone()));

    // P2: {r} -> (historically[:2000](not{p})
    let form1 = |b| prop::implies(r.clone(), past::always_up(b, prop::not(p.clone())));

    // P3: ({r} && !{q} && once{q}) -> (!{p} since[1000:2000] {q})
    let form2 = |b| prop::implies(prop::and(prop::and(r.clone(), prop::not(q.clone())), past::sometime(q.clone())),
                          past::since_lo_up(b, 2*b, prop::not(p.clone()), q.clone()));

    // P4: (once[:2000]({y > 0.25})) -> ({{x > 0.5}} since {y > 0.25})
    let form3 = |b| prop::implies(past::sometime_up(b, q.clone()), past::since(p.clone(), q.clone()));

    // P5: once[:2000]{q} -> ({p} since {q})
    let form4 = |b| prop::implies(past::sometime_up(b, p.clone()), past::since(p.clone(), q.clone()));

    // P6: ({r} && !{q} && once {q}) -> ({p} since[1000:2000] {q})
    let form5 = |b| prop::implies(prop::and(prop::and(r.clone(), prop::not(q.clone())), past::sometime(q.clone())),
                          past::since_lo_up(b, 2*b, p.clone(), q.clone()));

    // P7: once[:2000]{p}
	let form6 = |b| past::sometime_up(b, p.clone());

    // P8: ({r} && !{p} && once {p}) -> ((once[:2000]({p} or {q})) since {p})
    let form7 = |b| prop::implies(prop::and(prop::and(r.clone(), prop::not(p.clone())), past::sometime(p.clone())),
                          past::since(past::sometime_up(b, prop::or(p.clone(), q.clone())), p.clone()));

    // P9: ({s} -> once[1000:2000] {p}) and !(!{s} since[1000:] {p})
    let form8 = |b| prop::and(prop::implies(s.clone(), past::sometime_lo_up(b, 2*b, p.clone())),
                      prop::not(past::since_lo(b, prop::not(s.clone()), p.clone())));

    // P10: ({r} && !{q} && once{q}) -> ((({s} -> once[1000:2000]{p}) and !(!{s} since[1000:]{p})))
    let form9 = |b| prop::implies(prop::and(prop::and(r.clone(), prop::not(q.clone())), past::sometime(q.clone())),
                                  prop::and(prop::implies(s.clone(), past::sometime_lo_up(b, 2*b, p.clone()))
                                          , prop::not(past::since_lo(b, prop::not(s.clone()), p.clone()))));

    let args: Vec<String> = env::args().collect();
    let mut formarg : i32 = 0;
    let mut bound : u32 = 0;
    let mut strmlen : u32 = 0;

    let describer = |f, b| {
        match f {
            0 => format!("((once[:{}]{{x > 0.0}}) -> ((not {{x > 0.5}}) since {{x > 0.0}}))", b),
            1 => format!("({{x > 0.25}} -> (historically[:{}](not {{x > 0.5}})))", b),
            2 => format!("({{x > 0.25}} && !{{x > 0.0}} && once {{x > 0.0}} ) -> ((not {{x > 0.5}}) since[{}:{}] {{x > 0.0}})", b, 2*b),
            3 => format!("((once[:{}]({{x > 0.0}})) -> ({{x > 0.5}} since {{x > 0.0}}))", b),
            4 => format!("({{x > 0.25}} -> (historically[:{}]{{x > 0.5}}))", b),
            5 => format!("(({{x > 0.25}} && !{{x > 0.0}} && once {{x > 0.0}}) -> ({{x > 0.5}} since[{}:{}] {{x > 0.0}}))", b,2*b),
            6 => format!("(once[:{}]{{x > 0.5}})", b),
            7 => format!("(({{x > 0.25}} && !{{x > 0.0}} && once {{x > 0.0}}) -> ((once[:{}]({{x > 0.5}} or {{x > 0.0}})) since {{x > 0.0}}))", b),
            8 => format!("(({{x > 0.75}} -> once[{}:{}] {{x > 0.5}}) and not( not({{x > 0.75}}) since[{}:] {{x > 0.5}}))", b, 2*b, b),
            9 => format!("({{x > 0.25}} && !{{x > 0.0}} && once {{x > 0.0}}) -> ((({{x > 0.75}} -> once[{}:{}] {{x > 0.5}}) and not( not({{x > 0.75}}) since[{}:] {{x > 0.5}})) since {{x > 0.0}})", b, 2*b, b),
            _ => "bad formula".to_string()
        }
    };

    match args.len(){
        4 =>{
            match args[1].parse(){
                Ok(f) => formarg = f,
                _ => { println!("couldn't parse formarg"); exit(1); },
            }
            match args[2].parse(){
                Ok(s) => strmlen = s,
                _ => { println!("couldn't parse strmlen"); exit(1); },
            }
            match args[3].parse(){
                Ok(b) => bound = b,
                _ => { println!("couldn't parse bound"); exit(1); },
            }
        }
        _ => { println!("Please check top of source code for usage instructions"); exit(1); }
    }

    match formarg{
        0 => measure(form0(bound).get_monitor(), strmlen, describer(formarg, bound)),
        1 => measure(form1(bound).get_monitor(), strmlen, describer(formarg, bound)),
        2 => measure(form2(bound).get_monitor(), strmlen, describer(formarg, bound)),
        3 => measure(form3(bound).get_monitor(), strmlen, describer(formarg, bound)),
        4 => measure(form4(bound).get_monitor(), strmlen, describer(formarg, bound)),
        5 => measure(form5(bound).get_monitor(), strmlen, describer(formarg, bound)),
        6 => measure(form6(bound).get_monitor(), strmlen, describer(formarg, bound)),
        7 => measure(form7(bound).get_monitor(), strmlen, describer(formarg, bound)),
        8 => measure(form8(bound).get_monitor(), strmlen, describer(formarg, bound)),
        9 => measure(form9(bound).get_monitor(), strmlen, describer(formarg, bound)),
        _ => println!("bad formarg"),
    };

}
