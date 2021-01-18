/**

<< "Please use this program the following way:" << '\n'
      << "bin [form] [strmlen] [b1]" << '\n'
      << "form should be 0 - 7" << '\n'
      << "strmlen, b1 are natural numbers" << '\n'
      << "fff == 0 means P_[0,b1]" << '\n'
      << "fff == 1 means P_[b1,b1]" << '\n'
      << "fff == 2 means P_[b1,2*b1]" << '\n'
      << "fff == 3 means P_[b1,inf]" << '\n'
      << "fff == 4 means S_[0,b1]" << '\n'
      << "fff == 5 means S_[b1,b1]" << '\n'
      << "fff == 6 means S_[b1,2*b1]" << '\n'
      << "fff == 7 means S_[b1,inf]" << '\n'

**/

extern crate signal_monitor;

use std::time::{ Instant, Duration };
use signal_monitor::utils::*;
use signal_monitor::utils::semiring::*;
use signal_monitor::eval::*;
use signal_monitor::query::*;
use signal_monitor::sink::*;
use signal_monitor::qmtl::*;

use std::env;

fn main() {

    fn over_half(x: Float64) -> Float64 { x - Float64::new(1.0 / 2.0) }
    fn over_zero(x: Float64) -> Float64 { x - Float64::new(0.0) }

    let f_half = prop::atomic::<Float64,SemiringFloat64>(over_half);
    let f_zero = prop::atomic::<Float64,SemiringFloat64>(over_zero);

    let form0 = |b| past::sometime_up(b, f_half.clone());
    let form1 = |b| past::sometime_at(b, f_half.clone());
    let form2 = |b| past::sometime_lo_up(b, 2*b, f_half.clone());
    let form3 = |b| past::sometime_lo(b, f_half.clone());

    let form4 = |b| past::since_up(b, f_half.clone(), f_zero.clone());
    let form5 = |b| past::since_at(b, f_half.clone(), f_zero.clone());
    let form6 = |b| past::since_lo_up(b, 2*b, f_half.clone(), f_zero.clone());
    let form7 = |b| past::since_lo(b, f_half.clone(), f_zero.clone());

    let args: Vec<String> = env::args().collect();
    let mut formarg : i32 = 0;
    let mut bound : u32 = 0;
    let mut strmlen : u32 = 0;

    let describer = |f, b| {
        match f {
            0 => format!("once[0:{}] x > 0.5", b),
            1 => format!("once[{}:{}] x > 0.5", b, b),
            2 => format!("once[{}:{}] x > 0.5", b, 2*b),
            3 => format!("once[{}:] x > 0.5", b),
            4 => format!("x > 0.5 since[0:{}] x > 0", b),
            5 => format!("x > 0.5 since[{}:{}] x > 0", b, b),
            6 => format!("x > 0.5 since[{}:{}] x > 0", b, 2*b),
            7 => format!("x > 0.5 since[{}:] x > 0", b),
            _ => "bad formula".to_string()
        }
    };

    // Rust does not allow arrays of lambdas? I am sad :(
    //
    //let forms : Vec<closure()> = vec![form0, form1, form2, form3, form4, form5, form6, form7];

    match args.len(){
        4 =>{
            match args[1].parse(){
                Ok(f) => formarg = f,
                _ => println!("couldn't parse formarg"),
            }
            match args[2].parse(){
                Ok(s) => strmlen = s,
                _ => println!("couldn't parse strmlen"),
            }
            match args[3].parse(){
                Ok(b) => bound = b,
                _ => println!("couldn't parse bound"),
            }
        }
        _ => println!("Please check top of source code for usage instructions")
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
        _ => println!("bad formarg"),
    };

}

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
