extern crate signal_monitor;

use signal_monitor::utils::*;
use signal_monitor::utils::semiring::*;
use signal_monitor::eval::*;
use signal_monitor::query::*;
use signal_monitor::sink::*;
use signal_monitor::qmtl::*;

use std::env;
use std::process::exit;

pub fn interact<Q:Query<Float64,Float64>>(q: Q){

	let mut snk = SPrinter::default();
	let mut eval = q.start(&mut snk);

    loop {
        let mut inpline = String::new();
        std::io::stdin().read_line(&mut inpline).expect("Failed to read line");
		if inpline.trim() == "DONE" { break; }
        let inp = inpline.trim().parse().expect("Failed to parse float");
        eval.next(Float64::new(inp), &mut snk);
    }

}

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
    let formarg : i32;
    let bound : u32;


    match args.len(){
        3 =>{
            match args[1].parse(){
                Ok(f) => formarg = f,
                _ => { println!("couldn't parse formarg"); exit(1); },
            }
            match args[2].parse(){
                Ok(b) => bound = b,
                _ => { println!("couldn't parse bound"); exit(1); },
            }
        }
        n => { println!("Please check top of source code for usage instructions");
		 	   println!("Got {} arguments", n); exit(1); }
    }

    match formarg{
        0 => interact(form0(bound).get_monitor()),
        1 => interact(form1(bound).get_monitor()),
        2 => interact(form2(bound).get_monitor()),
        3 => interact(form3(bound).get_monitor()),
        4 => interact(form4(bound).get_monitor()),
        5 => interact(form5(bound).get_monitor()),
        6 => interact(form6(bound).get_monitor()),
        7 => interact(form7(bound).get_monitor()),
        _ => println!("bad formarg"),
    };

}
