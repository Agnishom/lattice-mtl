#include <ctime>
#include "iostream"
#include "reelay/common.hpp"
#include "reelay/json.hpp"
#include "reelay/networks/discrete_timed_robustness_network.hpp"
#include "reelay/options.hpp"
#include "vector"
#include <random>
#include <sys/resource.h>

using time_type = int64_t;

using input_t = reelay::json;
using value_t = double;
value_t top = reelay::infinity<value_t>::value();
value_t bot = -reelay::infinity<value_t>::value();

std::vector<input_t> buff;

const int size = 10;

void measure(std::string formula, int strmlen, int input_type){
  std::cout << "Tool=" << "Reelay" << std::endl;
  std::cout << "Formula=" << formula << std::endl;
  std::cout << "StreamLength=" << strmlen << std::endl;
  if (input_type == 0)
    std::cout << "InputType=Random" << std::endl;
  else if (input_type == 1)
    std::cout << "InputType=Increasing" << std::endl;
  else if (input_type == 2)
    std::cout << "InputType=Decreasing" << std::endl;
  int cnt = 0;
  auto net1 = reelay::discrete_timed_robustness_network<time_type, value_t, input_t>::make(formula);
  auto start = std::chrono::high_resolution_clock::now();
  for (int i = 0; i < strmlen; i++){
    if (net1.output() > 0) {
      cnt++;
    }
    input_t inp;
    if (input_type == 0)
      inp = buff[i%size];
    else if (input_type == 1)
      inp = input_t{{"x", i}};
    else if (input_type == 2)
      inp = input_t{{"x", -i}};
    net1.update(inp);
  }
  auto end = std::chrono::high_resolution_clock::now();
  std::cout << "TimeUnit=ms" << std::endl;
  std::chrono::milliseconds duration = std::chrono::duration_cast<std::chrono::milliseconds>(end - start);
  std::cout << "TimeElapsed=" << duration.count() << std::endl;
  std::cout << cnt << std::endl;
}

int main(int argc, char* argv[]){

  buff = std::vector<input_t>();
  buff.push_back(input_t{{"x", 0.3954132773952119}});
  buff.push_back(input_t{{"x", 0.7802043456276684}});
  buff.push_back(input_t{{"x", 0.9056838067459964}});
  buff.push_back(input_t{{"x", 0.9919627616090054}});
  buff.push_back(input_t{{"x", 0.3153684746871873}});
  buff.push_back(input_t{{"x", 0.868398327264566}});
  buff.push_back(input_t{{"x", 0.8470972988532026}});
  buff.push_back(input_t{{"x", 0.7257287331532113}});
  buff.push_back(input_t{{"x", 0.8272851976726383}});
  buff.push_back(input_t{{"x", 0.15529920818726972}});

  if (argc != 5){
    std::cerr << "Please use this program the following way:" << '\n'
              << "bin [form] [strmlen] [b1] [inp]" << '\n'
              << "form should be 0 - 7" << '\n'
              << "inp should be 0 - 2" << '\n'
              << "strmlen, b1 are natural numbers" << '\n'
              << "fff == 0 means P_[0,b1]" << '\n'
              << "fff == 1 means P_[b1,b1]" << '\n'
              << "fff == 2 means P_[b1,2*b1]" << '\n'
              << "fff == 3 means P_[b1,inf]" << '\n'
              << "fff == 4 means S_[0,b1]" << '\n'
              << "fff == 5 means S_[b1,b1]" << '\n'
              << "fff == 6 means S_[b1,2*b1]" << '\n'
              << "fff == 7 means S_[b1,inf]" << '\n'
              << "inp == 0 means Random" << '\n'
              << "inp == 1 means Increasing" << '\n'
              << "inp == 2 means Decreasing" << '\n'
              << std::endl;
    return 0;
  }

  int form = std::stoi(argv[1]);
  int strmlen = std::stoi(argv[2]);
  int bound = std::stoi(argv[3]);
  int input_type = std::stoi(argv[4]);

  if (form == 0){
    measure("once[0:" + std::to_string(bound) + "] {x > 0.5}",
            strmlen, input_type);

  }
  else if (form == 1){
    measure("once[" + std::to_string(bound) + ":" + std::to_string(bound) + "] {x > 0.5}",
            strmlen, input_type);
  }
  else if (form == 2){
    measure("once[" + std::to_string(bound) + ":" + std::to_string(2*bound) + "] {x > 0.5}",
            strmlen, input_type);
  }
  else if (form == 3){
    measure("once[" + std::to_string(bound) + ":] {x > 0.5}",
            strmlen, input_type);
  }
  else if (form == 4){
    measure("{x > 0.0} since[0:" + std::to_string(bound) + "] {x > 0.5}",
            strmlen, input_type);

  }
  else if (form == 5){
    measure("{x > 0.0} since[" + std::to_string(bound) + ":" + std::to_string(bound) + "] {x > 0.5}",
            strmlen, input_type);
  }
  else if (form == 6){
    measure("{x > 0.0} since[" + std::to_string(bound) + ":" + std::to_string(2*bound) + "] {x > 0.5}",
            strmlen, input_type);
  }
  else if (form == 7){
    measure("{x > 0.0} since[" + std::to_string(bound) + ":] {x > 0.5}",
            strmlen, input_type);
  }


}
