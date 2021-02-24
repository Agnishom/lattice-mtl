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

void measure(std::string formula, int strmlen){
  std::cout << "Tool=" << "Reelay" << std::endl;
  std::cout << "Formula=" << formula << std::endl;
  std::cout << "StreamLength=" << strmlen << std::endl;
  int cnt = 0;
  auto net1 = reelay::discrete_timed_robustness_network<time_type, value_t, input_t>::make(formula);
  auto start = std::chrono::high_resolution_clock::now();
  for (int i = 0; i < strmlen; i++){
    if (net1.output() > 0) {
      cnt++;
    }
    net1.update(buff[i%size]);
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

  if (argc != 4){
    std::cerr << "Please use this program the following way:" << '\n'
              << "bin [form] [strmlen] [b1]" << '\n'
              << "form should be 0 - 9" << '\n'
              << "strmlen, b1 are natural numbers" << '\n'
              << std::endl;
    return 0;
  }

  int form = std::stoi(argv[1]);
  int strmlen = std::stoi(argv[2]);
  int bound = std::stoi(argv[3]);

  if (form == 0){
    measure("((once[:"+ std::to_string(bound) + "]{x > 0.00}) -> ((not {x > 0.5}) since {x > 0.00}))",
            strmlen);

  }
  else if (form == 1){
    measure("({x > 0.25} -> (historically[:" + std::to_string(bound) +  "](not {x > 0.5})))",
            strmlen);
  }
  else if (form == 2){
    measure("({x > 0.25} && !{x > 0.0} && once {x > 0.0} ) -> ((not {x > 0.5}) since[" + std::to_string(bound) + ":" + std::to_string(2*bound) + "] {x > 0.0})",
            strmlen);
  }
  else if (form == 3){
    measure("((once[:" + std::to_string(bound) + "]({x > 0.0})) -> ({x > 0.5} since {x > 0.0}))",
            strmlen);
  }
  else if (form == 4){
    measure("({x > 0.25} -> (historically[:" + std::to_string(bound) + "]{x > 0.5}))",
            strmlen);
  }
  else if (form == 5){
    measure("(({x > 0.25} && !{x > 0.0} && once {x > 0.0}) -> ({x > 0.5} since[" + std::to_string(bound) + ":" + std::to_string(2*bound) + "] {x > 0.0}))",
            strmlen);
  }
  else if (form == 6){
    measure("(once[:" + std::to_string(bound) + "]{x > 0.5})",
            strmlen);
  }
  else if (form == 7){
    measure("(({x > 0.25} && !{x > 0.0} && once {x > 0.0}) -> ((once[:" + std::to_string(bound) + "]({x > 0.5} or {x > 0.0})) since {x > 0.0}))",
            strmlen);
  }
  else if (form == 8){
    measure("(({x > 0.75} -> once[" + std::to_string(bound) + ":" + std::to_string(2*bound) + "] {x > 0.5}) and not( not({x > 0.75}) since[" + std::to_string(bound) + ":] {x > 0.5}))",
            strmlen);
  }
  else if (form == 9){
    measure("({x > 0.25} && !{x > 0.0} && once {x > 0.0}) -> ((({x > 0.75} -> once[" + std::to_string(bound) + ":" + std::to_string(2*bound) + "] {x > 0.5}) and not( not({x > 0.75}) since[" + std::to_string(bound) + ":] {x > 0.5})) since {x > 0.0})",
            strmlen);
  }
  else
    std::cout << "Need Formula within 0-9" << std::endl;

}
