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

void interact(std::string formula){
  auto net1 = reelay::discrete_timed_robustness_network<time_type, value_t, input_t>::make(formula);
  float inp;
  while (1){
    std::cin >> inp;
    net1.update(input_t{{"x", inp}});
    std::cout << net1.output() << std::endl;
  }
}

int main(int argc, char* argv[]){

  if (argc != 3){
    std::cerr << "Please use this program the following way:" << '\n'
              << "bin [form] [b1]" << '\n'
              << "form should be 0 - 7" << '\n'
              << "b1 is a natural number" << '\n'
              << "fff == 0 means P_[0,b1]" << '\n'
              << "fff == 1 means P_[b1,b1]" << '\n'
              << "fff == 2 means P_[b1,2*b1]" << '\n'
              << "fff == 3 means P_[b1,inf]" << '\n'
              << "fff == 4 means S_[0,b1]" << '\n'
              << "fff == 5 means S_[b1,b1]" << '\n'
              << "fff == 6 means S_[b1,2*b1]" << '\n'
              << "fff == 7 means S_[b1,inf]" << '\n'
              << std::endl;
    return 0;
  }

  int form = std::stoi(argv[1]);
  int bound = std::stoi(argv[2]);

  if (form == 0){
    interact("once[0:" + std::to_string(bound) + "] {x > 0.5}");

  }
  else if (form == 1){
    interact("once[" + std::to_string(bound) + ":" + std::to_string(bound) + "] {x > 0.5}");
  }
  else if (form == 2){
    interact("once[" + std::to_string(bound) + ":" + std::to_string(2*bound) + "] {x > 0.5}");
  }
  else if (form == 3){
    interact("once[" + std::to_string(bound) + ":] {x > 0.5}");
  }
  else if (form == 4){
    interact("{x > 0.0} since[0:" + std::to_string(bound) + "] {x > 0.5}");

  }
  else if (form == 5){
    interact("{x > 0.0} since[" + std::to_string(bound) + ":" + std::to_string(bound) + "] {x > 0.5}");
  }
  else if (form == 6){
    interact("{x > 0.0} since[" + std::to_string(bound) + ":" + std::to_string(2*bound) + "] {x > 0.5}");
  }
  else if (form == 7){
    interact("{x > 0.0} since[" + std::to_string(bound) + ":] {x > 0.5}");
  }


}
