/*

To use this file:

1. Clone the repo at https://github.com/doganulus/reelay.git
2. Add this file to test/
3. Add the following to the Makefile:

```
test_zhifu:
	cd test/build && $(CXX) $(CXXFLAGS_TEST) main.o $(ROOT_DIR)/test/mytest_micro.cpp -o mytest_micro -I$(ROOT_DIR)/include -lcudd
	cd test/build && ./mytest_micro -r compact
```
4. ???
5. Run `make test_zhifu`

*/

#include <ctime>
#include "catch.hpp"
#include "iostream"
#include "reelay/common.hpp"
#include "reelay/json.hpp"
#include "reelay/networks.hpp"
#include "vector"
#include <random>

using time_type = int64_t;

using input_t = reelay::json;
using function_t = std::function<bool(const input_t &)>;
using output_t = float;

const int item_num = 2000000;

std::default_random_engine generator;
std::uniform_real_distribution<float> distribution(0.0,1.0);

std::vector<input_t> sequence;

void measure(int item_num, std::string formula){
  std::cout << "----------------------------------------------" << std::endl;
  std::cout << "tool = Reelay" << std::endl;
  std::cout << formula << std::endl;
  std::cout << "stream length = " << item_num << std::endl;
  auto net1 =
     reelay::detail::discrete_timed<time_type>::robustness<output_t>::network<input_t>::from_temporal_logic(formula);
  auto start = std::chrono::high_resolution_clock::now();
  for (int i = 0; i < item_num; i++){
    // std::cout << sequence[i%1000] << " " << net1->output() << std::endl;
    net1->output();
    net1->update(sequence[i%1000]);
  }
  auto end = std::chrono::high_resolution_clock::now();
  std::chrono::duration<double> duration = (end - start);
  std::cout << "duration = "
            << duration.count() << " sec" << std::endl;
  std::cout << std::fixed << "throughput = " << item_num / duration.count() << " items/sec" << std::endl;
}

void suite(){
  measure(500000, "{x > 0.5}");
  measure(500000, "{x > 0.25}");
  measure(500000, "{x > 0.5} and {x > 0.25}");
  measure(500000, "{x > 0.5} or {x > 0.25}");
  measure(500000, "once {x > 0.5}");
  measure(500000, "historically {x > 0.5}");
  measure(500000, "{x > 0.5} since {x > 0.25}");
  measure(500000, "not ({x <= 0.5} since {x <= 0.25})");
  measure(500000, "historically [10:10] {x > 0.5}");
  measure(500000, "once [10:10] {x > 0.5}");
  measure(500000, "once [100:100] {x > 0.5}");
  measure(500000, "once [1000:1000] {x > 0.5}");
  measure(50000, "once [10000:10000] {x > 0.5}");
  measure(50000, "once [100000:100000] {x > 0.5}");
  measure(500000, "historically[:10] {x > 0.5}");
  measure(500000, "once[:10] {x > 0.5}");
  measure(500000, "once[:100] {x > 0.5}");
  measure(500000, "once[:1000] {x > 0.5}");
  measure(500000, "once[:10000] {x > 0.5}");
  measure(500000, "once[:100000] {x > 0.5}");
  measure(500000, "once[:1000000] {x > 0.5}");
  measure(500000, "{x > 0.5} since[1000:] {x > 0.25}");
  measure(500000, "{x > 0.5} since[1000:2000] {x > 0.25}");
  measure(500000, "pre {x > 0.5}");
  measure(500000, "{x > 0.5} since[:10] {x > 0.25}");
  measure(500000, "{x > 0.5} since[:100] {x > 0.25}");
  measure(500000, "{x > 0.5} since[:1000] {x > 0.25}");
  measure(500000, "{x > 0.5} since[:10000] {x > 0.25}");
  measure(500000, "{x > 0.5} since[:100000] {x > 0.25}");
}

TEST_CASE("Blah") {

  SECTION("Bleh") {
   std::chrono::system_clock::time_point tp = std::chrono::system_clock::now();
   std::chrono::system_clock::duration dtn = tp.time_since_epoch();
   std::cout << "timestamp = " << dtn.count() * std::chrono::system_clock::period::num / std::chrono::system_clock::period::den
            << " seconds after epoch" << std::endl;
   sequence = std::vector<input_t>();
   for (int i = 0; i < 1000; i++) {
      sequence.push_back(input_t{{"x", distribution(generator)},
                                 {"y", distribution(generator)},
                                 {"z", distribution(generator)}});
    }
   for (int i = 0; i < 10; i++)
    suite();
  }
}

/**
----------------------------------------------
{x > 0.5}
stream length = 2000000
duration = 3.3165 sec
throughput = 603044.798031 items/sec
----------------------------------------------
{x > 0.25}
stream length = 2000000
duration = 3.317384 sec
throughput = 602884.655551 items/sec
----------------------------------------------
{x > 0.5} and {x > 0.25}
stream length = 2000000
duration = 6.436973 sec
throughput = 310705.038786 items/sec
----------------------------------------------
{x > 0.5} or {x > 0.25}
stream length = 2000000
duration = 6.431251 sec
throughput = 310981.492919 items/sec
----------------------------------------------
once {x > 0.5}
stream length = 2000000
duration = 3.591302 sec
throughput = 556901.025959 items/sec
----------------------------------------------
historically {x > 0.5}
stream length = 2000000
duration = 3.598623 sec
throughput = 555768.192620 items/sec
----------------------------------------------
{x > 0.5} since {x > 0.25}
stream length = 2000000
duration = 6.557117 sec
throughput = 305012.089226 items/sec
----------------------------------------------
pre {x > 0.5}
stream length = 2000000
duration = 3.573869 sec
throughput = 559617.650172 items/sec
----------------------------------------------
once [10:10] {x > 0.5}
stream length = 2000000
duration = 49.787056 sec
throughput = 40171.083992 items/sec
----------------------------------------------
once [20:20] {x > 0.5}
stream length = 2000000
duration = 65.159558 sec
throughput = 30693.885476 items/sec
----------------------------------------------
historically[:10] {x > 0.5}
stream length = 2000000
duration = 87.688489 sec
throughput = 22808.010842 items/sec
----------------------------------------------
once[:10] {x > 0.5}
stream length = 2000000
duration = 87.769466 sec
throughput = 22786.967815 items/sec
----------------------------------------------
once[:20] {x > 0.5}
stream length = 2000000
duration = 95.601145 sec
throughput = 20920.251466 items/sec
----------------------------------------------
once[:40] {x > 0.5}
stream length = 2000000
duration = 103.147965 sec
throughput = 19389.621426 items/sec
----------------------------------------------
once[10:20] {x > 0.5}
stream length = 2000000
duration = 95.894713 sec
throughput = 20856.207133 items/sec
----------------------------------------------
once[10:30] {x > 0.5}
stream length = 2000000
duration = 100.514942 sec
throughput = 19897.539168 items/sec
----------------------------------------------
once[60:60] {x > 0.5}
stream length = 2000000
duration = 109.835573 sec
throughput = 18209.036859 items/sec
----------------------------------------------
{x > 0.5} since[10:] {x > 0.25}
stream length = 2000000
duration = 255.865389 sec
throughput = 7816.610175 items/sec
----------------------------------------------
{x > 0.5} since[20:] {x > 0.25}
stream length = 2000000
duration = 264.194591 sec
throughput = 7570.177696 items/sec
----------------------------------------------
{x > 0.5} since[40:] {x > 0.25}
stream length = 2000000
duration = 272.205606 sec
throughput = 7347.387252 items/sec
----------------------------------------------
{x > 0.5} since[:5] {x > 0.25}
stream length = 2000000
duration = 212.851012 sec
throughput = 9396.243772 items/sec
----------------------------------------------
{x > 0.5} since[:10] {x > 0.25}
stream length = 2000000
duration = 222.236367 sec
throughput = 8999.427154 items/sec
----------------------------------------------
{x > 0.5} since[:15] {x > 0.25}
stream length = 2000000
duration = 227.472245 sec
throughput = 8792.281444 items/sec
----------------------------------------------
{x > 0.5} since[1:5] {x > 0.25}
stream length = 2000000
duration = 249.087665 sec
throughput = 8029.301641 items/sec
----------------------------------------------
{x > 0.5} since[5:10] {x > 0.25}
stream length = 2000000
duration = 281.030898 sec
throughput = 7116.655188 items/sec
----------------------------------------------
{x > 0.5} since[15:20] {x > 0.25}
stream length = 2000000
duration = 307.114969 sec
throughput = 6512.219217 items/sec
*/
