# generating ourtool benchmarks

rm *.mli *.o *.cmx *.cmi
ocamlopt -o a.out unix.cmxa Extracted.ml Experiments.ml
./a.out | tee ourtool_results

# generating reelay benchmarks

git clone https://github.com/doganulus/reelay.git --recurse-submodules

cp mytest_micro.cpp reelay/test/mytest_micro.cpp

echo "" >> reelay/Makefile
echo "" >> reelay/Makefile
echo "test_zhifu:" >> reelay/Makefile
echo "\tcd test/build && \$(CXX) \$(CXXFLAGS_TEST) main.o \$(ROOT_DIR)/test/mytest_micro.cpp -o mytest_micro -I\$(ROOT_DIR)/include -lcudd" >> reelay/Makefile

cd reelay
make test_main
make test_zhifu

cd test/build
./mytest_micro -r compact | tee ../../../reelay_results

# parsing and plotting the results

cd ../../../
python3 plot_results.py
