cmake_minimum_required(VERSION 3.28.2)

if (NOT DEFINED BOUTGLAY_MONOREPO)
    project(btgly)
endif ()

set(CMAKE_CXX_STANDARD 20)

include_directories(include)

add_library(btgly.bitvec STATIC src/bitvec.cc)
add_library(btgly.strbitvec STATIC src/strbitvec.cc)

include(FetchContent)
FetchContent_Declare(
        googletest
        URL https://github.com/google/googletest/archive/refs/tags/v1.14.0.zip
)
FetchContent_MakeAvailable(googletest)

# Google Benchmark for microbenchmarks
FetchContent_Declare(
        benchmark
        URL https://github.com/google/benchmark/archive/refs/tags/v1.8.3.zip
)
FetchContent_MakeAvailable(benchmark)

enable_testing()

add_executable(btgly.bitvec.tests tests/bitvec_test.cc tests/strbitvec_test.cc tests/arith_fuzz_test.cc tests/width_property_test.cc)
target_link_libraries(btgly.bitvec.tests PRIVATE btgly.bitvec btgly.strbitvec gtest_main)
add_test(NAME bitvec_tests COMMAND btgly.bitvec.tests)

# Microbenchmark target
add_executable(bitvec_bench bench/bitvec_bench.cc)
target_link_libraries(bitvec_bench PRIVATE btgly.bitvec btgly.strbitvec benchmark::benchmark)

