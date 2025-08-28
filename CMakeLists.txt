cmake_minimum_required(VERSION 3.28.2)

if (NOT DEFINED BOUTGLAY_MONOREPO)
    project(btgly)
endif ()

set(CMAKE_CXX_STANDARD 20)

include_directories(include)

add_library(btgly.bitvec STATIC src/bitvec.cc)

include(FetchContent)
FetchContent_Declare(
        googletest
        URL https://github.com/google/googletest/archive/refs/tags/v1.14.0.zip
)
FetchContent_MakeAvailable(googletest)

enable_testing()

add_executable(btgly.bitvec.tests tests/bitvec_test.cc)
target_link_libraries(btgly.bitvec.tests PRIVATE btgly.bitvec gtest_main)
add_test(NAME bitvec_tests COMMAND btgly.bitvec.tests)

