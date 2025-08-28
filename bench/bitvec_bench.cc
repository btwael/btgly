#include <benchmark/benchmark.h>
#include <btgly/bitvec.hh>
#include <btgly/strbitvec.hh>
#include <string>
#include <vector>

using namespace std;
using btgly::BitVec;
using btgly::StrBitVec;

static const int widths[] = {1,5,8,13,16,25,32,55,64,99,128};

// Helpers to generate test vectors

template <typename BV>
BV make_a(size_t w){ return BV::from_int("0x123456789ABCDEF", w); }

template <typename BV>
BV make_b(size_t w){ return BV::from_int("0xFEDCBA987654321", w); }

template <typename BV>
BV make_shift(size_t w){ return BV::from_int("1", w); }

static void register_benchmarks(){
  for(int w : widths){
    // Bitwise AND
    benchmark::RegisterBenchmark(("BitVec/and/"+to_string(w)).c_str(), [w](benchmark::State& st){
      BitVec a = make_a<BitVec>(w);
      BitVec b = make_b<BitVec>(w);
      for(auto _ : st){ benchmark::DoNotOptimize(a.$and(b)); }
    });
    benchmark::RegisterBenchmark(("StrBitVec/and/"+to_string(w)).c_str(), [w](benchmark::State& st){
      StrBitVec a = make_a<StrBitVec>(w);
      StrBitVec b = make_b<StrBitVec>(w);
      for(auto _ : st){ benchmark::DoNotOptimize(a.$and(b)); }
    });

    // Bitwise OR
    benchmark::RegisterBenchmark(("BitVec/or/"+to_string(w)).c_str(), [w](benchmark::State& st){
      BitVec a = make_a<BitVec>(w);
      BitVec b = make_b<BitVec>(w);
      for(auto _ : st){ benchmark::DoNotOptimize(a.$or(b)); }
    });
    benchmark::RegisterBenchmark(("StrBitVec/or/"+to_string(w)).c_str(), [w](benchmark::State& st){
      StrBitVec a = make_a<StrBitVec>(w);
      StrBitVec b = make_b<StrBitVec>(w);
      for(auto _ : st){ benchmark::DoNotOptimize(a.$or(b)); }
    });

    // Bitwise XOR
    benchmark::RegisterBenchmark(("BitVec/xor/"+to_string(w)).c_str(), [w](benchmark::State& st){
      BitVec a = make_a<BitVec>(w);
      BitVec b = make_b<BitVec>(w);
      for(auto _ : st){ benchmark::DoNotOptimize(a.$xor(b)); }
    });
    benchmark::RegisterBenchmark(("StrBitVec/xor/"+to_string(w)).c_str(), [w](benchmark::State& st){
      StrBitVec a = make_a<StrBitVec>(w);
      StrBitVec b = make_b<StrBitVec>(w);
      for(auto _ : st){ benchmark::DoNotOptimize(a.$xor(b)); }
    });

    // Shifts
    benchmark::RegisterBenchmark(("BitVec/shl/"+to_string(w)).c_str(), [w](benchmark::State& st){
      BitVec a = make_a<BitVec>(w);
      BitVec amt = make_shift<BitVec>(w);
      for(auto _ : st){ benchmark::DoNotOptimize(a.shl(amt)); }
    });
    benchmark::RegisterBenchmark(("StrBitVec/shl/"+to_string(w)).c_str(), [w](benchmark::State& st){
      StrBitVec a = make_a<StrBitVec>(w);
      StrBitVec amt = make_shift<StrBitVec>(w);
      for(auto _ : st){ benchmark::DoNotOptimize(a.shl(amt)); }
    });
    benchmark::RegisterBenchmark(("BitVec/lshr/"+to_string(w)).c_str(), [w](benchmark::State& st){
      BitVec a = make_a<BitVec>(w);
      BitVec amt = make_shift<BitVec>(w);
      for(auto _ : st){ benchmark::DoNotOptimize(a.lshr(amt)); }
    });
    benchmark::RegisterBenchmark(("StrBitVec/lshr/"+to_string(w)).c_str(), [w](benchmark::State& st){
      StrBitVec a = make_a<StrBitVec>(w);
      StrBitVec amt = make_shift<StrBitVec>(w);
      for(auto _ : st){ benchmark::DoNotOptimize(a.lshr(amt)); }
    });
    benchmark::RegisterBenchmark(("BitVec/ashr/"+to_string(w)).c_str(), [w](benchmark::State& st){
      BitVec a = make_a<BitVec>(w);
      BitVec amt = make_shift<BitVec>(w);
      for(auto _ : st){ benchmark::DoNotOptimize(a.ashr(amt)); }
    });
    benchmark::RegisterBenchmark(("StrBitVec/ashr/"+to_string(w)).c_str(), [w](benchmark::State& st){
      StrBitVec a = make_a<StrBitVec>(w);
      StrBitVec amt = make_shift<StrBitVec>(w);
      for(auto _ : st){ benchmark::DoNotOptimize(a.ashr(amt)); }
    });

    // Arithmetic
    benchmark::RegisterBenchmark(("BitVec/add/"+to_string(w)).c_str(), [w](benchmark::State& st){
      BitVec a = make_a<BitVec>(w);
      BitVec b = make_b<BitVec>(w);
      for(auto _ : st){ benchmark::DoNotOptimize(a.add(b)); }
    });
    benchmark::RegisterBenchmark(("StrBitVec/add/"+to_string(w)).c_str(), [w](benchmark::State& st){
      StrBitVec a = make_a<StrBitVec>(w);
      StrBitVec b = make_b<StrBitVec>(w);
      for(auto _ : st){ benchmark::DoNotOptimize(a.add(b)); }
    });
    benchmark::RegisterBenchmark(("BitVec/sub/"+to_string(w)).c_str(), [w](benchmark::State& st){
      BitVec a = make_a<BitVec>(w);
      BitVec b = make_b<BitVec>(w);
      for(auto _ : st){ benchmark::DoNotOptimize(a.sub(b)); }
    });
    benchmark::RegisterBenchmark(("StrBitVec/sub/"+to_string(w)).c_str(), [w](benchmark::State& st){
      StrBitVec a = make_a<StrBitVec>(w);
      StrBitVec b = make_b<StrBitVec>(w);
      for(auto _ : st){ benchmark::DoNotOptimize(a.sub(b)); }
    });
    benchmark::RegisterBenchmark(("BitVec/mul/"+to_string(w)).c_str(), [w](benchmark::State& st){
      BitVec a = make_a<BitVec>(w);
      BitVec b = make_b<BitVec>(w);
      for(auto _ : st){ benchmark::DoNotOptimize(a.mul(b)); }
    });
    benchmark::RegisterBenchmark(("StrBitVec/mul/"+to_string(w)).c_str(), [w](benchmark::State& st){
      StrBitVec a = make_a<StrBitVec>(w);
      StrBitVec b = make_b<StrBitVec>(w);
      for(auto _ : st){ benchmark::DoNotOptimize(a.mul(b)); }
    });
    benchmark::RegisterBenchmark(("BitVec/udiv/"+to_string(w)).c_str(), [w](benchmark::State& st){
      BitVec a = make_a<BitVec>(w);
      BitVec b = make_b<BitVec>(w);
      for(auto _ : st){ benchmark::DoNotOptimize(a.udiv(b)); }
    });
    benchmark::RegisterBenchmark(("StrBitVec/udiv/"+to_string(w)).c_str(), [w](benchmark::State& st){
      StrBitVec a = make_a<StrBitVec>(w);
      StrBitVec b = make_b<StrBitVec>(w);
      for(auto _ : st){ benchmark::DoNotOptimize(a.udiv(b)); }
    });
    benchmark::RegisterBenchmark(("BitVec/sdiv/"+to_string(w)).c_str(), [w](benchmark::State& st){
      BitVec a = make_a<BitVec>(w);
      BitVec b = make_b<BitVec>(w);
      for(auto _ : st){ benchmark::DoNotOptimize(a.sdiv(b)); }
    });
    benchmark::RegisterBenchmark(("StrBitVec/sdiv/"+to_string(w)).c_str(), [w](benchmark::State& st){
      StrBitVec a = make_a<StrBitVec>(w);
      StrBitVec b = make_b<StrBitVec>(w);
      for(auto _ : st){ benchmark::DoNotOptimize(a.sdiv(b)); }
    });

    // Comparisons
    benchmark::RegisterBenchmark(("BitVec/eq/"+to_string(w)).c_str(), [w](benchmark::State& st){
      BitVec a = make_a<BitVec>(w);
      BitVec b = make_b<BitVec>(w);
      for(auto _ : st){ benchmark::DoNotOptimize(a.eq(b)); }
    });
    benchmark::RegisterBenchmark(("StrBitVec/eq/"+to_string(w)).c_str(), [w](benchmark::State& st){
      StrBitVec a = make_a<StrBitVec>(w);
      StrBitVec b = make_b<StrBitVec>(w);
      for(auto _ : st){ benchmark::DoNotOptimize(a.eq(b)); }
    });
    benchmark::RegisterBenchmark(("BitVec/ult/"+to_string(w)).c_str(), [w](benchmark::State& st){
      BitVec a = make_a<BitVec>(w);
      BitVec b = make_b<BitVec>(w);
      for(auto _ : st){ benchmark::DoNotOptimize(a.ult(b)); }
    });
    benchmark::RegisterBenchmark(("StrBitVec/ult/"+to_string(w)).c_str(), [w](benchmark::State& st){
      StrBitVec a = make_a<StrBitVec>(w);
      StrBitVec b = make_b<StrBitVec>(w);
      for(auto _ : st){ benchmark::DoNotOptimize(a.ult(b)); }
    });
    benchmark::RegisterBenchmark(("BitVec/slt/"+to_string(w)).c_str(), [w](benchmark::State& st){
      BitVec a = make_a<BitVec>(w);
      BitVec b = make_b<BitVec>(w);
      for(auto _ : st){ benchmark::DoNotOptimize(a.slt(b)); }
    });
    benchmark::RegisterBenchmark(("StrBitVec/slt/"+to_string(w)).c_str(), [w](benchmark::State& st){
      StrBitVec a = make_a<StrBitVec>(w);
      StrBitVec b = make_b<StrBitVec>(w);
      for(auto _ : st){ benchmark::DoNotOptimize(a.slt(b)); }
    });
  }
}

static int bench_registrar = (register_benchmarks(), 0);

BENCHMARK_MAIN();
