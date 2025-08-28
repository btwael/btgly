#include <gtest/gtest.h>
#include <random>
#include <string>

#include "btgly/bitvec.hh"

using namespace btgly;

namespace {

std::string random_bits(std::size_t w, std::mt19937_64 &rng) {
  std::string s("0b");
  for(std::size_t i = 0; i < w; ++i) {
    s.push_back((rng() & 1) ? '1' : '0');
  }
  return s;
}

BitVec force_zero_large(const BitVec &v) {
  return v.zero_extend(65);
}

BitVec force_sign_large(const BitVec &v) {
  return v.sign_extend(65);
}

BitVec trunc(const BitVec &v, std::size_t w) {
  return w == 0 ? BitVec::zeros(0) : v.extract(w - 1, 0);
}

} // namespace

TEST(BitVecWidthProperty, SmallVsForcedLarge) {
  std::vector<std::size_t> widths = {1, 5, 8, 13, 16, 25, 32, 55, 64, 99, 128};
  std::mt19937_64 rng(123456);

  for(std::size_t w : widths) {
    for(int iter = 0; iter < 50; ++iter) {
      BitVec a = BitVec::from_int(random_bits(w, rng), w);
      BitVec b = BitVec::from_int(random_bits(w, rng), w);

      BitVec az = force_zero_large(a);
      BitVec bz = force_zero_large(b);
      BitVec as = force_sign_large(a);
      BitVec bs = force_sign_large(b);

      // arithmetic
      EXPECT_EQ(a.add(b).bits(), trunc(az.add(bz), w).bits());
      EXPECT_EQ(a.sub(b).bits(), trunc(az.sub(bz), w).bits());
      EXPECT_EQ(a.mul(b).bits(), trunc(az.mul(bz), w).bits());
      EXPECT_EQ(a.neg().bits(), trunc(as.neg(), w).bits());
      EXPECT_EQ(a.udiv(b).bits(), trunc(az.udiv(bz), w).bits());
      EXPECT_EQ(a.urem(b).bits(), trunc(az.urem(bz), w).bits());
      EXPECT_EQ(a.sdiv(b).bits(), trunc(as.sdiv(bs), w).bits());
      EXPECT_EQ(a.srem(b).bits(), trunc(as.srem(bs), w).bits());
      EXPECT_EQ(a.smod(b).bits(), trunc(as.smod(bs), w).bits());

      // bitwise
      EXPECT_EQ(a.$not().bits(), trunc(az.$not(), w).bits());
      EXPECT_EQ(a.$and(b).bits(), trunc(az.$and(bz), w).bits());
      EXPECT_EQ(a.$or(b).bits(), trunc(az.$or(bz), w).bits());
      EXPECT_EQ(a.$xor(b).bits(), trunc(az.$xor(bz), w).bits());
      EXPECT_EQ(a.nand(b).bits(), trunc(az.nand(bz), w).bits());
      EXPECT_EQ(a.nor(b).bits(), trunc(az.nor(bz), w).bits());
      EXPECT_EQ(a.xnor(b).bits(), trunc(az.xnor(bz), w).bits());

      // shifts
      std::size_t sh = w == 0 ? 0 : static_cast<std::size_t>(rng() % w);
      BitVec shv = BitVec::from_int(std::to_string(sh), w);
      BitVec shz = force_zero_large(shv);
      EXPECT_EQ(a.shl(shv).bits(), trunc(az.shl(shz), w).bits());
      EXPECT_EQ(a.lshr(shv).bits(), trunc(az.lshr(shz), w).bits());
      EXPECT_EQ(a.ashr(shv).bits(), trunc(as.ashr(shz), w).bits());

      // Rotations are covered elsewhere; width extension alters semantics, so
      // they are omitted from the small-vs-large comparison here.

      // comparisons
      EXPECT_EQ(a.eq(b), az.eq(bz));
      EXPECT_EQ(a.equals(b), az.equals(bz));
      EXPECT_EQ(a.ult(b), az.ult(bz));
      EXPECT_EQ(a.ule(b), az.ule(bz));
      EXPECT_EQ(a.ugt(b), az.ugt(bz));
      EXPECT_EQ(a.uge(b), az.uge(bz));
      EXPECT_EQ(a.slt(b), as.slt(bs));
      EXPECT_EQ(a.sle(b), as.sle(bs));
      EXPECT_EQ(a.sgt(b), as.sgt(bs));
      EXPECT_EQ(a.sge(b), as.sge(bs));
      EXPECT_EQ(a.comp(b).bits(), az.comp(bz).bits());
      // Reduction operations depend on total width; forcing to large via
      // extension changes the value, so we skip direct comparison here.
    }
  }
}

