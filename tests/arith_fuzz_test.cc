#include <gtest/gtest.h>
#include <random>
#include <string>

#include "btgly/bitvec.hh"
#include "btgly/strbitvec.hh"

using namespace btgly;

TEST(BitVecArithmeticFuzz, SmallVsStrReference) {
  std::mt19937_64 rng(12345);
  std::uniform_int_distribution<int> widthDist(0, 64);
  for(int i = 0; i < 1000; ++i) {
    std::size_t w = static_cast<std::size_t>(widthDist(rng));
    std::uint64_t mask = w == 64 ? ~std::uint64_t{0} : ((std::uint64_t{1} << w) - 1);
    std::uint64_t a = rng() & mask;
    std::uint64_t b = rng() & mask;

    BitVec ba = BitVec::from_int(std::to_string(a), w);
    BitVec bb = BitVec::from_int(std::to_string(b), w);
    StrBitVec sa = StrBitVec::from_int(std::to_string(a), w);
    StrBitVec sb = StrBitVec::from_int(std::to_string(b), w);

    BitVec add_res = ba.add(bb);
    StrBitVec add_ref = sa.add(sb);
    EXPECT_EQ(add_res.bits(), add_ref.bits());

    BitVec sub_res = ba.sub(bb);
    StrBitVec sub_ref = sa.sub(sb);
    EXPECT_EQ(sub_res.bits(), sub_ref.bits());

    BitVec neg_res = ba.neg();
    StrBitVec neg_ref = sa.neg();
    EXPECT_EQ(neg_res.bits(), neg_ref.bits());

    EXPECT_EQ(ba.uaddo(bb), sa.uaddo(sb));
    EXPECT_EQ(ba.usubo(bb), sa.usubo(sb));
    EXPECT_EQ(ba.saddo(bb), sa.saddo(sb));
    EXPECT_EQ(ba.ssubo(bb), sa.ssubo(sb));
    EXPECT_EQ(ba.nego(), sa.nego());

    BitVec mul_res = ba.mul(bb);
    StrBitVec mul_ref = sa.mul(sb);
    EXPECT_EQ(mul_res.bits(), mul_ref.bits());

    BitVec udiv_res = ba.udiv(bb);
    StrBitVec udiv_ref = sa.udiv(sb);
    EXPECT_EQ(udiv_res.bits(), udiv_ref.bits());

    BitVec urem_res = ba.urem(bb);
    StrBitVec urem_ref = sa.urem(sb);
    EXPECT_EQ(urem_res.bits(), urem_ref.bits());

    BitVec sdiv_res = ba.sdiv(bb);
    StrBitVec sdiv_ref = sa.sdiv(sb);
    EXPECT_EQ(sdiv_res.bits(), sdiv_ref.bits());

    BitVec srem_res = ba.srem(bb);
    StrBitVec srem_ref = sa.srem(sb);
    EXPECT_EQ(srem_res.bits(), srem_ref.bits());

    BitVec smod_res = ba.smod(bb);
    StrBitVec smod_ref = sa.smod(sb);
    EXPECT_EQ(smod_res.bits(), smod_ref.bits());

    EXPECT_EQ(ba.umulo(bb), sa.umulo(sb));
    EXPECT_EQ(ba.sdivo(bb), sa.sdivo(sb));
  }
}

