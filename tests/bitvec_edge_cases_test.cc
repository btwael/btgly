#include <gtest/gtest.h>
#include "btgly/bitvec.hh"

using namespace btgly;

TEST(BitVecParsing, VariousBasesAndErrors) {
  BitVec hex = BitVec::from_int("0x1f", 8);
  EXPECT_EQ(hex.u_to_int(), "31");
  BitVec oct = BitVec::from_int("0o17", 8);
  EXPECT_EQ(oct.u_to_int(), "15");
  BitVec binUpper = BitVec::from_int("0B101", 3);
  EXPECT_EQ(binUpper.u_to_int(), "5");
  EXPECT_THROW(BitVec::from_int("0b102", 8), std::invalid_argument);
  EXPECT_THROW(BitVec::from_int("0o8", 4), std::invalid_argument);
  EXPECT_THROW(BitVec::from_int("0xG", 4), std::invalid_argument);
}

TEST(BitVecShiftRotate, LargeAmounts) {
  BitVec v = BitVec::from_int("0b1001", 4);
  EXPECT_EQ(v.rotate_left(4).u_to_int(), "9");
  EXPECT_EQ(v.rotate_right(6).u_to_int(), "6");
  BitVec shl = BitVec::from_int("3", 4).shl(BitVec::from_int("4", 4));
  EXPECT_TRUE(shl.is_zero());
  BitVec lshr = BitVec::from_int("8", 4).lshr(BitVec::from_int("5", 4));
  EXPECT_TRUE(lshr.is_zero());
  BitVec ashrNeg = BitVec::from_int("-4", 4).ashr(BitVec::from_int("5", 4));
  EXPECT_EQ(ashrNeg.s_to_int(), "-1");
  BitVec ashrPos = BitVec::from_int("4", 4).ashr(BitVec::from_int("5", 4));
  EXPECT_TRUE(ashrPos.is_zero());
}

TEST(BitVecDivision, DivisionByZeroAndOverflow) {
  BitVec v = BitVec::from_int("5", 4);
  EXPECT_EQ(v.udiv(BitVec::zeros(4)).u_to_int(), "15");
  EXPECT_EQ(v.urem(BitVec::zeros(4)).u_to_int(), "5");
  BitVec neg = BitVec::from_int("-3", 4);
  EXPECT_EQ(neg.sdiv(BitVec::zeros(4)).s_to_int(), "-1");
  EXPECT_EQ(neg.srem(BitVec::zeros(4)).s_to_int(), "-3");
  EXPECT_EQ(neg.smod(BitVec::zeros(4)).s_to_int(), "-3");
  BitVec min = BitVec::from_int("-8", 4);
  BitVec minusOne = BitVec::from_int("-1", 4);
  BitVec sdivRes = min.sdiv(minusOne);
  EXPECT_EQ(sdivRes.s_to_int(), "-8");
  BitVec sremRes = min.srem(minusOne);
  EXPECT_TRUE(sremRes.is_zero());
  BitVec smodRes = min.smod(minusOne);
  EXPECT_TRUE(smodRes.is_zero());
}

TEST(BitVecMisc, RepeatExtractAndOverflowFalse) {
  BitVec v = BitVec::from_int("1", 1);
  BitVec r0 = v.repeat(0);
  EXPECT_EQ(r0.width(), 0u);
  BitVec eSrc = BitVec::from_int("0b101", 3);
  EXPECT_THROW(eSrc.extract(1, 2), std::invalid_argument);
  EXPECT_THROW(eSrc.extract(3, 1), std::out_of_range);
  BitVec uaddLhs = BitVec::from_int("3", 4);
  BitVec uaddRhs = BitVec::from_int("1", 4);
  EXPECT_FALSE(uaddLhs.uaddo(uaddRhs));
  BitVec saddLhs = BitVec::from_int("1", 4);
  BitVec saddRhs = BitVec::from_int("1", 4);
  EXPECT_FALSE(saddLhs.saddo(saddRhs));
  BitVec umulLhs = BitVec::from_int("2", 4);
  BitVec umulRhs = BitVec::from_int("3", 4);
  EXPECT_FALSE(umulLhs.umulo(umulRhs));
  BitVec smulLhs = BitVec::from_int("2", 4);
  BitVec smulRhs = BitVec::from_int("2", 4);
  EXPECT_FALSE(smulLhs.smulo(smulRhs));
  BitVec usubLhs = BitVec::from_int("5", 4);
  BitVec usubRhs = BitVec::from_int("3", 4);
  EXPECT_FALSE(usubLhs.usubo(usubRhs));
  BitVec ssubLhs = BitVec::from_int("2", 4);
  BitVec ssubRhs = BitVec::from_int("1", 4);
  EXPECT_FALSE(ssubLhs.ssubo(ssubRhs));
  BitVec sdivoLhs = BitVec::from_int("4", 4);
  BitVec sdivoRhs = BitVec::from_int("2", 4);
  EXPECT_FALSE(sdivoLhs.sdivo(sdivoRhs));
}

TEST(BitVecParsing, SignPrefixesAndLargeDecimal) {
  BitVec plus = BitVec::from_int("+42", 8);
  EXPECT_EQ(plus.u_to_int(), "42");
  BitVec negBin = BitVec::from_int("-0b1010", 5);
  EXPECT_EQ(negBin.s_to_int(), "-10");
  BitVec negHex = BitVec::from_int("-0x1F", 8);
  EXPECT_EQ(negHex.s_to_int(), "-31");
  BitVec bigDec = BitVec::from_int("12345678901234567890", 64);
  EXPECT_EQ(bigDec.u_to_int(), "12345678901234567890");
}

TEST(BitVecShiftRotate, ZeroAmountsAndZeroWidth) {
  BitVec v = BitVec::from_int("0b1010", 4);
  BitVec shl0 = v.shl(BitVec::zeros(4));
  EXPECT_EQ(shl0.u_to_int(), "10");
  BitVec lshr0 = v.lshr(BitVec::zeros(4));
  EXPECT_EQ(lshr0.u_to_int(), "10");
  BitVec ashr0 = BitVec::from_int("-4", 4).ashr(BitVec::zeros(4));
  EXPECT_EQ(ashr0.s_to_int(), "-4");
  BitVec zeroW = BitVec::zeros(0);
  BitVec shlZW = zeroW.shl(BitVec::from_int("1", 1));
  EXPECT_EQ(shlZW.width(), 0u);
  BitVec lshrZW = zeroW.lshr(BitVec::from_int("1", 1));
  EXPECT_EQ(lshrZW.width(), 0u);
}

TEST(BitVecSignedArith, MixedSigns) {
  BitVec pos = BitVec::from_int("6", 4);
  BitVec neg = BitVec::from_int("-2", 4);
  BitVec sdiv = pos.sdiv(neg);
  EXPECT_EQ(sdiv.s_to_int(), "-3");
  BitVec srem = pos.srem(neg);
  EXPECT_EQ(srem.s_to_int(), "0");
  BitVec smod = BitVec::from_int("-7", 4).smod(BitVec::from_int("3", 4));
  EXPECT_EQ(smod.s_to_int(), "2");
}
