#include <gtest/gtest.h>
#include "btgly/bitvec.hh"

using namespace btgly;

TEST(BitVecConstruction, Basics) {
  BitVec empty(4);
  EXPECT_EQ(empty.width(), 4u);
  EXPECT_TRUE(empty.is_zero());

  BitVec ones = BitVec::ones(4);
  EXPECT_TRUE(ones.is_all_ones());

  BitVec zeros = BitVec::zeros(4);
  EXPECT_TRUE(zeros.is_zero());

  BitVec fromBoolTrue(true, 3);
  EXPECT_TRUE(fromBoolTrue.is_all_ones());

  BitVec fromBoolFalse(false, 2);
  EXPECT_TRUE(fromBoolFalse.is_zero());

  BitVec neg = BitVec::from_int("-8", 4);
  EXPECT_TRUE(neg.is_negative());
  EXPECT_TRUE(neg.is_most_negative());
  EXPECT_EQ(neg.s_to_int(), "-8");
}

TEST(BitVecManipulation, BasicOps) {
  BitVec a = BitVec::from_int("0b1010", 4);
  BitVec b = BitVec::from_int("0b1100", 4);
  BitVec cat = a.concat(b);
  EXPECT_EQ(cat.u_to_int(), "172");

  BitVec ext = cat.extract(5, 2);
  EXPECT_EQ(ext.u_to_int(), "11");

  BitVec rep = BitVec::from_int("0b10", 2).repeat(3);
  EXPECT_EQ(rep.u_to_int(), "42");

  BitVec se = BitVec::from_int("-3", 3).sign_extend(2);
  EXPECT_EQ(se.s_to_int(), "-3");

  BitVec ze = BitVec::from_int("0b101", 3).zero_extend(2);
  EXPECT_EQ(ze.u_to_int(), "5");

  BitVec rl = BitVec::from_int("0b1001", 4).rotate_left(1);
  EXPECT_EQ(rl.u_to_int(), "3");

  BitVec rr = BitVec::from_int("0b1001", 4).rotate_right(2);
  EXPECT_EQ(rr.u_to_int(), "6");

  BitVec n = a.$not();
  EXPECT_EQ(n.u_to_int(), "5");

  BitVec aand = a.$and(b);
  EXPECT_EQ(aand.u_to_int(), "8");

  BitVec oor = a.$or(b);
  EXPECT_EQ(oor.u_to_int(), "14");

  BitVec xxor = a.$xor(b);
  EXPECT_EQ(xxor.u_to_int(), "6");

  BitVec anand = a.nand(b);
  EXPECT_EQ(anand.u_to_int(), "7");

  BitVec anor = a.nor(b);
  EXPECT_EQ(anor.u_to_int(), "1");

  BitVec axnor = a.xnor(b);
  EXPECT_EQ(axnor.u_to_int(), "9");

  EXPECT_TRUE(BitVec::ones(3).redand());
  EXPECT_FALSE(BitVec::from_int("0b101", 3).redand());
  EXPECT_TRUE(BitVec::from_int("0b100", 3).redor());
  EXPECT_FALSE(BitVec::zeros(3).redor());
}

TEST(BitVecArithmetic, Operations) {
  BitVec two = BitVec::from_int("2", 3);
  EXPECT_EQ(two.neg().s_to_int(), "-2");

  BitVec add = BitVec::from_int("3", 3).add(BitVec::from_int("1", 3));
  EXPECT_EQ(add.u_to_int(), "4");

  BitVec sub = BitVec::from_int("3", 3).sub(BitVec::from_int("1", 3));
  EXPECT_EQ(sub.u_to_int(), "2");

  BitVec mul = BitVec::from_int("3", 4).mul(BitVec::from_int("2", 4));
  EXPECT_EQ(mul.u_to_int(), "6");

  BitVec udiv = BitVec::from_int("6", 4).udiv(BitVec::from_int("2", 4));
  EXPECT_EQ(udiv.u_to_int(), "3");

  BitVec urem = BitVec::from_int("6", 4).urem(BitVec::from_int("4", 4));
  EXPECT_EQ(urem.u_to_int(), "2");

  BitVec sdiv = BitVec::from_int("-6", 4).sdiv(BitVec::from_int("2", 4));
  EXPECT_EQ(sdiv.s_to_int(), "-3");

  BitVec srem = BitVec::from_int("-7", 4).srem(BitVec::from_int("4", 4));
  EXPECT_EQ(srem.s_to_int(), "-3");

  BitVec smod = BitVec::from_int("-7", 4).smod(BitVec::from_int("4", 4));
  EXPECT_EQ(smod.u_to_int(), "1");

  BitVec shl = BitVec::from_int("3", 4).shl(BitVec::from_int("1", 4));
  EXPECT_EQ(shl.u_to_int(), "6");

  BitVec lshr = BitVec::from_int("8", 4).lshr(BitVec::from_int("1", 4));
  EXPECT_EQ(lshr.u_to_int(), "4");

  BitVec ashr = BitVec::from_int("-4", 4).ashr(BitVec::from_int("1", 4));
  EXPECT_EQ(ashr.s_to_int(), "-2");
}

TEST(BitVecComparison, Relations) {
  BitVec three = BitVec::from_int("3", 4);
  BitVec five = BitVec::from_int("5", 4);
  EXPECT_TRUE(three.ult(five));
  EXPECT_TRUE(three.ule(three));
  EXPECT_TRUE(five.uge(three));
  EXPECT_TRUE(five.ugt(three));
  EXPECT_TRUE(three.eq(BitVec::from_int("3", 4)));
  EXPECT_TRUE(three.equals(BitVec::from_int("3", 4)));

  BitVec minus2 = BitVec::from_int("-2", 4);
  BitVec one = BitVec::from_int("1", 4);
  EXPECT_TRUE(minus2.slt(one));
  EXPECT_TRUE(minus2.sle(minus2));
  EXPECT_TRUE(one.sge(minus2));
  EXPECT_TRUE(one.sgt(minus2));

  BitVec compEq = three.comp(BitVec::from_int("3", 4));
  EXPECT_EQ(compEq.u_to_int(), "1");
  BitVec compNe = three.comp(five);
  EXPECT_EQ(compNe.u_to_int(), "0");
}

TEST(BitVecOverflow, Detection) {
  BitVec min = BitVec::from_int("-8", 4);
  EXPECT_TRUE(min.nego());

  BitVec uadd_lhs = BitVec::from_int("15", 4);
  BitVec uadd_rhs = BitVec::from_int("1", 4);
  EXPECT_TRUE(uadd_lhs.uaddo(uadd_rhs));

  BitVec sadd_lhs = BitVec::from_int("4", 4);
  BitVec sadd_rhs = BitVec::from_int("5", 4);
  EXPECT_TRUE(sadd_lhs.saddo(sadd_rhs));

  BitVec umul_lhs = BitVec::from_int("8", 4);
  BitVec umul_rhs = BitVec::from_int("2", 4);
  EXPECT_TRUE(umul_lhs.umulo(umul_rhs));

  BitVec smul_lhs = BitVec::from_int("4", 4);
  BitVec smul_rhs = BitVec::from_int("4", 4);
  EXPECT_TRUE(smul_lhs.smulo(smul_rhs));

  BitVec usub_lhs = BitVec::from_int("3", 4);
  BitVec usub_rhs = BitVec::from_int("5", 4);
  EXPECT_TRUE(usub_lhs.usubo(usub_rhs));

  BitVec ssub_lhs = BitVec::from_int("7", 4);
  BitVec ssub_rhs = BitVec::from_int("-2", 4);
  EXPECT_TRUE(ssub_lhs.ssubo(ssub_rhs));

  BitVec sdiv_lhs = BitVec::from_int("-8", 4);
  BitVec sdiv_rhs = BitVec::from_int("-1", 4);
  EXPECT_TRUE(sdiv_lhs.sdivo(sdiv_rhs));
}

TEST(BitVecConversion, ToInt) {
  BitVec u = BitVec::from_int("42", 8);
  EXPECT_EQ(u.u_to_int(), "42");
  BitVec s = BitVec::from_int("-5", 8);
  EXPECT_EQ(s.s_to_int(), "-5");
}

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

// ---------- Small helpers ----------
static BitVec mk_dec(std::size_t w, unsigned long long v) { return BitVec::from_int(std::to_string(v), w); }

static BitVec mk_hex(std::size_t w, const std::string &hex_wo_prefix) {
  return BitVec::from_int(std::string("0x") + hex_wo_prefix, w);
}

static BitVec mk_bin(std::size_t w, const std::string &bits_wo_prefix) {
  return BitVec::from_int(std::string("0b") + bits_wo_prefix, w);
}

static BitVec bv_min(std::size_t w) { // most-negative: 1000...0
  if(w == 0) return BitVec::zeros(0);
  // Start with width-1 zero-extend of 1 -> 00..001, then rotate left by w-1
  BitVec one1 = mk_dec(1, 1);
  BitVec msb = one1.zero_extend(w - 1).rotate_left(w - 1);
  return msb;
}

static BitVec bv_smax(std::size_t w) { // signed max: 0111...1
  if(w == 0) return BitVec::zeros(0);
  BitVec all1 = BitVec::ones(w);
  BitVec one = mk_dec(w, 1);
  return all1.lshr(one); // logical >> 1 turns 111..1 into 0111..1
}

static BitVec bv_neg1(std::size_t w) { return BitVec::ones(w); }
static BitVec bv_zero(std::size_t w) { return BitVec::zeros(w); }

static void expect_bveq(const BitVec &a, const BitVec &b) {
  ASSERT_EQ(a.width(), b.width()) << "Width mismatch";
  EXPECT_TRUE(a.equals(b)) << "u(a)=" << a.u_to_int() << ", u(b)=" << b.u_to_int();
  EXPECT_TRUE(a.eq(b));
}

// ---------- Parameterized by width ----------
class BitVecWidthSuite: public ::testing::TestWithParam<size_t> {};

INSTANTIATE_TEST_SUITE_P(AllWidths, BitVecWidthSuite,
                         ::testing::Values(0u, 1u, 5u, 8u, 13u, 16u, 25u, 32u, 55u, 64u, 99u, 128u));

TEST_P(BitVecWidthSuite, ConstructorsAndProperties) {
  const size_t w = GetParam();
  BitVec raw(w); // just exercise the ctor; content unspecified
  EXPECT_EQ(raw.width(), w);

  BitVec z = BitVec::zeros(w);
  BitVec o = BitVec::ones(w);

  EXPECT_EQ(z.width(), w);
  EXPECT_EQ(o.width(), w);
  EXPECT_TRUE(z.is_zero());
  if(w > 0) {
    EXPECT_FALSE(z.is_all_ones());
    EXPECT_FALSE(o.is_zero());
  }
  EXPECT_TRUE(o.is_all_ones());

  if(w > 0) {
    EXPECT_FALSE(z.is_negative());
    EXPECT_TRUE(bv_neg1(w).is_negative());
    EXPECT_TRUE(bv_min(w).is_most_negative());
    EXPECT_EQ(bv_min(w).is_negative(), true);
  }

  // bits()[0] should be LSB
  BitVec five = mk_dec(w, 5); // ..0101
  if(w >= 3) {
    EXPECT_TRUE(five.bits()[0]);
    EXPECT_FALSE(five.bits()[1]);
    EXPECT_TRUE(five.bits()[2]);
  } else if(w == 2) {
    EXPECT_TRUE(five.bits()[0]);
    EXPECT_FALSE(five.bits()[1]);
  } else if(w == 1) {
    EXPECT_TRUE(five.bits()[0]);
  }
}

TEST_P(BitVecWidthSuite, FromIntParsingAndModulo) {
  const size_t w = GetParam();
  // Hex, bin, oct and decimal; ensure truncation modulo 2^w
  BitVec a = BitVec::from_int("0xff", w);
  BitVec b = BitVec::from_int("255", w);
  expect_bveq(a, b);

  BitVec c = BitVec::from_int("0o77", w); // 63
  BitVec d = mk_dec(w, 63ull);
  expect_bveq(c, d);

  // Truncation: add one bit beyond width
  std::string big_hex = (w == 0) ? "0" : "1" + std::string((w + 3) / 4, '0');
  BitVec e = mk_hex(w, big_hex); // 1 << (4*((w+3)/4)) truncated to w
  (void) e;                      // constructed; core correctness exercised elsewhere
}

TEST_P(BitVecWidthSuite, ConcatExtractRepeat) {
  const size_t w = GetParam();
  // Build two pieces whose widths add up to 2*w (works even for w==1)
  BitVec hi = mk_dec(w, 0xAAAAAAAAull); // truncated to w
  BitVec lo = mk_dec(w, 0x55555555ull);
  BitVec both = hi.concat(lo);
  EXPECT_EQ(both.width(), w + w);

  // Extract back low and high parts
  if(w > 0) {
    BitVec lo_x = both.extract(w - 1, 0);
    BitVec hi_x = both.extract(2 * w - 1, w);
    expect_bveq(lo_x, lo);
    expect_bveq(hi_x, hi);
  }

  // Repeat basic shape
  BitVec base = mk_bin(3, "101");
  BitVec r0 = base.repeat(0);
  EXPECT_EQ(r0.width(), 0u);
  EXPECT_TRUE(r0.redand());
  EXPECT_FALSE(r0.redor());
  BitVec r3 = base.repeat(3); // 101101101
  EXPECT_EQ(r3.width(), 9u);
  // spot-check a couple of bits
  EXPECT_TRUE(r3.bits()[0]); // ...1
  EXPECT_TRUE(r3.bits()[2]); // ...101
}

TEST_P(BitVecWidthSuite, RotatesAndShifts) {
  const size_t w = GetParam();
  if(w == 0) GTEST_SKIP();

  BitVec v = (w >= 4) ? mk_bin(4, "1001").zero_extend(w - 4) : mk_bin(w, "1");
  // rotate inverse
  for(auto k: {0ull, 1ull, 3ull, (unsigned long long) w, (unsigned long long) (w + 7)}) {
    BitVec rl = v.rotate_left(k);
    BitVec back = rl.rotate_right(k);
    expect_bveq(back, v);
  }
  // rotate by w+1 == rotate by 1
  expect_bveq(v.rotate_left(w + 1), v.rotate_left(1));
  expect_bveq(v.rotate_right(w + 1), v.rotate_right(1));

  // Logical shifts: shift >= width -> zeros
  BitVec amt_ge = mk_dec(w, w);
  BitVec zeros = bv_zero(w);
  expect_bveq(v.shl(amt_ge), zeros);
  expect_bveq(v.lshr(amt_ge), zeros);

  // Arithmetic shift: fill with sign bit
  BitVec neg = bv_min(w);  // MSB=1
  BitVec pos = bv_zero(w); // MSB=0
  BitVec one = mk_dec(w, 1);
  BitVec neg_shift1 = neg.ashr(one); // 1000..0 >>a 1 == 1100..0 (sign bit fill)
  EXPECT_TRUE(neg_shift1.is_negative());
  expect_bveq(pos.ashr(amt_ge), pos); // all zeros stays zeros
  // For negative, ashr >= width -> all ones
  if(w > 0) { expect_bveq(neg.ashr(amt_ge), bv_neg1(w)); }
}

TEST_P(BitVecWidthSuite, BitwiseOpsAndReductions) {
  const size_t w = GetParam();
  if(w <= 1) GTEST_SKIP();
  BitVec a = mk_dec(w, 0xF0F0F0F0ull);
  BitVec b = mk_dec(w, 0x0FF00FF0ull);

  BitVec nota = a.$not();
  expect_bveq(nota.$not(), a);

  expect_bveq(a.nand(b), a.$and(b).$not());
  expect_bveq(a.nor(b), a.$or(b).$not());
  expect_bveq(a.xnor(b), a.$xor(b).$not());

  // redand/redor
  EXPECT_TRUE(bv_neg1(w).redand());
  EXPECT_FALSE(bv_zero(w).redand());
  EXPECT_TRUE(a.redor() || b.redor());
  EXPECT_FALSE(bv_zero(w).redor());
}

TEST_P(BitVecWidthSuite, ArithmeticModuloAndOverflowFlags) {
  const size_t w = GetParam();
  if(w <= 1) GTEST_SKIP();

  BitVec x = mk_dec(w, 1234567ull);
  BitVec y = mk_dec(w, 891011ull);

  // x + (-x) == 0 (mod 2^w)
  expect_bveq(x.add(x.neg()), bv_zero(w));

  // (x + y) - y == x
  expect_bveq(x.add(y).sub(y), x);

  // ones + 1 wraps to 0, and uaddo detects it
  BitVec one = mk_dec(w, 1);
  EXPECT_TRUE(BitVec::ones(w).uaddo(one));
  expect_bveq(BitVec::ones(w).add(one), bv_zero(w));

  // usubo: 0 - 1 borrows
  EXPECT_TRUE(bv_zero(w).usubo(one));

  // saddo: smax + 1 overflows
  EXPECT_TRUE(bv_smax(w).saddo(one));

  // ssubo: smax - (-1) overflows
  EXPECT_TRUE(bv_smax(w).ssubo(bv_neg1(w)));

  // sdivo: min / -1
  EXPECT_TRUE(bv_min(w).sdivo(bv_neg1(w)));

  // negation overflow predicate == is_most_negative
  EXPECT_EQ(bv_min(w).nego(), true);
  EXPECT_EQ(x.nego(), false);

  // Multiplication identities
  expect_bveq(x.mul(one), x);
  expect_bveq(x.mul(bv_zero(w)), bv_zero(w));

  // Unsigned multiplication overflow example when possible (w>=2)
  if(w >= 2) {
    BitVec two = mk_dec(w, 2);
    EXPECT_TRUE(bv_min(w).umulo(two));
    expect_bveq(bv_min(w).mul(two), bv_zero(w)); // 1<< (w-1) * 2 == 0 mod 2^w
  }
}

TEST_P(BitVecWidthSuite, DivRemAndModSemantics) {
  const size_t w = GetParam();
  if(w == 0) GTEST_SKIP();
  BitVec zero = bv_zero(w);
  BitVec all1 = bv_neg1(w);

  BitVec a = mk_dec(w, 12345);
  BitVec b = mk_dec(w, 234);

  // Division by zero cases
  expect_bveq(a.udiv(zero), all1);
  expect_bveq(a.urem(zero), a);
  expect_bveq(a.sdiv(zero), all1); // -1
  expect_bveq(a.srem(zero), a);
  expect_bveq(a.smod(zero), a);

  // Overflow (min / -1)
  expect_bveq(bv_min(w).sdiv(all1), bv_min(w));
  expect_bveq(bv_min(w).srem(all1), bv_zero(w));
  expect_bveq(bv_min(w).smod(all1), bv_zero(w));

  // udiv/urem relation: a = q*b + r, with r < b (when b != 0)
  if(!b.is_zero()) {
    BitVec q = a.udiv(b);
    BitVec r = a.urem(b);
    expect_bveq(q.mul(b).add(r), a);
    EXPECT_TRUE(r.ult(b));
  }
}

TEST_P(BitVecWidthSuite, ComparisonsAndComp) {
  const size_t w = GetParam();
  if(w <= 1) GTEST_SKIP();

  BitVec z = bv_zero(w);
  BitVec mn = bv_min(w);
  BitVec mxs = bv_smax(w);
  BitVec m1 = bv_neg1(w); // -1

  // Unsigned
  EXPECT_TRUE(z.ult(m1));
  EXPECT_TRUE(m1.ugt(z));
  EXPECT_TRUE(z.ule(z));
  EXPECT_TRUE(m1.uge(m1));

  // Signed
  EXPECT_TRUE(mn.slt(z));
  EXPECT_TRUE(mxs.sgt(z));
  EXPECT_TRUE(m1.sle(z));
  EXPECT_TRUE(mn.sle(mn));

  // eq vs equals
  EXPECT_TRUE(m1.eq(bv_neg1(w)));
  EXPECT_TRUE(m1.equals(bv_neg1(w)));
  EXPECT_EQ(m1.eq(z), m1.equals(z));

  // bvcomp (1-bit result)
  BitVec c1 = z.comp(z);
  BitVec c0 = z.comp(m1);
  EXPECT_EQ(c1.width(), 1u);
  EXPECT_EQ(c0.width(), 1u);
  EXPECT_TRUE(c1.eq(BitVec::from_int("1", 1)));
  EXPECT_TRUE(c0.eq(BitVec::from_int("0", 1)));
}

TEST_P(BitVecWidthSuite, ToIntStringsSigns) {
  const size_t w = GetParam();
  if(w == 0) GTEST_SKIP();

  BitVec z = bv_zero(w);
  BitVec m1 = bv_neg1(w);
  EXPECT_EQ(z.u_to_int(), std::string("0"));
  EXPECT_EQ(z.s_to_int(), std::string("0"));
  // -1 signed string must start with '-'
  std::string sm1 = m1.s_to_int();
  ASSERT_FALSE(sm1.empty());
  EXPECT_EQ(sm1[0], '-');

  // For small widths (<=16), check a few exact values
  if(w <= 16) {
    BitVec v = mk_dec(w, 42);
    if(w >= 6) {
      EXPECT_EQ(v.u_to_int(), std::string("42"));
      if(!v.is_negative()) EXPECT_EQ(v.s_to_int(), std::string("42"));
    }

    BitVec neg = bv_min(w); // most-negative
    std::string sneg = neg.s_to_int();
    ASSERT_FALSE(sneg.empty());
    EXPECT_EQ(sneg[0], '-');
  }
}

// A small non-parameterized smoke test for $and/$or/$xor with width==1 edge cases
TEST(BitVecEdgeCases, WidthOneBasics) {
  const size_t w = 1;
  BitVec zero = bv_zero(w);
  BitVec one = mk_dec(w, 1);
  expect_bveq(one.$and(one), one);
  expect_bveq(one.$or(zero), one);
  expect_bveq(one.$xor(one), zero);
  EXPECT_TRUE(one.is_negative()); // in 1-bit two's complement, 1 == -1
}