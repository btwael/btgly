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
