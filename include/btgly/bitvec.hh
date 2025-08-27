//
// Created by Wael-Amine Boutglay on 26/08/2025.
//

#pragma once

#include <vector>
#include <string>
#include "btgly/codepoint.hh"
#include "btgly/radix.hh"

namespace btgly {

  //*-- BitVec

  /// \brief Fixed-width bit-vector with SMT-LIB–style semantics.
  class BitVec {
  public:
    explicit BitVec(std::size_t width);

    BitVec(bool value, std::size_t width);

    static BitVec zeros(std::size_t width);

    static BitVec ones(std::size_t width);

    /// \brief Construct a bit-vector of \p width from an integer string.
    ///
    /// Parses \p integer as an unsigned integer in base 10 by default, or in
    /// base 2/8/16 when prefixed with \c 0b / \c 0o / \c 0x respectively.
    /// The value is reduced modulo 2^width (i.e., truncated to \p width bits).
    ///
    /// \param integer The textual integer value (e.g., "42", "0xff", "0b1010").
    /// \param width   Number of bits (may be 0).
    static BitVec from_int(std::string s, std::size_t width);

    //*- properties

    const std::vector<bool> &bits() const { return _bits; }

    /// \brief Return the number of bits in this bit-vector.
    std::size_t width() const;

    bool is_all_ones() const;

    bool is_zero() const;

    bool is_negative() const;

    bool is_most_negative() const;

    //*- methods

    /// \brief Concatenate this bit-vector (high part) with \p rhs (low part).
    ///
    /// \param rhs Low-order bits to append.
    /// \returns A new bit-vector of combined width.
    BitVec concat(const BitVec &rhs) const;

    /// \brief Extract bits \c [i : j] (inclusive), with \c i >= j.
    ///
    /// Uses 0-based indexing where bit 0 is LSB. The result has width \c i-j+1
    /// with result[0] = original bit \c j.
    ///
    /// \param i High bit index (inclusive).
    /// \param j Low bit index  (inclusive).
    /// \returns A new bit-vector of width \c (i - j + 1).
    BitVec extract(std::size_t i, std::size_t j) const;

    /// \brief Repeat this bit-vector \p k times by concatenation.
    ///
    /// \param k Number of repetitions (k >= 0). If \p k == 0, the result has
    /// width 0.
    /// \returns A new bit-vector of width \c k * this->width().
    BitVec repeat(std::size_t k) const;

    /// \brief Sign-extend by \p k bits (two's-complement).
    ///
    /// High bits of the result are filled with the sign bit (original bit
    /// \c width()-1). Result width is \c width()+k.
    ///
    /// \param k Number of bits to add.
    BitVec sign_extend(std::size_t k) const;

    /// \brief Zero-extend by \p k bits.
    ///
    /// High bits of the result are filled with zeros. Result width is
    /// \c width()+k.
    ///
    /// \param k Number of bits to add.
    BitVec zero_extend(std::size_t k) const;

    /// \brief Rotate left by \p k (mod \c width()).
    ///
    /// \param k Rotation amount (any size; taken modulo \c width()).
    /// \returns A bitwise rotation; width unchanged.
    BitVec rotate_left(std::size_t k) const;

    /// \brief Rotate right by \p k (mod \c width()).
    ///
    /// \param k Rotation amount (any size; taken modulo \c width()).
    /// \returns A bitwise rotation; width unchanged.
    BitVec rotate_right(std::size_t k) const;

    /// \brief Bitwise NOT (~).
    ///
    /// \returns A bit-vector where each bit is inverted.
    BitVec $not() const;

    /// \brief Bitwise AND.
    ///
    /// \param rhs Right-hand operand (same width).
    /// \returns \c (*this) & rhs.
    BitVec $and(const BitVec &rhs) const;

    /// \brief Bitwise OR.
    ///
    /// \param rhs Right-hand operand (same width).
    /// \returns \c (*this) | rhs.
    BitVec $or(const BitVec &rhs) const;

    /// \brief Bitwise XOR.
    ///
    /// \param rhs Right-hand operand (same width).
    /// \returns \c (*this) ^ rhs.
    BitVec $xor(const BitVec &rhs) const;

    /// \brief Bitwise NAND: NOT(AND).
    ///
    /// \param rhs Right-hand operand (same width).
    /// \returns \c ~((*this) & rhs).
    BitVec nand(const BitVec &rhs) const;

    /// \brief Bitwise NOR: NOT(OR).
    ///
    /// \param rhs Right-hand operand (same width).
    /// \returns \c ~((*this) | rhs).
    BitVec nor(const BitVec &rhs) const;

    /// \brief Bitwise XNOR: NOT(XOR).
    ///
    /// \param rhs Right-hand operand (same width).
    /// \returns \c ~((*this) ^ rhs).
    BitVec xnor(const BitVec &rhs) const;

    /// \brief Reduction AND.
    ///
    /// \returns \c true iff all bits are 1 (width==0 returns \c true).
    bool redand() const;

    /// \brief Reduction OR.
    ///
    /// \returns \c true iff any bit is 1 (width==0 returns \c false).
    bool redor() const;

    /// \brief Two's-complement negation.
    ///
    /// Equivalent to \c (~x + 1) modulo 2^width. Overflow (negation overflow)
    /// occurs only for the most-negative value (1000...0).
    BitVec neg() const;

    /// \brief Unsigned/signed-agnostic modular addition.
    ///
    /// Result is \c (*this + rhs) mod 2^width.
    BitVec add(const BitVec &rhs) const;

    /// \brief Unsigned/signed-agnostic modular subtraction.
    ///
    /// Result is \c (*this - rhs) mod 2^width.
    BitVec sub(const BitVec &rhs) const;

    /// \brief Unsigned/signed-agnostic modular multiplication.
    ///
    /// Result is \c (*this * rhs) mod 2^width.
    BitVec mul(const BitVec &rhs) const;

    /// \brief Unsigned division (SMT-LIB \c bvudiv semantics), Div/0 -> all ones.
    ///
    /// \param rhs Divisor.
    /// \returns \c floor(u(*this) / u(rhs)), where \c u is the unsigned value.
    /// Division by zero yields a vector of all 1s.
    BitVec udiv(const BitVec &rhs) const;

    /// \brief Unsigned remainder (SMT-LIB \c bvurem semantics), Div/0 -> lhs.
    ///
    /// \param rhs Divisor.
    /// \returns \c u(*this) mod u(rhs). If \p rhs is zero, returns \c *this.
    BitVec urem(const BitVec &rhs) const;

    /// \brief Signed division (two's-complement; SMT-LIB \c bvsdiv semantics).
    /// Div/0 -> -1. Overflow (min / -1) -> min.
    ///
    /// \returns Truncating division toward zero on signed values. Division by
    /// zero yields all 1s (i.e., -1). The overflow case (most-negative / -1)
    /// returns most-negative.
    BitVec sdiv(const BitVec &rhs) const;

    /// \brief Signed remainder (SMT-LIB \c bvsrem semantics).
    /// Div/0 -> lhs. Overflow (min / -1) -> 0.
    ///
    /// \returns \c s(*this) - trunc(s(*this)/s(rhs)) * s(rhs), where \c s is the
    /// signed value. If \p rhs is zero, returns \c *this. In the overflow case
    /// (most-negative / -1), returns 0.
    BitVec srem(const BitVec &rhs) const;

    /// \brief Signed modulo (SMT-LIB \c bvsmod semantics).
    /// Div/0 -> lhs. Overflow (min / -1) -> 0.
    ///
    /// \returns A value with the sign of \p rhs and magnitude < |rhs|. If
    /// \p rhs is zero, returns \c *this. In the overflow case
    /// (most-negative / -1), returns 0.
    BitVec smod(const BitVec &rhs) const;

    /// \brief Logical left shift by an unsigned amount in \p rhs.
    ///
    /// Shift amount is interpreted as an unsigned integer from \p rhs. If the
    /// amount >= width, the result is all zeros.
    BitVec shl(const BitVec &rhs) const;

    /// \brief Logical right shift by an unsigned amount in \p rhs.
    ///
    /// Shift amount is interpreted as unsigned. If the amount >= width, the
    /// result is all zeros.
    BitVec lshr(const BitVec &rhs) const;

    /// \brief Arithmetic right shift by an unsigned amount in \p rhs.
    ///
    /// Vacated bits are filled with the sign bit. If the amount >= width, the
    /// result is all sign bits (all 0s for non-negative, all 1s for negative).
    BitVec ashr(const BitVec &rhs) const;

    /// \brief Unsigned comparison: \c *this < rhs.
    bool ult(const BitVec &rhs) const;

    /// \brief Unsigned comparison: \c *this \<= rhs.
    bool ule(const BitVec &rhs) const;

    /// \brief Unsigned comparison: \c *this \>= rhs.
    bool uge(const BitVec &rhs) const;

    /// \brief Unsigned comparison: \c *this > rhs.
    bool ugt(const BitVec &rhs) const;

    bool eq(const BitVec &rhs) const;

    bool equals(const BitVec &rhs) const;

    /// \brief Signed comparison: \c *this < rhs.
    bool slt(const BitVec &rhs) const;

    /// \brief Signed comparison: \c *this \<= rhs.
    bool sle(const BitVec &rhs) const;

    /// \brief Signed comparison: \c *this \>= rhs.
    bool sge(const BitVec &rhs) const;

    /// \brief Signed comparison: \c *this > rhs.
    bool sgt(const BitVec &rhs) const;

    /// \brief Bit-vector compare (SMT-LIB \c bvcomp).
    ///
    /// \returns A 1-bit vector equal to 1 iff \c *this == rhs, else 0.
    BitVec comp(const BitVec &rhs) const;

    /// \brief Negation overflow predicate.
    ///
    /// \returns \c true iff \c *this is the most-negative two's-complement value.
    bool nego() const;

    /// \brief Unsigned addition overflow.
    ///
    /// \returns \c true iff \c u(*this) + u(rhs) >= 2^width.
    bool uaddo(const BitVec &rhs) const;

    /// \brief Signed addition overflow.
    ///
    /// \returns \c true iff adding as signed two's-complement overflows.
    bool saddo(const BitVec &rhs) const;

    /// \brief Unsigned multiplication overflow.
    ///
    /// \returns \c true iff the full unsigned product does not fit in \c width
    /// bits (i.e., any high bits beyond width are non-zero).
    bool umulo(const BitVec &rhs) const;

    /// \brief Signed multiplication overflow.
    ///
    /// \returns \c true iff the exact two's-complement product cannot be
    /// represented in \c width bits.
    bool smulo(const BitVec &rhs) const;

    /// \brief Unsigned subtraction overflow (borrow).
    ///
    /// \returns \c true iff \c u(*this) < u(rhs) (i.e., a borrow occurs).
    bool usubo(const BitVec &rhs) const;

    /// \brief Signed subtraction overflow.
    ///
    /// \returns \c true iff subtracting as signed two's-complement overflows.
    bool ssubo(const BitVec &rhs) const;

    /// \brief Signed division overflow.
    ///
    /// \returns \c true iff \c *this is most-negative and \p rhs is -1 (the only
    /// overflowing signed divide in two's-complement).
    bool sdivo(const BitVec &rhs) const;

    /// \brief Return the unsigned decimal string representation.
    ///
    /// \returns The value interpreted as an unsigned integer, in base 10.
    std::string u_to_int() const;

    /// \brief Return the signed decimal string representation.
    ///
    /// \returns The value interpreted as a signed two's-complement integer,
    /// in base 10.
    std::string s_to_int() const;

  private:
    /// \brief Bit storage (LSB-first; index 0 is the least significant bit).
    std::vector<bool> _bits;

    static bool _is_decimal_zero(const std::string &s);

    static int _div_decimal_by_2(std::string &s);

    static void _trim_leading_zeros(std::string &s);

    // Add a*b into 'acc' (acc has size >= a.size()+b.size())
    static void _mul(std::vector<bool> &acc, const std::vector<bool> &a, const std::vector<bool> &b);

    // TODO: static + rename to ucomp
    static int _compare_unsigned(const BitVec &a, const BitVec &b);

    // Unsigned division: compute quotient q (size w) and remainder r (dynamic).
    static void _udivrem_bits(const std::vector<bool> &num, const std::vector<bool> &den, std::vector<bool> &q,
                              std::vector<bool> &r);

    // Compare arbitrary-length LSB-first vectors (unsigned).
    static int _cmp_arb_unsigned(const std::vector<bool> &a, const std::vector<bool> &b);

    // a -= b, assumes a >= b (unsigned), arbitrary-length LSB-first.
    static void _sub_arb_unsigned_in_place(std::vector<bool> &a, const std::vector<bool> &b);

    static void _trim_bits(std::vector<bool> &v);

    static int _msb_index(const std::vector<bool> &v);

    static void _dec_mul_add(std::string &s, int mul, int add);

    static std::size_t _rhs_amount_mod(const BitVec &amt, std::size_t mod);

    static bool _rhs_amount_ge_width(const BitVec &amt, std::size_t w);

    /*void ensureSameWidth(const BitVec &rhs, const char *op) const {
        if (width() != rhs.width())
          throw std::invalid_argument(std::string(op) + ": width mismatch");
    }*/
  };

} // namespace btgly