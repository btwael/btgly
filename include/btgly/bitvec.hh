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
    explicit BitVec(std::size_t width) : _bits(width) {}

    BitVec(bool value, std::size_t width) : _bits(width, value) {}

    static BitVec zeros(std::size_t width) { return BitVec(0, width); }

    static BitVec ones(std::size_t width) { return BitVec(1, width); }

    static BitVec from_int(std::string s, std::size_t width) {
      // TODO: specify
      // TODO: deal with empty or illegal string
      BitVec result(width);

      // determine negativeness
      bool neg = false;
      if(s[0] == '+' || s[0] == '-') {
        neg = (s[0] == '-');
        s.erase(s.begin());
      }

      // determine base
      Radix base = Radix::Decimal;
      if(s.size() >= 2 && s[0] == CodePoint::$0 &&
         (s[1] == CodePoint::$b || s[1] == CodePoint::$B || s[1] == CodePoint::$x || s[1] == CodePoint::$X ||
          s[1] == CodePoint::$o || s[1] == CodePoint::$O)) {
        char p = s[1];
        if(p == CodePoint::$b || p == CodePoint::$B) {
          base = Radix::Binary;
        } else if(p == CodePoint::$o || p == CodePoint::$O) {
          base = Radix::Octal;
        } else {
          base = Radix::Hexadecimal;
        }
        s.erase(0, 2);
      }

      if(base == Radix::Binary) { // parse binary integer
        std::size_t pos = 0;
        for(std::size_t k = 0; k < s.size(); ++k) {
          char c = s[s.size() - 1 - k];
          if(c != CodePoint::$0 && c != CodePoint::$1) { throw std::invalid_argument("invalid binary digit"); }
          if(pos < width) { result._bits[pos] = (c == CodePoint::$1); }
          ++pos;
        }
      } else if(base == Radix::Octal) { // parse octal integer
        std::size_t pos = 0;
        for(std::size_t k = 0; k < s.size(); ++k) {
          char c = s[s.size() - 1 - k];
          if(c < CodePoint::$0 || c > CodePoint::$7) { throw std::invalid_argument("invalid octal digit"); }
          int v = c - CodePoint::$0;
          for(int b = 0; b < 3; ++b) {
            if(pos < width) { result._bits[pos] = (v >> b) & 1; }
            ++pos;
          }
        }
      } else if(base == Radix::Hexadecimal) { // parse hex integer
        std::size_t pos = 0;
        for(std::size_t k = 0; k < s.size(); ++k) {
          int v = CodePoint::hex_to_int(s[s.size() - 1 - k]);
          if(v < 0) { throw std::invalid_argument("invalid hexadecimal digit"); }
          for(int b = 0; b < 4; ++b) {
            if(pos < width) { result._bits[pos] = (v >> b) & 1; }
            ++pos;
          }
        }
      } else { // parse decimal integer
        std::string dec = s;
        std::size_t pos = 0;
        while(!_is_decimal_zero(dec) && pos < width) {
          int rem = _div_decimal_by_2(dec);
          result._bits[pos++] = (rem != 0);
        }
      }

      // negate if negative
      if(neg) { result = result.neg(); }

      return result;
    }

    /// \brief Construct a bit-vector of \p width from an integer string.
    ///
    /// Parses \p integer as an unsigned integer in base 10 by default, or in
    /// base 2/8/16 when prefixed with \c 0b / \c 0o / \c 0x respectively.
    /// The value is reduced modulo 2^width (i.e., truncated to \p width bits).
    ///
    /// \param integer The textual integer value (e.g., "42", "0xff", "0b1010").
    /// \param width   Number of bits. Must be > 0.
    BitVec(std::string integer, std::size_t width);

    //*- properties

    /// \brief Return the number of bits in this bit-vector.
    std::size_t width() const { return _bits.size(); }

    bool is_all_ones() const { return redand(); }

    bool is_zero() const { return !redor(); }

    //*- methods

    /// \brief Concatenate this bit-vector (high part) with \p rhs (low part).
    ///
    /// \param rhs Low-order bits to append.
    /// \returns A new bit-vector of combined width.
    BitVec concat(const BitVec &rhs) const {
      //$ ensures return.width() == this.width() + rhs.width()
      //$ ensures forall k: Int :: 0 <= k < rhs.width() => return[k] == rhs[k]
      //$ ensures forall k: Int :: 0 <= k < this.width() => return[rhs.width() + k] == this[k]
      BitVec result(this->width() + rhs.width());
      // Low part from rhs
      for(std::size_t i = 0; i < rhs.width(); ++i) { result._bits[i] = rhs._bits[i]; }
      // High part from this
      for(std::size_t i = 0; i < this->width(); ++i) { result._bits[i + rhs.width()] = _bits[i]; }
      return result;
    }

    /// \brief Extract bits \c [i : j] (inclusive), with \c i >= j.
    ///
    /// Uses 0-based indexing where bit 0 is LSB. The result has width \c i-j+1
    /// with result[0] = original bit \c j.
    ///
    /// \param i High bit index (inclusive).
    /// \param j Low bit index  (inclusive).
    /// \returns A new bit-vector of width \c (i - j + 1).
    BitVec extract(std::size_t i, std::size_t j) const {
      // TODO: specify
      if(i < j) { throw std::invalid_argument("extract: i < j"); }
      if(i >= this->width()) { throw std::out_of_range("extract: high index out of range"); }
      const std::size_t w = i - j + 1;
      BitVec result(w);
      for(std::size_t k = 0; k < w; ++k) {
        const std::size_t src = j + k;
        result._bits[k] = _bits[src];
      }
      return result;
    }

    /// \brief Repeat this bit-vector \p k times by concatenation.
    ///
    /// \param k Number of repetitions (k >= 0). If \p k == 0, the result has
    /// width 0.
    /// \returns A new bit-vector of width \c k * this->width().
    BitVec repeat(std::size_t k) const {
      // TODO: specify
      if(k == 0) { return BitVec::zeros(0); }
      BitVec result(width() * k);
      for(std::size_t r = 0; r < k; ++r) {
        for(std::size_t i = 0; i < this->width(); ++i) { result._bits[r * this->width() + i] = _bits[i]; }
      }
      return result;
    }

    /// \brief Sign-extend by \p k bits (two's-complement).
    ///
    /// High bits of the result are filled with the sign bit (original bit
    /// \c width()-1). Result width is \c width()+k.
    ///
    /// \param k Number of bits to add.
    BitVec sign_extend(std::size_t k) const {
      // TODO: specify
      BitVec result(0, this->width() + k);
      const bool sign = _bits[width() - 1];
      for(std::size_t i = 0; i < this->width(); ++i) { result._bits[i] = _bits[i]; }
      for(std::size_t i = this->width(); i < result.width(); ++i) { result._bits[i] = sign; }
      return result;
    }

    /// \brief Zero-extend by \p k bits.
    ///
    /// High bits of the result are filled with zeros. Result width is
    /// \c width()+k.
    ///
    /// \param k Number of bits to add.
    BitVec zero_extend(std::size_t k) const {
      // TODO: specify
      BitVec out(0, width() + k);
      for(std::size_t i = 0; i < width(); ++i) { out._bits[i] = _bits[i]; }
      return out;
    }

    /// \brief Rotate left by \p k (mod \c width()).
    ///
    /// \param k Rotation amount (any size; taken modulo \c width()).
    /// \returns A bitwise rotation; width unchanged.
    BitVec rotate_left(std::size_t k) const; // TODO: implement

    /// \brief Rotate right by \p k (mod \c width()).
    ///
    /// \param k Rotation amount (any size; taken modulo \c width()).
    /// \returns A bitwise rotation; width unchanged.
    BitVec rotate_right(std::size_t k) const; // TODO: implement

    /// \brief Bitwise NOT (~).
    ///
    /// \returns A bit-vector where each bit is inverted.
    BitVec $not() const {
      //$ ensures return.width() == this.width()
      //$ ensures forall k: Int :: 0 <= k < rhs.width() => return[k] == !this[k]
      BitVec result(this->width());
      for(std::size_t i = 0; i < width(); ++i) { result._bits[i] = !_bits[i]; }
      return result;
    }

    /// \brief Bitwise AND.
    ///
    /// \param rhs Right-hand operand (same width).
    /// \returns \c (*this) & rhs.
    BitVec $and(const BitVec &rhs) const {
      //$ requires rhs.width() == this.width()
      //$ ensures return.width() == this.width()
      //$ ensures forall k: Int :: 0 <= k < rhs.width() => return[k] == (this[k] && rhs[k])
      // TODO: ensureSameWidth(rhs, "$and");
      BitVec result(width());
      for(std::size_t i = 0; i < width(); ++i) { result._bits[i] = _bits[i] & rhs._bits[i]; }
      return result;
    }

    /// \brief Bitwise OR.
    ///
    /// \param rhs Right-hand operand (same width).
    /// \returns \c (*this) | rhs.
    BitVec $or(const BitVec &rhs) const {
      //$ requires rhs.width() == this.width()
      //$ ensures return.width() == this.width()
      //$ ensures forall k: Int :: 0 <= k < rhs.width() => return[k] == (this[k] || rhs[k])
      // TODO: ensureSameWidth(rhs, "or");
      BitVec result(width());
      for(std::size_t i = 0; i < width(); ++i) { result._bits[i] = _bits[i] | rhs._bits[i]; }
      return result;
    }

    /// \brief Bitwise XOR.
    ///
    /// \param rhs Right-hand operand (same width).
    /// \returns \c (*this) ^ rhs.
    BitVec $xor(const BitVec &rhs) const {
      //$ requires rhs.width() == this.width()
      //$ ensures return.width() == this.width()
      //$ ensures forall k: Int :: 0 <= k < rhs.width() => return[k] == (this[k] ^ rhs[k])
      // TODO: ensureSameWidth(rhs, "$xor");
      BitVec result(width());
      for(std::size_t i = 0; i < width(); ++i) { result._bits[i] = _bits[i] ^ rhs._bits[i]; }
      return result;
    }

    /// \brief Bitwise NAND: NOT(AND).
    ///
    /// \param rhs Right-hand operand (same width).
    /// \returns \c ~((*this) & rhs).
    BitVec nand(const BitVec &rhs) const {
      // TODO: specify
      return $and(rhs).$not();
    }

    /// \brief Bitwise NOR: NOT(OR).
    ///
    /// \param rhs Right-hand operand (same width).
    /// \returns \c ~((*this) | rhs).
    BitVec nor(const BitVec &rhs) const {
      // TODO: specify
      return $or(rhs).$not();
    }

    /// \brief Bitwise XNOR: NOT(XOR).
    ///
    /// \param rhs Right-hand operand (same width).
    /// \returns \c ~((*this) ^ rhs).
    BitVec xnor(const BitVec &rhs) const {
      // TODO: specify
      return $xor(rhs).$not();
    }

    /// \brief Reduction AND.
    ///
    /// \returns \c true iff all bits are 1 (width==0 returns \c true).
    bool redand() const {
      // TODO: specify
      for(bool b: _bits) {
        if(!b) { return false; }
      }
      return true;
    }

    /// \brief Reduction OR.
    ///
    /// \returns \c true iff any bit is 1 (width==0 returns \c false).
    bool redor() const {
      // TODO: specify
      for(bool b: _bits) {
        if(b) { return true; };
      }
      return false;
    }

    /// \brief Two's-complement negation.
    ///
    /// Equivalent to \c (~x + 1) modulo 2^width. Overflow (negation overflow)
    /// occurs only for the most-negative value (1000...0).
    BitVec neg() const {
      //$ ensures return.width() == this.width()
      // TODO: specify
      // Return 0 - this (mod 2^w)
      return BitVec::zeros(this->width()).sub(*this);
    }

    /// \brief Unsigned/signed-agnostic modular addition.
    ///
    /// Result is \c (*this + rhs) mod 2^width.
    BitVec add(const BitVec &rhs) const {
      //$ requires rhs.width() == this.width()
      //$ ensures return.width() == this.width()
      // TODO: specify
      // TODO: ensureSameWidth(rhs, "add");
      BitVec result(this->width());
      bool carry = false;
      for(std::size_t i = 0; i < width(); ++i) {
        const bool a = _bits[i], b = rhs._bits[i];
        result._bits[i] = (a ^ b) ^ carry;
        carry = (a & b) | (a & carry) | (b & carry);
      }
      return result;
    }

    /// \brief Unsigned/signed-agnostic modular subtraction.
    ///
    /// Result is \c (*this - rhs) mod 2^width.
    BitVec sub(const BitVec &rhs) const {
      //$ requires rhs.width() == this.width()
      //$ ensures return.width() == this.width()
      // TODO: specify
      // TODO: ensureSameWidth(rhs, "sub");
      BitVec result(width());
      bool borrow = false;
      for(std::size_t i = 0; i < width(); ++i) {
        const bool a = _bits[i], b = rhs._bits[i];
        result._bits[i] = (a ^ b) ^ borrow;
        borrow = (!a & b) | ((!(a) | b) & borrow);
      }
      return result;
    }

    /// \brief Unsigned/signed-agnostic modular multiplication.
    ///
    /// Result is \c (*this * rhs) mod 2^width.
    BitVec mul(const BitVec &rhs) const {
      // TODO: specify
      // TODO:ensureSameWidth(rhs, "mul");
      const std::size_t w = this->width();
      // Compute full 2w-bit product, return low w bits.
      std::vector<bool> full(2 * w, false);
      _mul(full, _bits, rhs._bits);
      BitVec out(w);
      for(std::size_t i = 0; i < w; ++i) { out._bits[i] = full[i]; }
      return out;
    }

    /// \brief Unsigned division (SMT-LIB \c bvudiv semantics).
    ///
    /// \param rhs Divisor.
    /// \returns \c floor(u(*this) / u(rhs)), where \c u is the unsigned value.
    /// Division by zero yields a vector of all 1s.
    BitVec udiv(const BitVec &rhs) const; // TODO: implement

    /// \brief Unsigned remainder (SMT-LIB \c bvurem semantics).
    ///
    /// \param rhs Divisor.
    /// \returns \c u(*this) mod u(rhs). If \p rhs is zero, returns \c *this.
    BitVec urem(const BitVec &rhs) const; // TODO: implement

    /// \brief Signed division (two's-complement; SMT-LIB \c bvsdiv semantics).
    ///
    /// \returns Truncating division toward zero on signed values. Division by
    /// zero yields all 1s (i.e., -1). The overflow case (most-negative / -1)
    /// returns most-negative.
    BitVec sdiv(const BitVec &rhs) const; // TODO: implement

    /// \brief Signed remainder (SMT-LIB \c bvsrem semantics).
    ///
    /// \returns \c s(*this) - trunc(s(*this)/s(rhs)) * s(rhs), where \c s is the
    /// signed value. If \p rhs is zero, returns \c *this. In the overflow case
    /// (most-negative / -1), returns 0.
    BitVec srem(const BitVec &rhs) const; // TODO: implement

    /// \brief Signed modulo (SMT-LIB \c bvsmod semantics).
    ///
    /// \returns A value with the sign of \p rhs and magnitude < |rhs|. If
    /// \p rhs is zero, returns \c *this. In the overflow case
    /// (most-negative / -1), returns 0.
    BitVec smod(const BitVec &rhs) const; // TODO: implement

    /// \brief Logical left shift by an unsigned amount in \p rhs.
    ///
    /// Shift amount is interpreted as an unsigned integer from \p rhs. If the
    /// amount >= width, the result is all zeros.
    BitVec shl(const BitVec &rhs) const; // TODO: implement

    /// \brief Logical right shift by an unsigned amount in \p rhs.
    ///
    /// Shift amount is interpreted as unsigned. If the amount >= width, the
    /// result is all zeros.
    BitVec lshr(const BitVec &rhs) const; // TODO: implement

    /// \brief Arithmetic right shift by an unsigned amount in \p rhs.
    ///
    /// Vacated bits are filled with the sign bit. If the amount >= width, the
    /// result is all sign bits (all 0s for non-negative, all 1s for negative).
    BitVec ashr(const BitVec &rhs) const; // TODO: implement

    /// \brief Unsigned comparison: \c *this < rhs.
    bool ult(const BitVec &rhs) const {
      // TODO: specify
      return _compare_unsigned(*this, rhs) < 0;
    }

    /// \brief Unsigned comparison: \c *this \<= rhs.
    bool ule(const BitVec &rhs) const {
      // TODO: specify
      return _compare_unsigned(*this, rhs) <= 0;
    }

    /// \brief Unsigned comparison: \c *this \>= rhs.
    bool uge(const BitVec &rhs) const {
      // TODO: specify
      return _compare_unsigned(*this, rhs) >= 0;
    }

    /// \brief Unsigned comparison: \c *this > rhs.
    bool ugt(const BitVec &rhs) const {
      // TODO: specify
      return _compare_unsigned(*this, rhs) > 0;
    }

    bool eq(const BitVec &rhs) const {
      // TODO: specify
      return this->equals(rhs);
    }

    bool equals(const BitVec &rhs) const {
      // TODO: specify
      return _compare_unsigned(*this, rhs) == 0;
    }

    /// \brief Signed comparison: \c *this < rhs.
    bool slt(const BitVec &rhs) const; // TODO: implement

    /// \brief Signed comparison: \c *this \<= rhs.
    bool sle(const BitVec &rhs) const; // TODO: implement

    /// \brief Signed comparison: \c *this \>= rhs.
    bool sge(const BitVec &rhs) const; // TODO: implement

    /// \brief Signed comparison: \c *this > rhs.
    bool sgt(const BitVec &rhs) const; // TODO: implement

    /// \brief Bit-vector compare (SMT-LIB \c bvcomp).
    ///
    /// \returns A 1-bit vector equal to 1 iff \c *this == rhs, else 0.
    BitVec comp(const BitVec &rhs) const; // TODO: implement

    /// \brief Negation overflow predicate.
    ///
    /// \returns \c true iff \c *this is the most-negative two's-complement value.
    bool nego() const; // TODO: implement

    /// \brief Unsigned addition overflow.
    ///
    /// \returns \c true iff \c u(*this) + u(rhs) >= 2^width.
    bool uaddo(const BitVec &rhs) const {
      // TODO:ensureSameWidth(rhs, "uaddo");
      // TODO: make common code with uaddo
      bool carry = false;
      for(std::size_t i = 0; i < width(); ++i) {
        const bool a = _bits[i], b = rhs._bits[i];
        carry = (a & b) | (a & carry) | (b & carry);
      }
      return carry;
    }

    /// \brief Signed addition overflow.
    ///
    /// \returns \c true iff adding as signed two's-complement overflows.
    bool saddo(const BitVec &rhs) const; // TODO: implement

    /// \brief Unsigned multiplication overflow.
    ///
    /// \returns \c true iff the full unsigned product does not fit in \c width
    /// bits (i.e., any high bits beyond width are non-zero).
    bool umulo(const BitVec &rhs) const {
      // TODO: specify
      // TODO: ensureSameWidth(rhs, "umulo");
      // TODO: make common code with umulo
      const std::size_t w = this->width();
      std::vector<bool> full(2 * w, false);
      _mul(full, _bits, rhs._bits);
      // Check high w bits for any 1.
      for(std::size_t i = w; i < 2 * w; ++i) {
        if(full[i]) { return true; }
      }
      return false;
    }

    /// \brief Signed multiplication overflow.
    ///
    /// \returns \c true iff the exact two's-complement product cannot be
    /// represented in \c width bits.
    bool smulo(const BitVec &rhs) const; // TODO: implement

    /// \brief Unsigned subtraction overflow (borrow).
    ///
    /// \returns \c true iff \c u(*this) < u(rhs) (i.e., a borrow occurs).
    bool usubo(const BitVec &rhs) const {
      // TODO: specify
      return ult(rhs);
    }

    /// \brief Signed subtraction overflow.
    ///
    /// \returns \c true iff subtracting as signed two's-complement overflows.
    bool ssubo(const BitVec &rhs) const; // TODO: implement

    /// \brief Signed division overflow.
    ///
    /// \returns \c true iff \c *this is most-negative and \p rhs is -1 (the only
    /// overflowing signed divide in two's-complement).
    bool sdivo(const BitVec &rhs) const; // TODO: implement

    /// \brief Return the unsigned decimal string representation.
    ///
    /// \returns The value interpreted as an unsigned integer, in base 10.
    std::string u_to_int() const; // TODO: implement

    /// \brief Return the signed decimal string representation.
    ///
    /// \returns The value interpreted as a signed two's-complement integer,
    /// in base 10.
    std::string s_to_int() const; // TODO: implement

  private:
    /// \brief Bit storage (LSB-first; index 0 is the least significant bit).
    std::vector<bool> _bits;

    static bool _is_decimal_zero(const std::string &s) {
      for(char c: s) {
        if(c != '0') { return false; }
      }
      return true;
    }

    static int _div_decimal_by_2(std::string &s) {
      int carry = 0;
      std::string out;
      out.reserve(s.size());
      for(char ch: s) {
        if(!std::isdigit(static_cast<unsigned char>(ch))) { throw std::invalid_argument("invalid decimal digit"); }
        int d = (ch - CodePoint::$0) + 10 * carry;
        int q = d / 2;
        carry = d % 2;
        out.push_back(static_cast<char>(CodePoint::$0 + q));
      }
      _trim_leading_zeros(out);
      if(out.empty()) { out = "0"; }
      s.swap(out);
      return carry;
    }

    static void _trim_leading_zeros(std::string &s) {
      std::size_t i = 0;
      while(i + 1 < s.size() && s[i] == CodePoint::$0) { ++i; }
      if(i) { s.erase(0, i); }
    }

    // Add a*b into 'acc' (acc has size >= a.size()+b.size())
    static void _mul(std::vector<bool> &acc, const std::vector<bool> &a, const std::vector<bool> &b) {
      const std::size_t na = a.size(), nb = b.size();
      for(std::size_t j = 0; j < nb; ++j) {
        if(!b[j]) { continue; }
        bool carry = false;
        for(std::size_t i = 0; i < na; ++i) {
          const std::size_t k = i + j;
          bool sum = acc[k] ^ a[i] ^ carry;
          carry = (acc[k] & a[i]) | (acc[k] & carry) | (a[i] & carry);
          acc[k] = sum;
        }
        // propagate carry
        std::size_t k = na + j;
        while(carry) {
          bool sum = acc[k] ^ carry;
          carry = acc[k] & carry;
          acc[k] = sum;
          ++k;
          if(k >= acc.size()) {
            break; // should not happen if acc large enough}
          }
        }
      }
    }

    // TODO: static + rename to ucomp
    static int _compare_unsigned(const BitVec &a, const BitVec &b) {
      // TODO: specify
      // TODO: a.ensureSameWidth(b, "compare");
      const std::size_t w = a.width();
      for(std::size_t i = 0; i < w; ++i) {
        // scan from MSB to LSB
        std::size_t idx = w - 1 - i;
        const bool abit = a._bits[idx], bbit = b._bits[idx];
        if(abit != bbit) { return abit ? 1 : -1; }
      }
      return 0;
    }
  };

} // namespace btgly