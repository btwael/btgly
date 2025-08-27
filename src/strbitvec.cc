//
// Created by Wael-Amine Boutglay on 26/08/2025.
//

#include "btgly/strbitvec.hh"
#include <stdexcept>

namespace btgly {

  //*-- StrBitVec

  StrBitVec::StrBitVec(std::size_t width) : _bits(width) {}

  StrBitVec::StrBitVec(bool value, std::size_t width) : _bits(width, value) {}

  StrBitVec StrBitVec::zeros(std::size_t width) { return StrBitVec(0, width); }

  StrBitVec StrBitVec::ones(std::size_t width) { return StrBitVec(1, width); }

  StrBitVec StrBitVec::from_int(std::string s, std::size_t width) {
    // TODO: specify
    // TODO: deal with empty or illegal string
    StrBitVec result(width);

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

  //*- properties

  std::size_t StrBitVec::width() const { return _bits.size(); }

  bool StrBitVec::is_all_ones() const { return redand(); }

  bool StrBitVec::is_zero() const { return !redor(); }

  bool StrBitVec::is_negative() const {
    return width() == 0 ? false : _bits[width() - 1];
  }

  bool StrBitVec::is_most_negative() const {
    const std::size_t w = width();
    if(w == 0) { return false; }
    if(!_bits[w - 1]) {
      return false; // sign bit must be 1
    }
    for(std::size_t i = 0; i + 1 < w; ++i) {
      if(_bits[i]) return false; // all others must be 0
    }
    return true;
  }

  //*- methods

  StrBitVec StrBitVec::concat(const StrBitVec &rhs) const {
    //$ ensures return.width() == this.width() + rhs.width()
    //$ ensures forall k: Int :: 0 <= k < rhs.width() => return[k] == rhs[k]
    //$ ensures forall k: Int :: 0 <= k < this.width() => return[rhs.width() + k] == this[k]
    StrBitVec result(this->width() + rhs.width());
    // Low part from rhs
    for(std::size_t i = 0; i < rhs.width(); ++i) { result._bits[i] = rhs._bits[i]; }
    // High part from this
    for(std::size_t i = 0; i < this->width(); ++i) { result._bits[i + rhs.width()] = _bits[i]; }
    return result;
  }

  StrBitVec StrBitVec::extract(std::size_t i, std::size_t j) const {
    // TODO: specify
    if(i < j) { throw std::invalid_argument("extract: i < j"); }
    if(i >= this->width()) { throw std::out_of_range("extract: high index out of range"); }
    const std::size_t w = i - j + 1;
    StrBitVec result(w);
    for(std::size_t k = 0; k < w; ++k) {
      const std::size_t src = j + k;
      result._bits[k] = _bits[src];
    }
    return result;
  }

  StrBitVec StrBitVec::repeat(std::size_t k) const {
    // TODO: specify
    if(k == 0) { return StrBitVec::zeros(0); }
    StrBitVec result(width() * k);
    for(std::size_t r = 0; r < k; ++r) {
      for(std::size_t i = 0; i < this->width(); ++i) { result._bits[r * this->width() + i] = _bits[i]; }
    }
    return result;
  }

  StrBitVec StrBitVec::sign_extend(std::size_t k) const {
    // TODO: specify
    StrBitVec result(0, this->width() + k);
    const bool sign = width() == 0 ? false : _bits[width() - 1];
    for(std::size_t i = 0; i < this->width(); ++i) { result._bits[i] = _bits[i]; }
    for(std::size_t i = this->width(); i < result.width(); ++i) { result._bits[i] = sign; }
    return result;
  }

  StrBitVec StrBitVec::zero_extend(std::size_t k) const {
    // TODO: specify
    StrBitVec out(0, width() + k);
    for(std::size_t i = 0; i < width(); ++i) { out._bits[i] = _bits[i]; }
    return out;
  }

  StrBitVec StrBitVec::rotate_left(std::size_t k) const {
    // TODO: specify
    const std::size_t w = width();
    if(w == 0) return StrBitVec(0);
    k %= w;
    StrBitVec out(w);
    for(std::size_t i = 0; i < w; ++i) {
      // new[i] = old[(i - k) mod w]
      const std::size_t src = (i + w - (k % w)) % w;
      out._bits[i] = _bits[src];
    }
    return out;
  }

  StrBitVec StrBitVec::rotate_right(std::size_t k) const {
    // TODO: specify
    const std::size_t w = width();
    if(w == 0) return StrBitVec(0);
    k %= w;
    StrBitVec out(w);
    for(std::size_t i = 0; i < w; ++i) {
      // new[i] = old[(i + k) mod w]
      const std::size_t src = (i + (k % w)) % w;
      out._bits[i] = _bits[src];
    }
    return out;
  }

  StrBitVec StrBitVec::$not() const {
    //$ ensures return.width() == this.width()
    //$ ensures forall k: Int :: 0 <= k < rhs.width() => return[k] == !this[k]
    StrBitVec result(this->width());
    for(std::size_t i = 0; i < width(); ++i) { result._bits[i] = !_bits[i]; }
    return result;
  }

  StrBitVec StrBitVec::$and(const StrBitVec &rhs) const {
    //$ requires rhs.width() == this.width()
    //$ ensures return.width() == this.width()
    //$ ensures forall k: Int :: 0 <= k < rhs.width() => return[k] == (this[k] && rhs[k])
    // TODO: ensureSameWidth(rhs, "$and");
    StrBitVec result(width());
    for(std::size_t i = 0; i < width(); ++i) { result._bits[i] = _bits[i] & rhs._bits[i]; }
    return result;
  }

  StrBitVec StrBitVec::$or(const StrBitVec &rhs) const {
    //$ requires rhs.width() == this.width()
    //$ ensures return.width() == this.width()
    //$ ensures forall k: Int :: 0 <= k < rhs.width() => return[k] == (this[k] || rhs[k])
    // TODO: ensureSameWidth(rhs, "or");
    StrBitVec result(width());
    for(std::size_t i = 0; i < width(); ++i) { result._bits[i] = _bits[i] | rhs._bits[i]; }
    return result;
  }

  StrBitVec StrBitVec::$xor(const StrBitVec &rhs) const {
    //$ requires rhs.width() == this.width()
    //$ ensures return.width() == this.width()
    //$ ensures forall k: Int :: 0 <= k < rhs.width() => return[k] == (this[k] ^ rhs[k])
    // TODO: ensureSameWidth(rhs, "$xor");
    StrBitVec result(width());
    for(std::size_t i = 0; i < width(); ++i) { result._bits[i] = _bits[i] ^ rhs._bits[i]; }
    return result;
  }

  StrBitVec StrBitVec::nand(const StrBitVec &rhs) const {
    // TODO: specify
    return $and(rhs).$not();
  }

  StrBitVec StrBitVec::nor(const StrBitVec &rhs) const {
    // TODO: specify
    return $or(rhs).$not();
  }

  StrBitVec StrBitVec::xnor(const StrBitVec &rhs) const {
    // TODO: specify
    return $xor(rhs).$not();
  }

  bool StrBitVec::redand() const {
    // TODO: specify
    for(bool b: _bits) {
      if(!b) { return false; }
    }
    return true;
  }

  bool StrBitVec::redor() const {
    // TODO: specify
    for(bool b: _bits) {
      if(b) { return true; };
    }
    return false;
  }

  StrBitVec StrBitVec::neg() const {
    //$ ensures return.width() == this.width()
    // TODO: specify
    // Return 0 - this (mod 2^w)
    return StrBitVec::zeros(this->width()).sub(*this);
  }

  StrBitVec StrBitVec::add(const StrBitVec &rhs) const {
    //$ requires rhs.width() == this.width()
    //$ ensures return.width() == this.width()
    // TODO: specify
    // TODO: ensureSameWidth(rhs, "add");
    StrBitVec result(this->width());
    bool carry = false;
    for(std::size_t i = 0; i < width(); ++i) {
      const bool a = _bits[i], b = rhs._bits[i];
      result._bits[i] = (a ^ b) ^ carry;
      carry = (a & b) | (a & carry) | (b & carry);
    }
    return result;
  }

  StrBitVec StrBitVec::sub(const StrBitVec &rhs) const {
    //$ requires rhs.width() == this.width()
    //$ ensures return.width() == this.width()
    // TODO: specify
    // TODO: ensureSameWidth(rhs, "sub");
    StrBitVec result(width());
    bool borrow = false;
    for(std::size_t i = 0; i < width(); ++i) {
      const bool a = _bits[i], b = rhs._bits[i];
      result._bits[i] = (a ^ b) ^ borrow;
      borrow = (!a & b) | ((!(a) | b) & borrow);
    }
    return result;
  }

  StrBitVec StrBitVec::mul(const StrBitVec &rhs) const {
    // TODO: specify
    // TODO:ensureSameWidth(rhs, "mul");
    const std::size_t w = this->width();
    // Compute full 2w-bit product, return low w bits.
    std::vector<bool> full(2 * w, false);
    _mul(full, _bits, rhs._bits);
    StrBitVec out(w);
    for(std::size_t i = 0; i < w; ++i) { out._bits[i] = full[i]; }
    return out;
  }

  StrBitVec StrBitVec::udiv(const StrBitVec &rhs) const {
    // TODO:specify
    // TODO: ensureSameWidth(rhs, "udiv");
    const std::size_t w = width();
    if(rhs.is_zero()) { return StrBitVec::ones(w); }
    std::vector<bool> q(w, false), r; // remainder dynamic
    _udivrem_bits(_bits, rhs._bits, q, r);
    StrBitVec out(w);
    out._bits = std::move(q);
    return out;
  }

  StrBitVec StrBitVec::urem(const StrBitVec &rhs) const {
    // TODO:specify
    // TODO: ensureSameWidth(rhs, "urem");
    const std::size_t w = width();
    if(rhs.is_zero()) return *this;
    std::vector<bool> q(w, false), r;
    _udivrem_bits(_bits, rhs._bits, q, r);
    StrBitVec out(w);
    // copy low w bits of r
    for(std::size_t i = 0; i < w && i < r.size(); ++i) { out._bits[i] = r[i]; }
    return out;
  }

  StrBitVec StrBitVec::sdiv(const StrBitVec &rhs) const {
    // TODO: specify
    //TODO: ensureSameWidth(rhs, "sdiv");
    const std::size_t w = width();
    if(rhs.is_zero()) {
      return StrBitVec::ones(w); // -1
    }
    if(is_most_negative() && rhs.is_all_ones()) {
      return *this; // overflow case
    }

    const bool negA = is_negative();
    const bool negB = rhs.is_negative();

    StrBitVec aMag = negA ? this->neg() : *this;
    StrBitVec bMag = negB ? rhs.neg() : rhs;

    StrBitVec q = aMag.udiv(bMag);
    if(negA ^ negB) { q = q.neg(); }
    return q;
  }

  StrBitVec StrBitVec::srem(const StrBitVec &rhs) const {
    // TODO: specify
    // TODO: ensureSameWidth(rhs, "srem");
    const std::size_t w = width();
    if(rhs.is_zero()) { return *this; }
    if(is_most_negative() && rhs.is_all_ones()) {
      return StrBitVec::zeros(w); // 0
    }

    const bool negA = is_negative();
    const bool negB = rhs.is_negative();

    StrBitVec aMag = negA ? this->neg() : *this;
    StrBitVec bMag = negB ? rhs.neg() : rhs;

    StrBitVec r = aMag.urem(bMag);
    if(negA) { r = r.neg(); }
    return r;
  }

  StrBitVec StrBitVec::smod(const StrBitVec &rhs) const {
    // TODO: specify
    // TODO: ensureSameWidth(rhs, "smod");
    const std::size_t w = width();
    if(w == 0) return StrBitVec(0);
    if(rhs.is_zero()) { return *this; }
    if(is_most_negative() && rhs.is_all_ones()) return StrBitVec(w); // 0

    StrBitVec r = srem(rhs);
    if(r.is_zero()) { return r; }

    const bool signR = r.is_negative();
    const bool signY = rhs.is_negative();

    if(signR != signY) {
      // r += y (mod 2^w)
      r = r.add(rhs);
    }
    return r;
  }

  StrBitVec StrBitVec::shl(const StrBitVec &rhs) const {
    // TODO: specify
    // TODO: ensureSameWidth(rhs, "shl");
    const std::size_t w = width();
    bool ge = _rhs_amount_ge_width(rhs, w);
    if(ge) {
      return StrBitVec::zeros(w); // all zeros
    }
    std::size_t amt = _rhs_amount_mod(rhs, w); // exact, since < w
    StrBitVec out(w);
    for(std::size_t i = w; i-- > 0;) {
      if(i >= amt) out._bits[i] = _bits[i - amt];
    }
    return out;
  }

  StrBitVec StrBitVec::lshr(const StrBitVec &rhs) const {
    // TODO: specify
    // TODO: ensureSameWidth(rhs, "lshr");
    const std::size_t w = width();
    bool ge = _rhs_amount_ge_width(rhs, w);
    if(ge) {
      return StrBitVec::zeros(w); // all zeros
    }
    std::size_t amt = _rhs_amount_mod(rhs, w);
    StrBitVec out(w);
    for(std::size_t i = 0; i < w; ++i) {
      const std::size_t src = i + amt;
      if(src < w) out._bits[i] = _bits[src];
    }
    return out;
  }

  StrBitVec StrBitVec::ashr(const StrBitVec &rhs) const {
    // TODO: specify
    // TODO: ensureSameWidth(rhs, "ashr");
    const std::size_t w = width();
    const bool sign = is_negative();
    bool ge = _rhs_amount_ge_width(rhs, w);
    if(ge) { return sign ? StrBitVec::ones(w) : StrBitVec::zeros(w); }
    std::size_t amt = _rhs_amount_mod(rhs, w);
    StrBitVec out(w);
    for(std::size_t i = 0; i < w; ++i) {
      const std::size_t src = i + amt;
      out._bits[i] = (src < w) ? _bits[src] : sign;
    }
    return out;
  }

  bool StrBitVec::ult(const StrBitVec &rhs) const {
    // TODO: specify
    return _compare_unsigned(*this, rhs) < 0;
  }

  bool StrBitVec::ule(const StrBitVec &rhs) const {
    // TODO: specify
    return _compare_unsigned(*this, rhs) <= 0;
  }

  bool StrBitVec::uge(const StrBitVec &rhs) const {
    // TODO: specify
    return _compare_unsigned(*this, rhs) >= 0;
  }

  bool StrBitVec::ugt(const StrBitVec &rhs) const {
    // TODO: specify
    return _compare_unsigned(*this, rhs) > 0;
  }

  bool StrBitVec::eq(const StrBitVec &rhs) const {
    // TODO: specify
    return this->equals(rhs);
  }

  bool StrBitVec::equals(const StrBitVec &rhs) const {
    // TODO: specify
    return _compare_unsigned(*this, rhs) == 0;
  }

  bool StrBitVec::slt(const StrBitVec &rhs) const {
    // TODO: specify
    // TODO: ensureSameWidth(rhs, "slt");
    const bool sa = is_negative(), sb = rhs.is_negative();
    if(sa != sb) {
      return sa; // negative < positive
    }
    // Same sign: for negatives, reverse unsigned sense.
    int cu = _compare_unsigned(*this, rhs);
    return sa ? (cu > 0) : (cu < 0);
  }

  bool StrBitVec::sle(const StrBitVec &rhs) const {
    // TODO: specify
    return !sgt(rhs);
  }

  bool StrBitVec::sge(const StrBitVec &rhs) const {
    // TODO: specify
    return !slt(rhs);
  }

  bool StrBitVec::sgt(const StrBitVec &rhs) const {
    // TODO: specify
    // TODO: ensureSameWidth(rhs, "sgt");
    const bool sa = is_negative(), sb = rhs.is_negative();
    if(sa != sb) return !sa; // positive > negative
    int cu = _compare_unsigned(*this, rhs);
    return sa ? (cu < 0) : (cu > 0);
  }

  StrBitVec StrBitVec::comp(const StrBitVec &rhs) const {
    // TODO: specify
    // TODO: ensureSameWidth(rhs, "comp");
    StrBitVec out(1);
    out._bits[0] = equals(rhs);
    return out;
  }

  bool StrBitVec::nego() const {
    // TODO: specify
    return is_most_negative();
  }

  bool StrBitVec::uaddo(const StrBitVec &rhs) const {
    // TODO:ensureSameWidth(rhs, "uaddo");
    // TODO: make common code with uaddo
    bool carry = false;
    for(std::size_t i = 0; i < width(); ++i) {
      const bool a = _bits[i], b = rhs._bits[i];
      carry = (a & b) | (a & carry) | (b & carry);
    }
    return carry;
  }

  bool StrBitVec::saddo(const StrBitVec &rhs) const {
    // TODO: specify
    // TODO: ensureSameWidth(rhs, "saddo");
    if(width() == 0) return false;
    StrBitVec sum = add(rhs);
    const bool sa = is_negative();
    const bool sb = rhs.is_negative();
    const bool ss = sum.is_negative();
    return (sa == sb) && (ss != sa);
  }

  bool StrBitVec::umulo(const StrBitVec &rhs) const {
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

  bool StrBitVec::smulo(const StrBitVec &rhs) const {
    // TODO: specify
    // TODO: ensureSameWidth(rhs, "smulo");
    const std::size_t w = width();
    // Sign-extend both to 2w and multiply (unsigned), then check that the
    // upper w bits are a sign-extension of the sign bit of the low part.
    std::vector<bool> a2(2 * w, false), b2(2 * w, false);
    const bool sa = is_negative(), sb = rhs.is_negative();
    // copy low
    for(std::size_t i = 0; i < w; ++i) {
      a2[i] = _bits[i];
      b2[i] = rhs._bits[i];
    }
    // sign-extend
    for(std::size_t i = w; i < 2 * w; ++i) {
      a2[i] = sa;
      b2[i] = sb;
    }
    std::vector<bool> prod(2 * w, false);
    _mul(prod, a2, b2);
    const bool sign = prod[w - 1];
    for(std::size_t i = w; i < 2 * w; ++i) {
      if(prod[i] != sign) { return true; }
    }
    return false;
  }

  bool StrBitVec::usubo(const StrBitVec &rhs) const {
    // TODO: specify
    return ult(rhs);
  }

  bool StrBitVec::ssubo(const StrBitVec &rhs) const {
    // TODO: specify
    // TODO: ensureSameWidth(rhs, "ssubo");
    StrBitVec diff = sub(rhs);
    const bool sa = is_negative();
    const bool sb = rhs.is_negative();
    const bool sd = diff.is_negative();
    return (sa != sb) && (sd != sa);
  }

  bool StrBitVec::sdivo(const StrBitVec &rhs) const {
    // TODO: specify
    // TODO: ensureSameWidth(rhs, "sdivo");
    return is_most_negative() && rhs.is_all_ones();
  }

  std::string StrBitVec::u_to_int() const {
    // TODO: specify
    // Build decimal by scanning from MSB to LSB: s = s*2 + bit
    std::string s = "0";
    int msb = _msb_index(_bits);
    if(msb < 0) { return "0"; }
    for(int i = msb; i >= 0; --i) {
      _dec_mul_add(s, 2, 0);
      if(_bits[static_cast<std::size_t>(i)]) {
        _dec_mul_add(s, 1, 1); // +1
      }
    }
    _trim_leading_zeros(s);
    return s;
  }

  std::string StrBitVec::s_to_int() const {
    // TODO: specify
    if(!is_negative()) { return u_to_int(); }

    // magnitude = two's-complement negation
    StrBitVec mag = this->neg();
    std::string s = mag.u_to_int();
    _trim_leading_zeros(s);
    return "-" + s;
  }

  bool StrBitVec::_is_decimal_zero(const std::string &s) {
    for(char c: s) {
      if(c != '0') { return false; }
    }
    return true;
  }

  int StrBitVec::_div_decimal_by_2(std::string &s) {
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

  void StrBitVec::_trim_leading_zeros(std::string &s) {
    std::size_t i = 0;
    while(i + 1 < s.size() && s[i] == CodePoint::$0) { ++i; }
    if(i) { s.erase(0, i); }
  }

  // Add a*b into 'acc' (acc has size >= a.size()+b.size())
  void StrBitVec::_mul(std::vector<bool> &acc, const std::vector<bool> &a, const std::vector<bool> &b) {
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
          break; // should not happen if acc large enough
        }
      }
    }
  }

  // TODO: + rename to ucomp
  int StrBitVec::_compare_unsigned(const StrBitVec &a, const StrBitVec &b) {
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

  // Unsigned division: compute quotient q (size w) and remainder r (dynamic).
  void StrBitVec::_udivrem_bits(const std::vector<bool> &num, const std::vector<bool> &den, std::vector<bool> &q,
                             std::vector<bool> &r) {
    const std::size_t w = q.size();
    r.clear(); // remainder, LSB-first dynamic
    // Process bits from MSB to LSB.
    for(std::size_t step = 0; step < w; ++step) {
      const std::size_t i = w - 1 - step; // current source bit index
      // r = (r << 1) | num[i]
      r.insert(r.begin(), false); // left shift by 1 (multiply by 2)
      if(!r.empty()) { r[0] = num[i]; }
      _trim_bits(r);
      // if r >= den then r -= den, q[i] = 1 else 0
      if(_cmp_arb_unsigned(r, den) >= 0) {
        _sub_arb_unsigned_in_place(r, den);
        q[i] = true;
      } else {
        q[i] = false;
      }
    }
    _trim_bits(r);
  }

  // Compare arbitrary-length LSB-first vectors (unsigned).
  int StrBitVec::_cmp_arb_unsigned(const std::vector<bool> &a, const std::vector<bool> &b) {
    const int ma = _msb_index(a);
    const int mb = _msb_index(b);
    if(ma != mb) return (ma < mb) ? -1 : 1;
    for(int i = ma; i >= 0; --i) {
      const bool abit = a[static_cast<std::size_t>(i)];
      const bool bbit = b[static_cast<std::size_t>(i)];
      if(abit != bbit) return abit ? 1 : -1;
    }
    return 0;
  }

  // a -= b, assumes a >= b (unsigned), arbitrary-length LSB-first.
  void StrBitVec::_sub_arb_unsigned_in_place(std::vector<bool> &a, const std::vector<bool> &b) {
    bool borrow = false;
    const std::size_t n = std::max(a.size(), b.size());
    if(a.size() < n) a.resize(n, false);
    for(std::size_t i = 0; i < n; ++i) {
      const bool ai = (i < a.size()) ? a[i] : false;
      const bool bi = (i < b.size()) ? b[i] : false;
      const bool diff = (ai ^ bi) ^ borrow;
      borrow = (!ai & bi) | ((!(ai) | bi) & borrow);
      a[i] = diff;
    }
    _trim_bits(a);
  }

  void StrBitVec::_trim_bits(std::vector<bool> &v) {
    // Remove leading zeros in MSB direction (but keep at least one 0 if empty).
    int m = _msb_index(v);
    if(m < 0) {
      v.clear();
    } else if(static_cast<std::size_t>(m + 1) < v.size()) {
      v.resize(static_cast<std::size_t>(m + 1));
    }
  }

  int StrBitVec::_msb_index(const std::vector<bool> &v) {
    for(int i = static_cast<int>(v.size()) - 1; i >= 0; --i)
      if(v[static_cast<std::size_t>(i)]) return i;
    return -1;
  }

  void StrBitVec::_dec_mul_add(std::string &s, int mul, int add) {
    int carry = add;
    for(int i = static_cast<int>(s.size()) - 1; i >= 0; --i) {
      int d = (s[static_cast<std::size_t>(i)] - CodePoint::$0) * mul + carry;
      s[static_cast<std::size_t>(i)] = static_cast<char>(CodePoint::$0 + (d % 10));
      carry = d / 10;
    }
    while(carry > 0) {
      s.insert(s.begin(), static_cast<char>(CodePoint::$0 + (carry % 10)));
      carry /= 10;
    }
  }

  std::size_t StrBitVec::_rhs_amount_mod(const StrBitVec &amt, std::size_t mod) {
    if(mod == 0) { return 0; }
    // Horner: ((...((0*2 + bN)*2 + bN-1)... ) % mod)
    std::size_t r = 0;
    for(int i = _msb_index(amt._bits); i >= 0; --i) {
      r = (r * 2) % mod;
      if(amt._bits[static_cast<std::size_t>(i)]) { r = (r + 1) % mod; }
    }
    return r;
  }

  bool StrBitVec::_rhs_amount_ge_width(const StrBitVec &amt, std::size_t w) {
    if(w == 0) {
      return true; // any amount >= 0 when width==0
    }
    int ma = _msb_index(amt._bits);
    if(ma < 0) { return false; }
    int mw = 0;
    for(std::size_t tmp = w >> 1; tmp > 0; tmp >>= 1) { ++mw; }
    if(ma > mw) { return true; }
    if(ma < mw) { return false; }
    for(int i = mw; i >= 0; --i) {
      const bool abit = amt._bits[static_cast<std::size_t>(i)];
      const bool wbit = ((w >> i) & 1u) != 0;
      if(abit != wbit) return abit; // true if amt bit is 1 when w bit 0
    }
    return true; // equal
  }

} // namespace btgly