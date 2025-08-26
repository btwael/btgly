//
// Created by Wael-Amine Boutglay on 26/08/2025.
//

#include "btgly/bitvec.hh"

namespace btgly {

  //*-- BitVec

  BitVec::BitVec(std::size_t width) : _bits(width) {}

  BitVec::BitVec(bool value, std::size_t width) : _bits(width, value) {}

  BitVec BitVec::zeros(std::size_t width) { return BitVec(0, width); }

  BitVec BitVec::ones(std::size_t width) { return BitVec(1, width); }

  BitVec BitVec::from_int(std::string s, std::size_t width) {
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

  //*- properties

  std::size_t BitVec::width() const { return _bits.size(); }

  bool BitVec::is_all_ones() const { return redand(); }

  bool BitVec::is_zero() const { return !redor(); }

  bool BitVec::is_negative() const { return _bits[this->width() - 1]; }

  bool BitVec::is_most_negative() const {
    const std::size_t w = width();
    if(!_bits[w - 1]) {
      return false; // sign bit must be 1
    }
    for(std::size_t i = 0; i + 1 < w; ++i) {
      if(_bits[i]) return false; // all others must be 0
    }
    return true;
  }

  //*- methods

  BitVec BitVec::concat(const BitVec &rhs) const {
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

  BitVec BitVec::extract(std::size_t i, std::size_t j) const {
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

  BitVec BitVec::repeat(std::size_t k) const {
    // TODO: specify
    if(k == 0) { return BitVec::zeros(0); }
    BitVec result(width() * k);
    for(std::size_t r = 0; r < k; ++r) {
      for(std::size_t i = 0; i < this->width(); ++i) { result._bits[r * this->width() + i] = _bits[i]; }
    }
    return result;
  }

  BitVec BitVec::sign_extend(std::size_t k) const {
    // TODO: specify
    BitVec result(0, this->width() + k);
    const bool sign = _bits[width() - 1];
    for(std::size_t i = 0; i < this->width(); ++i) { result._bits[i] = _bits[i]; }
    for(std::size_t i = this->width(); i < result.width(); ++i) { result._bits[i] = sign; }
    return result;
  }

  BitVec BitVec::zero_extend(std::size_t k) const {
    // TODO: specify
    BitVec out(0, width() + k);
    for(std::size_t i = 0; i < width(); ++i) { out._bits[i] = _bits[i]; }
    return out;
  }

  BitVec BitVec::rotate_left(std::size_t k) const {
    // TODO: specify
    const std::size_t w = width();
    k %= w;
    BitVec out(w);
    for(std::size_t i = 0; i < w; ++i) {
      // new[i] = old[(i - k) mod w]
      const std::size_t src = (i + w - (k % w)) % w;
      out._bits[i] = _bits[src];
    }
    return out;
  }

  BitVec BitVec::rotate_right(std::size_t k) const {
    // TODO: specify
    const std::size_t w = width();
    k %= w;
    BitVec out(w);
    for(std::size_t i = 0; i < w; ++i) {
      // new[i] = old[(i + k) mod w]
      const std::size_t src = (i + (k % w)) % w;
      out._bits[i] = _bits[src];
    }
    return out;
  }

  BitVec BitVec::$not() const {
    //$ ensures return.width() == this.width()
    //$ ensures forall k: Int :: 0 <= k < rhs.width() => return[k] == !this[k]
    BitVec result(this->width());
    for(std::size_t i = 0; i < width(); ++i) { result._bits[i] = !_bits[i]; }
    return result;
  }

  BitVec BitVec::$and(const BitVec &rhs) const {
    //$ requires rhs.width() == this.width()
    //$ ensures return.width() == this.width()
    //$ ensures forall k: Int :: 0 <= k < rhs.width() => return[k] == (this[k] && rhs[k])
    // TODO: ensureSameWidth(rhs, "$and");
    BitVec result(width());
    for(std::size_t i = 0; i < width(); ++i) { result._bits[i] = _bits[i] & rhs._bits[i]; }
    return result;
  }

  BitVec BitVec::$or(const BitVec &rhs) const {
    //$ requires rhs.width() == this.width()
    //$ ensures return.width() == this.width()
    //$ ensures forall k: Int :: 0 <= k < rhs.width() => return[k] == (this[k] || rhs[k])
    // TODO: ensureSameWidth(rhs, "or");
    BitVec result(width());
    for(std::size_t i = 0; i < width(); ++i) { result._bits[i] = _bits[i] | rhs._bits[i]; }
    return result;
  }

  BitVec BitVec::$xor(const BitVec &rhs) const {
    //$ requires rhs.width() == this.width()
    //$ ensures return.width() == this.width()
    //$ ensures forall k: Int :: 0 <= k < rhs.width() => return[k] == (this[k] ^ rhs[k])
    // TODO: ensureSameWidth(rhs, "$xor");
    BitVec result(width());
    for(std::size_t i = 0; i < width(); ++i) { result._bits[i] = _bits[i] ^ rhs._bits[i]; }
    return result;
  }

  BitVec BitVec::nand(const BitVec &rhs) const {
    // TODO: specify
    return $and(rhs).$not();
  }

  BitVec BitVec::nor(const BitVec &rhs) const {
    // TODO: specify
    return $or(rhs).$not();
  }

  BitVec BitVec::xnor(const BitVec &rhs) const {
    // TODO: specify
    return $xor(rhs).$not();
  }

  bool BitVec::redand() const {
    // TODO: specify
    for(bool b: _bits) {
      if(!b) { return false; }
    }
    return true;
  }

  bool BitVec::redor() const {
    // TODO: specify
    for(bool b: _bits) {
      if(b) { return true; };
    }
    return false;
  }

  BitVec BitVec::neg() const {
    //$ ensures return.width() == this.width()
    // TODO: specify
    // Return 0 - this (mod 2^w)
    return BitVec::zeros(this->width()).sub(*this);
  }

  BitVec BitVec::add(const BitVec &rhs) const {
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

  BitVec BitVec::sub(const BitVec &rhs) const {
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

  BitVec BitVec::mul(const BitVec &rhs) const {
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

  BitVec BitVec::udiv(const BitVec &rhs) const {
    // TODO:specify
    // TODO: ensureSameWidth(rhs, "udiv");
    const std::size_t w = width();
    if(rhs.is_zero()) { return BitVec::ones(w); }
    std::vector<bool> q(w, false), r; // remainder dynamic
    _udivrem_bits(_bits, rhs._bits, q, r);
    BitVec out(w);
    out._bits = std::move(q);
    return out;
  }

  BitVec BitVec::urem(const BitVec &rhs) const {
    // TODO:specify
    // TODO: ensureSameWidth(rhs, "urem");
    const std::size_t w = width();
    if(rhs.is_zero()) return *this;
    std::vector<bool> q(w, false), r;
    _udivrem_bits(_bits, rhs._bits, q, r);
    BitVec out(w);
    // copy low w bits of r
    for(std::size_t i = 0; i < w && i < r.size(); ++i) { out._bits[i] = r[i]; }
    return out;
  }

  BitVec BitVec::sdiv(const BitVec &rhs) const {
    // TODO: specify
    //TODO: ensureSameWidth(rhs, "sdiv");
    const std::size_t w = width();
    if(rhs.is_zero()) {
      return BitVec::ones(w); // -1
    }
    if(is_most_negative() && rhs.is_all_ones()) {
      return *this; // overflow case
    }

    const bool negA = is_negative();
    const bool negB = rhs.is_negative();

    BitVec aMag = negA ? this->neg() : *this;
    BitVec bMag = negB ? rhs.neg() : rhs;

    BitVec q = aMag.udiv(bMag);
    if(negA ^ negB) { q = q.neg(); }
    return q;
  }

  BitVec BitVec::srem(const BitVec &rhs) const {
    // TODO: specify
    // TODO: ensureSameWidth(rhs, "srem");
    const std::size_t w = width();
    if(rhs.is_zero()) { return *this; }
    if(is_most_negative() && rhs.is_all_ones()) {
      return BitVec::zeros(w); // 0
    }

    const bool negA = is_negative();
    const bool negB = rhs.is_negative();

    BitVec aMag = negA ? this->neg() : *this;
    BitVec bMag = negB ? rhs.neg() : rhs;

    BitVec r = aMag.urem(bMag);
    if(negA) { r = r.neg(); }
    return r;
  }

  BitVec BitVec::smod(const BitVec &rhs) const {
    // TODO: specify
    // TODO: ensureSameWidth(rhs, "smod");
    const std::size_t w = width();
    if(w == 0) return BitVec(0);
    if(rhs.is_zero()) { return *this; }
    if(is_most_negative() && rhs.is_all_ones()) return BitVec(w); // 0

    BitVec r = srem(rhs);
    if(r.is_zero()) { return r; }

    const bool signR = r.is_negative();
    const bool signY = rhs.is_negative();

    if(signR != signY) {
      // r += y (mod 2^w)
      r = r.add(rhs);
    }
    return r;
  }

  BitVec BitVec::shl(const BitVec &rhs) const {
    // TODO: specify
    // TODO: ensureSameWidth(rhs, "shl");
    const std::size_t w = width();
    bool ge = _rhs_amount_ge_width(rhs, w);
    if(ge) {
      return BitVec::zeros(w); // all zeros
    }
    std::size_t amt = _rhs_amount_mod(rhs, w); // exact, since < w
    BitVec out(w);
    for(std::size_t i = w; i-- > 0;) {
      if(i >= amt) out._bits[i] = _bits[i - amt];
    }
    return out;
  }

  BitVec BitVec::lshr(const BitVec &rhs) const {
    // TODO: specify
    // TODO: ensureSameWidth(rhs, "lshr");
    const std::size_t w = width();
    bool ge = _rhs_amount_ge_width(rhs, w);
    if(ge) {
      return BitVec::zeros(w); // all zeros
    }
    std::size_t amt = _rhs_amount_mod(rhs, w);
    BitVec out(w);
    for(std::size_t i = 0; i < w; ++i) {
      const std::size_t src = i + amt;
      if(src < w) out._bits[i] = _bits[src];
    }
    return out;
  }

  BitVec BitVec::ashr(const BitVec &rhs) const {
    // TODO: specify
    // TODO: ensureSameWidth(rhs, "ashr");
    const std::size_t w = width();
    const bool sign = is_negative();
    bool ge = _rhs_amount_ge_width(rhs, w);
    if(ge) { return sign ? BitVec::ones(w) : BitVec::zeros(w); }
    std::size_t amt = _rhs_amount_mod(rhs, w);
    BitVec out(w);
    for(std::size_t i = 0; i < w; ++i) {
      const std::size_t src = i + amt;
      out._bits[i] = (src < w) ? _bits[src] : sign;
    }
    return out;
  }

  bool BitVec::ult(const BitVec &rhs) const {
    // TODO: specify
    return _compare_unsigned(*this, rhs) < 0;
  }

  bool BitVec::ule(const BitVec &rhs) const {
    // TODO: specify
    return _compare_unsigned(*this, rhs) <= 0;
  }

  bool BitVec::uge(const BitVec &rhs) const {
    // TODO: specify
    return _compare_unsigned(*this, rhs) >= 0;
  }

  bool BitVec::ugt(const BitVec &rhs) const {
    // TODO: specify
    return _compare_unsigned(*this, rhs) > 0;
  }

  bool BitVec::eq(const BitVec &rhs) const {
    // TODO: specify
    return this->equals(rhs);
  }

  bool BitVec::equals(const BitVec &rhs) const {
    // TODO: specify
    return _compare_unsigned(*this, rhs) == 0;
  }

  bool BitVec::slt(const BitVec &rhs) const {
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

  bool BitVec::sle(const BitVec &rhs) const {
    // TODO: specify
    return !sgt(rhs);
  }

  bool BitVec::sge(const BitVec &rhs) const {
    // TODO: specify
    return !slt(rhs);
  }

  bool BitVec::sgt(const BitVec &rhs) const {
    // TODO: specify
    // TODO: ensureSameWidth(rhs, "sgt");
    const bool sa = is_negative(), sb = rhs.is_negative();
    if(sa != sb) return !sa; // positive > negative
    int cu = _compare_unsigned(*this, rhs);
    return sa ? (cu < 0) : (cu > 0);
  }

  BitVec BitVec::comp(const BitVec &rhs) const {
    // TODO: specify
    // TODO: ensureSameWidth(rhs, "comp");
    BitVec out(1);
    out._bits[0] = equals(rhs);
    return out;
  }

  bool BitVec::nego() const {
    // TODO: specify
    return is_most_negative();
  }

  bool BitVec::uaddo(const BitVec &rhs) const {
    // TODO:ensureSameWidth(rhs, "uaddo");
    // TODO: make common code with uaddo
    bool carry = false;
    for(std::size_t i = 0; i < width(); ++i) {
      const bool a = _bits[i], b = rhs._bits[i];
      carry = (a & b) | (a & carry) | (b & carry);
    }
    return carry;
  }

  bool BitVec::saddo(const BitVec &rhs) const {
    // TODO: specify
    // TODO: ensureSameWidth(rhs, "saddo");
    if(width() == 0) return false;
    BitVec sum = add(rhs);
    const bool sa = is_negative();
    const bool sb = rhs.is_negative();
    const bool ss = sum.is_negative();
    return (sa == sb) && (ss != sa);
  }

  bool BitVec::umulo(const BitVec &rhs) const {
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

  bool BitVec::smulo(const BitVec &rhs) const {
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

  bool BitVec::usubo(const BitVec &rhs) const {
    // TODO: specify
    return ult(rhs);
  }

  bool BitVec::ssubo(const BitVec &rhs) const {
    // TODO: specify
    // TODO: ensureSameWidth(rhs, "ssubo");
    BitVec diff = sub(rhs);
    const bool sa = is_negative();
    const bool sb = rhs.is_negative();
    const bool sd = diff.is_negative();
    return (sa != sb) && (sd != sa);
  }

  bool BitVec::sdivo(const BitVec &rhs) const {
    // TODO: specify
    // TODO: ensureSameWidth(rhs, "sdivo");
    return is_most_negative() && rhs.is_all_ones();
  }

  std::string BitVec::u_to_int() const {
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

  std::string BitVec::s_to_int() const {
    // TODO: specify
    if(!is_negative()) { return u_to_int(); }

    // magnitude = two's-complement negation
    BitVec mag = this->neg();
    std::string s = mag.u_to_int();
    _trim_leading_zeros(s);
    return "-" + s;
  }

  bool BitVec::_is_decimal_zero(const std::string &s) {
    for(char c: s) {
      if(c != '0') { return false; }
    }
    return true;
  }

  int BitVec::_div_decimal_by_2(std::string &s) {
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

  void BitVec::_trim_leading_zeros(std::string &s) {
    std::size_t i = 0;
    while(i + 1 < s.size() && s[i] == CodePoint::$0) { ++i; }
    if(i) { s.erase(0, i); }
  }

  // Add a*b into 'acc' (acc has size >= a.size()+b.size())
  void BitVec::_mul(std::vector<bool> &acc, const std::vector<bool> &a, const std::vector<bool> &b) {
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
  int BitVec::_compare_unsigned(const BitVec &a, const BitVec &b) {
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
  void BitVec::_udivrem_bits(const std::vector<bool> &num, const std::vector<bool> &den, std::vector<bool> &q,
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
  int BitVec::_cmp_arb_unsigned(const std::vector<bool> &a, const std::vector<bool> &b) {
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
  void BitVec::_sub_arb_unsigned_in_place(std::vector<bool> &a, const std::vector<bool> &b) {
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

  void BitVec::_trim_bits(std::vector<bool> &v) {
    // Remove leading zeros in MSB direction (but keep at least one 0 if empty).
    int m = _msb_index(v);
    if(m < 0) {
      v.clear();
    } else if(static_cast<std::size_t>(m + 1) < v.size()) {
      v.resize(static_cast<std::size_t>(m + 1));
    }
  }

  int BitVec::_msb_index(const std::vector<bool> &v) {
    for(int i = static_cast<int>(v.size()) - 1; i >= 0; --i)
      if(v[static_cast<std::size_t>(i)]) return i;
    return -1;
  }

  void BitVec::_dec_mul_add(std::string &s, int mul, int add) {
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

  std::size_t BitVec::_rhs_amount_mod(const BitVec &amt, std::size_t mod) {
    if(mod == 0) { return 0; }
    // Horner: ((...((0*2 + bN)*2 + bN-1)... ) % mod)
    std::size_t r = 0;
    for(int i = _msb_index(amt._bits); i >= 0; --i) {
      r = (r * 2) % mod;
      if(amt._bits[static_cast<std::size_t>(i)]) { r = (r + 1) % mod; }
    }
    return r;
  }

  bool BitVec::_rhs_amount_ge_width(const BitVec &amt, std::size_t w) {
    if(w == 0) {
      return true; // treat as >=
    }
    // Compare value(amt) >= w using bitwise comparison against binary(w).
    int ma = _msb_index(amt._bits);
    if(ma < 0) {
      return false; // 0 < w (assuming w>0)
    }
    int mw = 0;
    {
      std::size_t tmp = w;
      while((tmp >> (mw + 1)) != 0) ++mw;
      if(w == 1) mw = 0; // fix for w=1
      // For w power-of-two, mw == log2(w). Numbers with msb > mw are >= w,
      // with msb == mw we must compare bits.
      while((static_cast<std::size_t>(1) << mw) > w && mw > 0) {
        --mw; // guard
      }
      while(((static_cast<std::size_t>(1) << (mw + 1)) <= w)) { ++mw; }
    }
    if(ma > mw) { return true; }
    if(ma < mw) { return false; }
    // msb equal; compare bit by bit from mw..0
    for(int i = mw; i >= 0; --i) {
      const bool abit = amt._bits[static_cast<std::size_t>(i)];
      const bool wbit = ((w >> i) & 1u) != 0;
      if(abit != wbit) {
        return abit; // true if abit==1 and wbit==0
      }
    }
    return true; // equal
  }

} // namespace btgly