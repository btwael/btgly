//
// Created by Wael-Amine Boutglay on 26/08/2025.
//

#include "btgly/bitvec.hh"
#include <bit>
#include <stdexcept>

namespace btgly {

  //*-- BitVec

  BitVec::BitVec(std::size_t width) : _width(width), _storage(Small{0}) {
    if(is_small()) {
      _storage = trim(Small{0}, width);
    } else {
      _storage = Large(width, false);
    }
  }

  BitVec::BitVec(bool value, std::size_t width) : _width(width), _storage(Small{0}) {
    if(is_small()) {
      _storage = trim(value ? ~Small{0} : Small{0}, width);
    } else {
      _storage = Large(width, value);
    }
  }

  BitVec BitVec::zeros(std::size_t width) { return {false, width}; }

  BitVec BitVec::ones(std::size_t width) { return {true, width}; }

  BitVec BitVec::from_int(std::string s, std::size_t width) {
    // TODO: specify
    // TODO: deal with empty or illegal string
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

    std::vector<bool> bits(width);
    if(base == Radix::Binary) { // parse binary integer
      std::size_t pos = 0;
      for(std::size_t k = 0; k < s.size(); ++k) {
        char c = s[s.size() - 1 - k];
        if(c != CodePoint::$0 && c != CodePoint::$1) { throw std::invalid_argument("invalid binary digit"); }
        if(pos < width) { bits[pos] = (c == CodePoint::$1); }
        ++pos;
      }
    } else if(base == Radix::Octal) { // parse octal integer
      std::size_t pos = 0;
      for(std::size_t k = 0; k < s.size(); ++k) {
        char c = s[s.size() - 1 - k];
        if(c < CodePoint::$0 || c > CodePoint::$7) { throw std::invalid_argument("invalid octal digit"); }
        int v = c - CodePoint::$0;
        for(int b = 0; b < 3; ++b) {
          if(pos < width) { bits[pos] = (v >> b) & 1; }
          ++pos;
        }
      }
    } else if(base == Radix::Hexadecimal) { // parse hex integer
      std::size_t pos = 0;
      for(std::size_t k = 0; k < s.size(); ++k) {
        int v = CodePoint::hex_to_int(s[s.size() - 1 - k]);
        if(v < 0) { throw std::invalid_argument("invalid hexadecimal digit"); }
        for(int b = 0; b < 4; ++b) {
          if(pos < width) { bits[pos] = (v >> b) & 1; }
          ++pos;
        }
      }
    } else { // parse decimal integer
      std::string dec = s;
      std::size_t pos = 0;
      while(!_is_decimal_zero(dec) && pos < width) {
        int rem = _div_decimal_by_2(dec);
        bits[pos++] = (rem != 0);
      }
    }

    BitVec result(width);
    if(result.is_small()) {
      Small small = 0;
      const std::size_t w = result._width;
      for(std::size_t i = 0; i < w && i < 64; ++i) {
        if(bits[i]) { small |= (Small{1} << i); }
      }
      result._storage = trim(small, w);
    } else {
      result.large_ref() = bits;
    }

    // negate if negative
    if(neg) { result = result.neg(); }

    return result;
  }

  //*- properties

  const std::vector<bool> &BitVec::bits() const { return _bits(); }

  std::size_t BitVec::width() const { return _width; }

  bool BitVec::is_all_ones() const { return redand(); }

  bool BitVec::is_zero() const { return !redor(); }

  bool BitVec::is_negative() const { return _width != 0 && _bits()[_width - 1]; }

  bool BitVec::is_most_negative() const {
    const std::size_t w = _width;
    if(w == 0) { return false; }
    if(!_bits()[w - 1]) {
      return false; // sign bit must be 1
    }
    for(std::size_t i = 0; i + 1 < w; ++i) {
      if(_bits()[i]) return false; // all others must be 0
    }
    return true;
  }

  //*- methods

  BitVec BitVec::concat(const BitVec &rhs) const {
    //$ ensures return._width == this._width + rhs._width
    //$ ensures forall k: Int :: 0 <= k < rhs._width => return[k] == rhs[k]
    //$ ensures forall k: Int :: 0 <= k < this._width => return[rhs._width + k] == this[k]
    BitVec result(this->_width + rhs._width);
    // Low part from rhs
    for(std::size_t i = 0; i < rhs._width; ++i) { result._bits()[i] = rhs._bits()[i]; }
    // High part from this
    for(std::size_t i = 0; i < this->_width; ++i) { result._bits()[i + rhs._width] = _bits()[i]; }
    if(result.is_small()) {
      Small small = 0;
      const std::size_t w = result._width;
      for(std::size_t i = 0; i < w && i < 64; ++i) {
        if(result._bits()[i]) { small |= (Small{1} << i); }
      }
      result._storage = trim(small, w);
    }
    return result;
  }

  BitVec BitVec::extract(std::size_t i, std::size_t j) const {
    // TODO: specify
    if(i < j) { throw std::invalid_argument("extract: i < j"); }
    if(i >= this->_width) { throw std::out_of_range("extract: high index out of range"); }
    const std::size_t w = i - j + 1;
    BitVec result(w);
    for(std::size_t k = 0; k < w; ++k) {
      const std::size_t src = j + k;
      result._bits()[k] = _bits()[src];
    }
    if(result.is_small()) {
      Small small = 0;
      for(std::size_t k = 0; k < w && k < 64; ++k) {
        if(result._bits()[k]) { small |= (Small{1} << k); }
      }
      result._storage = trim(small, w);
    }
    return result;
  }

  BitVec BitVec::repeat(std::size_t k) const {
    // TODO: specify
    if(k == 0) { return BitVec::zeros(0); }
    BitVec result(_width * k);
    for(std::size_t r = 0; r < k; ++r) {
      for(std::size_t i = 0; i < this->_width; ++i) { result._bits()[r * this->_width + i] = _bits()[i]; }
    }
    if(result.is_small()) {
      Small small = 0;
      const std::size_t w = result._width;
      for(std::size_t i = 0; i < w && i < 64; ++i) {
        if(result._bits()[i]) { small |= (Small{1} << i); }
      }
      result._storage = trim(small, w);
    }
    return result;
  }

  BitVec BitVec::sign_extend(std::size_t k) const {
    // TODO: specify
    BitVec result(false, this->_width + k);
    const bool sign = _width != 0 && _bits()[_width - 1];
    for(std::size_t i = 0; i < this->_width; ++i) { result._bits()[i] = _bits()[i]; }
    for(std::size_t i = this->_width; i < result._width; ++i) { result._bits()[i] = sign; }
    if(result.is_small()) {
      Small small = 0;
      const std::size_t w = result._width;
      for(std::size_t i = 0; i < w && i < 64; ++i) {
        if(result._bits()[i]) { small |= (Small{1} << i); }
      }
      result._storage = trim(small, w);
    }
    return result;
  }

  BitVec BitVec::zero_extend(std::size_t k) const {
    // TODO: specify
    BitVec result(false, _width + k);
    for(std::size_t i = 0; i < _width; ++i) { result._bits()[i] = _bits()[i]; }
    if(result.is_small()) {
      Small small = 0;
      const std::size_t w = result._width;
      for(std::size_t i = 0; i < w && i < 64; ++i) {
        if(result._bits()[i]) { small |= (Small{1} << i); }
      }
      result._storage = trim(small, w);
    }
    return result;
  }

  BitVec BitVec::rotate_left(std::size_t k) const {
    // TODO: specify
    const std::size_t w = _width;
    if(w == 0) return BitVec(0);
    k %= w;
    BitVec result(w);
    if(is_small()) {
      Small val = as_small();
      Small rot;
#if defined(__cpp_lib_bitops)
      if(w == 64) {
        rot = std::rotl(val, static_cast<int>(k));
      } else
#endif
      {
        rot = (k == 0) ? val : ((val << k) | (val >> (w - k)));
      }
      rot = trim(rot, w);
      result._storage = rot;
      for(std::size_t i = 0; i < w; ++i) { result._bits()[i] = (rot >> i) & Small{1}; }
    } else {
      Large &out = result.large_ref();
      const Large &lhs = large_ref();
      for(std::size_t i = 0; i < w; ++i) {
        const std::size_t src = (i + w - k) % w;
        bool bit = lhs[src];
        out[i] = bit;
        result._bits()[i] = bit;
      }
    }
    return result;
  }

  BitVec BitVec::rotate_right(std::size_t k) const {
    // TODO: specify
    const std::size_t w = _width;
    if(w == 0) return BitVec(0);
    k %= w;
    BitVec result(w);
    if(is_small()) {
      Small val = as_small();
      Small rot;
#if defined(__cpp_lib_bitops)
      if(w == 64) {
        rot = std::rotr(val, static_cast<int>(k));
      } else
#endif
      {
        rot = (k == 0) ? val : ((val >> k) | (val << (w - k)));
      }
      rot = trim(rot, w);
      result._storage = rot;
      for(std::size_t i = 0; i < w; ++i) { result._bits()[i] = (rot >> i) & Small{1}; }
    } else {
      Large &out = result.large_ref();
      const Large &lhs = large_ref();
      for(std::size_t i = 0; i < w; ++i) {
        const std::size_t src = (i + k) % w;
        bool bit = lhs[src];
        out[i] = bit;
        result._bits()[i] = bit;
      }
    }
    return result;
  }

  BitVec BitVec::$not() const {
    //$ ensures return._width == this._width
    //$ ensures forall k: Int :: 0 <= k < rhs._width => return[k] == !this[k]
    if(!is_small()) {
      BitVec result(_width);
      Large &out = result.large_ref();
      const Large &lhs = large_ref();
      for(std::size_t i = 0; i < _width; ++i) {
        bool bit = !lhs[i];
        out[i] = bit;
        result._bits()[i] = bit;
      }
      return result;
    }
    Small val = trim(~as_small(), _width);
    BitVec result(_width);
    result._storage = val;
    return result;
  }

  BitVec BitVec::$and(const BitVec &rhs) const {
    //$ requires rhs._width == this._width
    //$ ensures return._width == this._width
    //$ ensures forall k: Int :: 0 <= k < rhs._width => return[k] == (this[k] && rhs[k])
    _ensure_same_width(rhs, "$and");
    if(!(is_small() && rhs.is_small())) {
      BitVec result(_width);
      Large &out = result.large_ref();
      for(std::size_t i = 0; i < _width; ++i) {
        bool bit = _bits()[i] & rhs._bits()[i];
        out[i] = bit;
        result._bits()[i] = bit;
      }
      return result;
    }
    Small val = trim(as_small() & rhs.as_small(), _width);
    BitVec result(_width);
    result._storage = val;
    return result;
  }

  BitVec BitVec::$or(const BitVec &rhs) const {
    //$ requires rhs._width == this._width
    //$ ensures return._width == this._width
    //$ ensures forall k: Int :: 0 <= k < rhs._width => return[k] == (this[k] || rhs[k])
    _ensure_same_width(rhs, "$or");
    if(!(is_small() && rhs.is_small())) {
      BitVec result(_width);
      Large &out = result.large_ref();
      for(std::size_t i = 0; i < _width; ++i) {
        bool bit = _bits()[i] | rhs._bits()[i];
        out[i] = bit;
        result._bits()[i] = bit;
      }
      return result;
    }
    Small val = trim(as_small() | rhs.as_small(), _width);
    BitVec result(_width);
    result._storage = val;
    return result;
  }

  BitVec BitVec::$xor(const BitVec &rhs) const {
    //$ requires rhs._width == this._width
    //$ ensures return._width == this._width
    //$ ensures forall k: Int :: 0 <= k < rhs._width => return[k] == (this[k] ^ rhs[k])
    _ensure_same_width(rhs, "$xor");
    if(!(is_small() && rhs.is_small())) {
      BitVec result(_width);
      Large &out = result.large_ref();
      for(std::size_t i = 0; i < _width; ++i) {
        bool bit = _bits()[i] ^ rhs._bits()[i];
        out[i] = bit;
        result._bits()[i] = bit;
      }
      return result;
    }
    Small val = trim(as_small() ^ rhs.as_small(), _width);
    BitVec result(_width);
    result._storage = val;
    return result;
  }

  BitVec BitVec::nand(const BitVec &rhs) const {
    // TODO: specify
    if(!(is_small() && rhs.is_small())) {
      BitVec result(_width);
      Large &out = result.large_ref();
      for(std::size_t i = 0; i < _width; ++i) {
        bool bit = !(_bits()[i] & rhs._bits()[i]);
        out[i] = bit;
        result._bits()[i] = bit;
      }
      return result;
    }
    Small val = trim(~(as_small() & rhs.as_small()), _width);
    BitVec result(_width);
    result._storage = val;
    return result;
  }

  BitVec BitVec::nor(const BitVec &rhs) const {
    // TODO: specify
    if(!(is_small() && rhs.is_small())) {
      BitVec result(_width);
      Large &out = result.large_ref();
      for(std::size_t i = 0; i < _width; ++i) {
        bool bit = !(_bits()[i] | rhs._bits()[i]);
        out[i] = bit;
        result._bits()[i] = bit;
      }
      return result;
    }
    Small val = trim(~(as_small() | rhs.as_small()), _width);
    BitVec result(_width);
    result._storage = val;
    return result;
  }

  BitVec BitVec::xnor(const BitVec &rhs) const {
    // TODO: specify
    if(!(is_small() && rhs.is_small())) {
      BitVec result(_width);
      Large &out = result.large_ref();
      for(std::size_t i = 0; i < _width; ++i) {
        bool bit = !(_bits()[i] ^ rhs._bits()[i]);
        out[i] = bit;
        result._bits()[i] = bit;
      }
      return result;
    }
    Small val = trim(~(as_small() ^ rhs.as_small()), _width);
    BitVec result(_width);
    result._storage = val;
    return result;
  }

  bool BitVec::redand() const {
    // TODO: specify
    if(!is_small()) {
      for(bool b: _bits()) {
        if(!b) { return false; }
      }
      return true;
    }
    Small v = trim(as_small(), _width);
    return v == mask(_width);
  }

  bool BitVec::redor() const {
    if(!is_small()) {
      for(bool b: _bits()) {
        if(b) { return true; };
      }
      return false;
    }
    Small v = trim(as_small(), _width);
    return v != 0;
  }

  BitVec BitVec::neg() const {
    //$ ensures return._width == this._width
    // TODO: specify
    if(!is_small()) {
      BitVec result(_width);
      Large &out = result.large_ref();
      bool carry = true; // add one after bitwise not
      for(std::size_t i = 0; i < _width; ++i) {
        bool bit = !_bits()[i];
        bool sum = bit ^ carry;
        carry = bit & carry;
        out[i] = sum;
        result._bits()[i] = sum;
      }
      return result;
    }
    Small val = trim(-as_small(), _width);
    BitVec result(_width);
    result._storage = val;
    return result;
  }

  BitVec BitVec::add(const BitVec &rhs) const {
    //$ requires rhs._width == this._width
    //$ ensures return._width == this._width
    // TODO: specify
    _ensure_same_width(rhs, "add");
    if(!(is_small() && rhs.is_small())) {
      BitVec result(_width);
      Large &out = result.large_ref();
      bool carry = false;
      for(std::size_t i = 0; i < _width; ++i) {
        const bool a = _bits()[i], b = rhs._bits()[i];
        bool sum = (a ^ b) ^ carry;
        carry = (a & b) | (a & carry) | (b & carry);
        out[i] = sum;
        result._bits()[i] = sum;
      }
      return result;
    }
    Small val = trim(as_small() + rhs.as_small(), _width);
    BitVec result(_width);
    result._storage = val;
    return result;
  }

  BitVec BitVec::sub(const BitVec &rhs) const {
    //$ requires rhs._width == this._width
    //$ ensures return._width == this._width
    // TODO: specify
    _ensure_same_width(rhs, "sub");
    if(!(is_small() && rhs.is_small())) {
      BitVec result(_width);
      Large &out = result.large_ref();
      bool borrow = false;
      for(std::size_t i = 0; i < _width; ++i) {
        const bool a = _bits()[i], b = rhs._bits()[i];
        bool diff = (a ^ b) ^ borrow;
        borrow = (!a & b) | ((!(a) | b) & borrow);
        out[i] = diff;
        result._bits()[i] = diff;
      }
      return result;
    }
    Small val = trim(as_small() - rhs.as_small(), _width);
    BitVec result(_width);
    result._storage = val;
    return result;
  }

  BitVec BitVec::mul(const BitVec &rhs) const {
    // TODO: specify
    _ensure_same_width(rhs, "mul");
    const std::size_t w = this->_width;
    if(is_small() && rhs.is_small()) {
      unsigned __int128 prod = static_cast<unsigned __int128>(as_small()) * rhs.as_small();
      Small val = trim(static_cast<Small>(prod), w);
      BitVec out(w);
      out._storage = val;
      return out;
    }
    // Compute full 2w-bit product, return low w bits.
    std::vector<bool> full(2 * w, false);
    _mul(full, _bits(), rhs._bits());
    BitVec out(w);
    for(std::size_t i = 0; i < w; ++i) { out._bits()[i] = full[i]; }
    if(out.is_small()) {
      Small val = 0;
      out._storage = trim(val, w);
    }
    return out;
  }

  BitVec BitVec::udiv(const BitVec &rhs) const {
    // TODO: specify
    _ensure_same_width(rhs, "udiv");
    const std::size_t w = _width;
    if(is_small() && rhs.is_small()) {
      Small b = rhs.as_small();
      if(b == 0) {
        BitVec out(w);
        Small val = mask(w);
        out._storage = val;
        for(std::size_t i = 0; i < w; ++i) { out._bits()[i] = true; }
        return out;
      }
      Small q = trim(as_small() / b, w);
      BitVec out(w);
      out._storage = q;
      return out;
    }
    if(rhs.is_zero()) { return BitVec::ones(w); }
    std::vector<bool> q(w, false), r; // remainder dynamic
    _udivrem_bits(_bits(), rhs._bits(), q, r);
    BitVec out(w);
    out._bits() = std::move(q);
    if(out.is_small()) {
      Small val = 0;
      out._storage = trim(val, w);
    }
    return out;
  }

  BitVec BitVec::urem(const BitVec &rhs) const {
    // TODO: specify
    _ensure_same_width(rhs, "urem");
    const std::size_t w = _width;
    if(is_small() && rhs.is_small()) {
      Small b = rhs.as_small();
      if(b == 0) return *this;
      Small r = trim(as_small() % b, w);
      BitVec out(w);
      out._storage = r;
      return out;
    }
    if(rhs.is_zero()) return *this;
    std::vector<bool> q(w, false), r;
    _udivrem_bits(_bits(), rhs._bits(), q, r);
    BitVec out(w);
    // copy low w bits of r
    for(std::size_t i = 0; i < w && i < r.size(); ++i) { out._bits()[i] = r[i]; }
    if(out.is_small()) {
      Small val = 0;
      out._storage = trim(val, w);
    }
    return out;
  }

  BitVec BitVec::sdiv(const BitVec &rhs) const {
    // TODO: specify
    _ensure_same_width(rhs, "sdiv");
    const std::size_t w = _width;
    if(is_small() && rhs.is_small()) {
      if(w == 0) return BitVec(0);
      Small b = rhs.as_small();
      if(b == 0) {
        BitVec out(w);
        Small val = mask(w);
        out._storage = val;
        return out;
      }
      Small signBit = Small{1} << (w - 1);
      Small a = as_small();
      if(a == signBit && b == mask(w)) { return *this; }
      bool negA = (a & signBit) != 0;
      bool negB = (b & signBit) != 0;
      Small aMag = negA ? trim(~a + 1, w) : a;
      Small bMag = negB ? trim(~b + 1, w) : b;
      Small q = aMag / bMag;
      q = trim(q, w);
      if(negA ^ negB) { q = trim(~q + 1, w); }
      BitVec out(w);
      out._storage = q;
      return out;
    }
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
    _ensure_same_width(rhs, "srem");
    const std::size_t w = _width;
    if(is_small() && rhs.is_small()) {
      if(w == 0) return BitVec(0);
      Small b = rhs.as_small();
      if(b == 0) { return *this; }
      Small signBit = Small{1} << (w - 1);
      Small a = as_small();
      if(a == signBit && b == mask(w)) { return BitVec::zeros(w); }
      bool negA = (a & signBit) != 0;
      bool negB = (b & signBit) != 0;
      Small aMag = negA ? trim(~a + 1, w) : a;
      Small bMag = negB ? trim(~b + 1, w) : b;
      Small r = aMag % bMag;
      r = trim(r, w);
      if(negA) { r = trim(~r + 1, w); }
      BitVec out(w);
      out._storage = r;
      return out;
    }
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
    _ensure_same_width(rhs, "smod");
    const std::size_t w = _width;
    if(is_small() && rhs.is_small()) {
      if(w == 0) return BitVec(0);
      Small b = rhs.as_small();
      if(b == 0) { return *this; }
      Small signBit = Small{1} << (w - 1);
      Small a = as_small();
      if(a == signBit && b == mask(w)) return BitVec(w);
      bool negA = (a & signBit) != 0;
      bool negB = (b & signBit) != 0;
      Small aMag = negA ? trim(~a + 1, w) : a;
      Small bMag = negB ? trim(~b + 1, w) : b;
      Small r = aMag % bMag;
      r = trim(r, w);
      if(r == 0) { return BitVec::zeros(w); }
      if(negA != negB) { r = trim(bMag - r, w); }
      Small resVal = negB ? trim(~r + 1, w) : r;
      BitVec out(w);
      out._storage = resVal;
      return out;
    }
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
    _ensure_same_width(rhs, "shl");
    const std::size_t w = _width;
    if(is_small() && rhs.is_small()) {
      auto amt = static_cast<std::size_t>(rhs.as_small());
      if(amt >= w) { return BitVec::zeros(w); }
      Small val = trim(as_small() << amt, w);
      BitVec result(w);
      result._storage = val;
      return result;
    }
    bool ge = _rhs_amount_ge_width(rhs, w);
    if(ge) { return BitVec::zeros(w); }
    std::size_t amt = _rhs_amount_mod(rhs, w);
    BitVec result(w);
    Large &out = result.large_ref();
    const Large &lhs = large_ref();
    for(std::size_t i = w; i-- > 0;) {
      if(i >= amt) {
        bool bit = lhs[i - amt];
        out[i] = bit;
        result._bits()[i] = bit;
      }
    }
    return result;
  }

  BitVec BitVec::lshr(const BitVec &rhs) const {
    // TODO: specify
    _ensure_same_width(rhs, "lshr");
    const std::size_t w = _width;
    if(is_small() && rhs.is_small()) {
      auto amt = static_cast<std::size_t>(rhs.as_small());
      if(amt >= w) { return BitVec::zeros(w); }
      Small val = as_small() >> amt;
      val = trim(val, w);
      BitVec result(w);
      result._storage = val;
      return result;
    }
    bool ge = _rhs_amount_ge_width(rhs, w);
    if(ge) { return BitVec::zeros(w); }
    std::size_t amt = _rhs_amount_mod(rhs, w);
    BitVec result(w);
    Large &out = result.large_ref();
    const Large &lhs = large_ref();
    for(std::size_t i = 0; i < w; ++i) {
      const std::size_t src = i + amt;
      if(src < w) {
        bool bit = lhs[src];
        out[i] = bit;
        result._bits()[i] = bit;
      }
    }
    return result;
  }

  BitVec BitVec::ashr(const BitVec &rhs) const {
    // TODO: specify
    _ensure_same_width(rhs, "ashr");
    const std::size_t w = _width;
    const bool sign = is_negative();
    if(is_small() && rhs.is_small()) {
      auto amt = static_cast<std::size_t>(rhs.as_small());
      if(amt >= w) { return sign ? BitVec::ones(w) : BitVec::zeros(w); }
      Small val = as_small();
      if(sign) { val |= ~mask(w); }
      auto shifted = static_cast<Small>(static_cast<std::int64_t>(val) >> amt);
      shifted = trim(shifted, w);
      BitVec result(w);
      result._storage = shifted;
      return result;
    }
    bool ge = _rhs_amount_ge_width(rhs, w);
    if(ge) { return sign ? BitVec::ones(w) : BitVec::zeros(w); }
    std::size_t amt = _rhs_amount_mod(rhs, w);
    BitVec result(w);
    Large &out = result.large_ref();
    const Large &lhs = large_ref();
    for(std::size_t i = 0; i < w; ++i) {
      const std::size_t src = i + amt;
      bool bit = (src < w) ? lhs[src] : sign;
      out[i] = bit;
      result._bits()[i] = bit;
    }
    return result;
  }

  bool BitVec::ult(const BitVec &rhs) const {
    // TODO: specify
    _ensure_same_width(rhs, "ult");
    if(is_small() && rhs.is_small()) {
      Small lhs = trim(as_small(), _width);
      Small rhv = trim(rhs.as_small(), _width);
      return lhs < rhv;
    }
    return _compare_unsigned(*this, rhs) < 0;
  }

  bool BitVec::ule(const BitVec &rhs) const {
    // TODO: specify
    _ensure_same_width(rhs, "ule");
    if(is_small() && rhs.is_small()) {
      Small lhs = trim(as_small(), _width);
      Small rhv = trim(rhs.as_small(), _width);
      return lhs <= rhv;
    }
    return _compare_unsigned(*this, rhs) <= 0;
  }

  bool BitVec::uge(const BitVec &rhs) const {
    // TODO: specify
    _ensure_same_width(rhs, "uge");
    if(is_small() && rhs.is_small()) {
      Small lhs = trim(as_small(), _width);
      Small rhv = trim(rhs.as_small(), _width);
      return lhs >= rhv;
    }
    return _compare_unsigned(*this, rhs) >= 0;
  }

  bool BitVec::ugt(const BitVec &rhs) const {
    // TODO: specify
    _ensure_same_width(rhs, "ugt");
    if(is_small() && rhs.is_small()) {
      Small lhs = trim(as_small(), _width);
      Small rhv = trim(rhs.as_small(), _width);
      return lhs > rhv;
    }
    return _compare_unsigned(*this, rhs) > 0;
  }

  bool BitVec::eq(const BitVec &rhs) const { return this->equals(rhs); }

  bool BitVec::equals(const BitVec &rhs) const {
    if(is_small() && rhs.is_small()) {
      Small lhs = trim(as_small(), _width);
      Small rhv = trim(rhs.as_small(), _width);
      return lhs == rhv;
    }
    return large_ref() == rhs.large_ref();
  }

  bool BitVec::slt(const BitVec &rhs) const {
    // TODO: specify
    _ensure_same_width(rhs, "slt");
    if(is_small() && rhs.is_small()) {
      if(_width == 0) return false;
      Small lhs = trim(as_small(), _width);
      Small rhv = trim(rhs.as_small(), _width);
      Small sign = Small{1} << (_width - 1);
      bool sa = (lhs & sign) != 0;
      bool sb = (rhv & sign) != 0;
      if(sa != sb) { return sa; }
      return lhs < rhv;
    }
    const bool sa = is_negative(), sb = rhs.is_negative();
    if(sa != sb) { return sa; }
    int cu = _compare_unsigned(*this, rhs);
    return cu < 0;
  }

  bool BitVec::sle(const BitVec &rhs) const {
    // TODO: specify
    _ensure_same_width(rhs, "sle");
    if(is_small() && rhs.is_small()) {
      if(_width == 0) return true;
      Small lhs = trim(as_small(), _width);
      Small rhv = trim(rhs.as_small(), _width);
      Small sign = Small{1} << (_width - 1);
      bool sa = (lhs & sign) != 0;
      bool sb = (rhv & sign) != 0;
      if(sa != sb) { return sa; }
      return lhs <= rhv;
    }
    const bool sa = is_negative(), sb = rhs.is_negative();
    if(sa != sb) { return sa; }
    int cu = _compare_unsigned(*this, rhs);
    return cu <= 0;
  }

  bool BitVec::sge(const BitVec &rhs) const {
    // TODO: specify
    _ensure_same_width(rhs, "sge");
    if(is_small() && rhs.is_small()) {
      if(_width == 0) return true;
      Small lhs = trim(as_small(), _width);
      Small rhv = trim(rhs.as_small(), _width);
      Small sign = Small{1} << (_width - 1);
      bool sa = (lhs & sign) != 0;
      bool sb = (rhv & sign) != 0;
      if(sa != sb) { return !sa; }
      return lhs >= rhv;
    }
    const bool sa = is_negative(), sb = rhs.is_negative();
    if(sa != sb) { return !sa; }
    int cu = _compare_unsigned(*this, rhs);
    return cu >= 0;
  }

  bool BitVec::sgt(const BitVec &rhs) const {
    // TODO: specify
    _ensure_same_width(rhs, "sgt");
    if(is_small() && rhs.is_small()) {
      if(_width == 0) return false;
      Small lhs = trim(as_small(), _width);
      Small rhv = trim(rhs.as_small(), _width);
      Small sign = Small{1} << (_width - 1);
      bool sa = (lhs & sign) != 0;
      bool sb = (rhv & sign) != 0;
      if(sa != sb) { return !sa; }
      return lhs > rhv;
    }
    const bool sa = is_negative(), sb = rhs.is_negative();
    if(sa != sb) return !sa;
    int cu = _compare_unsigned(*this, rhs);
    return cu > 0;
  }

  BitVec BitVec::comp(const BitVec &rhs) const { return {equals(rhs), 1}; }

  bool BitVec::nego() const {
    if(is_small()) {
      if(_width == 0) return false;
      Small v = as_small();
      Small mn = Small{1} << (_width - 1);
      return v == mn;
    }
    return is_most_negative();
  }

  bool BitVec::uaddo(const BitVec &rhs) const {
    // TODO: specify
    _ensure_same_width(rhs, "uaddo");
    if(is_small() && rhs.is_small()) {
      Small lhs = as_small();
      Small rhv = rhs.as_small();
      Small sum = lhs + rhv;
      bool overflow = _width < 64 ? (sum >> _width) != 0 : sum < lhs;
      return overflow;
    }
    bool carry = false;
    for(std::size_t i = 0; i < _width; ++i) {
      const bool a = _bits()[i], b = rhs._bits()[i];
      carry = (a & b) | (a & carry) | (b & carry);
    }
    return carry;
  }

  bool BitVec::saddo(const BitVec &rhs) const {
    // TODO: specify
    _ensure_same_width(rhs, "saddo");
    if(_width == 0) return false;
    if(is_small() && rhs.is_small()) {
      Small lhs = as_small();
      Small rhv = rhs.as_small();
      Small sum = trim(lhs + rhv, _width);
      bool sa = (lhs >> (_width - 1)) & 1u;
      bool sb = (rhv >> (_width - 1)) & 1u;
      bool ss = (sum >> (_width - 1)) & 1u;
      return (sa == sb) && (ss != sa);
    }
    BitVec sum = add(rhs);
    const bool sa = is_negative();
    const bool sb = rhs.is_negative();
    const bool ss = sum.is_negative();
    return (sa == sb) && (ss != sa);
  }

  bool BitVec::umulo(const BitVec &rhs) const {
    // TODO: specify
    _ensure_same_width(rhs, "umulo");
    if(is_small() && rhs.is_small()) {
      unsigned __int128 prod = static_cast<unsigned __int128>(as_small()) * rhs.as_small();
      return (prod >> _width) != 0;
    }
    const std::size_t w = this->_width;
    std::vector<bool> full(2 * w, false);
    _mul(full, _bits(), rhs._bits());
    // Check high w bits for any 1.
    for(std::size_t i = w; i < 2 * w; ++i) {
      if(full[i]) { return true; }
    }
    return false;
  }

  bool BitVec::smulo(const BitVec &rhs) const {
    // TODO: specify
    _ensure_same_width(rhs, "smulo");
    const std::size_t w = _width;
    if(w == 0) return false;
    if(is_small() && rhs.is_small()) {
      auto sx = [w](Small v) -> std::int64_t {
        return static_cast<std::int64_t>(static_cast<std::int64_t>(v << (64 - w)) >> (64 - w));
      };
      std::int64_t a = sx(as_small());
      std::int64_t b = sx(rhs.as_small());
      __int128 prod = static_cast<__int128>(a) * static_cast<__int128>(b);
      __int128 min = -(static_cast<__int128>(1) << (w - 1));
      __int128 max = (static_cast<__int128>(1) << (w - 1)) - 1;
      return prod < min || prod > max;
    }
    // Sign-extend both to 2w and multiply (unsigned), then check that the
    // upper w bits are a sign-extension of the sign bit of the low part.
    std::vector<bool> a2(2 * w, false), b2(2 * w, false);
    const bool sa = is_negative(), sb = rhs.is_negative();
    // copy low
    for(std::size_t i = 0; i < w; ++i) {
      a2[i] = _bits()[i];
      b2[i] = rhs._bits()[i];
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
    _ensure_same_width(rhs, "usubo");
    if(is_small() && rhs.is_small()) { return as_small() < rhs.as_small(); }
    return ult(rhs);
  }

  bool BitVec::ssubo(const BitVec &rhs) const {
    // TODO: specify
    _ensure_same_width(rhs, "ssubo");
    if(_width == 0) return false;
    if(is_small() && rhs.is_small()) {
      Small lhs = as_small();
      Small rhv = rhs.as_small();
      Small diff = trim(lhs - rhv, _width);
      bool sa = (lhs >> (_width - 1)) & 1u;
      bool sb = (rhv >> (_width - 1)) & 1u;
      bool sd = (diff >> (_width - 1)) & 1u;
      return (sa != sb) && (sd != sa);
    }
    BitVec diff = sub(rhs);
    const bool sa = is_negative();
    const bool sb = rhs.is_negative();
    const bool sd = diff.is_negative();
    return (sa != sb) && (sd != sa);
  }

  bool BitVec::sdivo(const BitVec &rhs) const {
    // TODO: specify
    _ensure_same_width(rhs, "sdivo");
    if(is_small() && rhs.is_small()) {
      if(_width == 0) return false;
      Small a = as_small();
      Small b = rhs.as_small();
      Small mn = Small{1} << (_width - 1);
      return a == mn && b == mask(_width);
    }
    return is_most_negative() && rhs.is_all_ones();
  }

  std::string BitVec::u_to_int() const {
    // TODO: specify
    // Build decimal by scanning from MSB to LSB: s = s*2 + bit
    std::string s = "0";
    int msb = _msb_index(_bits());
    if(msb < 0) { return "0"; }
    for(int i = msb; i >= 0; --i) {
      _dec_mul_add(s, 2, 0);
      if(_bits()[static_cast<std::size_t>(i)]) {
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
    const std::size_t w = a._width;
    for(std::size_t i = 0; i < w; ++i) {
      // scan from MSB to LSB
      std::size_t idx = w - 1 - i;
      const bool abit = a._bits()[idx], bbit = b._bits()[idx];
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
      const bool ai = (i < a.size()) && a[i];
      const bool bi = (i < b.size()) && b[i];
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
    } else if(m + 1 < v.size()) {
      v.resize(m + 1);
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
    for(int i = _msb_index(amt._bits()); i >= 0; --i) {
      r = (r * 2) % mod;
      if(amt._bits()[static_cast<std::size_t>(i)]) { r = (r + 1) % mod; }
    }
    return r;
  }

  bool BitVec::_rhs_amount_ge_width(const BitVec &amt, std::size_t w) {
    if(w == 0) {
      return true; // any amount >= 0 when width==0
    }
    int ma = _msb_index(amt._bits());
    if(ma < 0) { return false; }
    int mw = 0;
    for(std::size_t tmp = w >> 1; tmp > 0; tmp >>= 1) { ++mw; }
    if(ma > mw) { return true; }
    if(ma < mw) { return false; }
    for(int i = mw; i >= 0; --i) {
      const bool abit = amt._bits()[static_cast<std::size_t>(i)];
      const bool wbit = ((w >> i) & 1u) != 0;
      if(abit != wbit) return abit; // true if amt bit is 1 when w bit 0
    }
    return true; // equal
  }

  constexpr BitVec::Small BitVec::mask(std::size_t w) noexcept {
    return w >= 64 ? ~Small{0} : (std::rotl(Small{1}, static_cast<int>(w)) - 1);
  }

  constexpr BitVec::Small BitVec::trim(Small v, std::size_t w) noexcept { return v & mask(w); }

  constexpr bool BitVec::is_small() const noexcept { return _width <= 64; }

  constexpr BitVec::Small BitVec::as_small() const noexcept { return std::get<Small>(_storage); }

  constexpr BitVec::Large &BitVec::large_ref() noexcept { return std::get<Large>(_storage); }

  constexpr const BitVec::Large &BitVec::large_ref() const noexcept { return std::get<Large>(_storage); }

  std::vector<bool> &BitVec::_bits() const {
    if(is_small()) {
      if(!_cached_bits) {
        Large tmp(_width);
        Small value = as_small();
        for(std::size_t i = 0; i < _width && i < 64; ++i) { tmp[i] = (value >> i) & Small{1}; }
        _cached_bits = std::move(tmp);
      }
      return *_cached_bits;
    }
    return std::get<Large>(_storage);
  }

  void BitVec::_ensure_same_width(const btgly::BitVec &rhs, const char *op) const {
    if(_width != rhs._width) { throw std::invalid_argument(std::string(op) + ": width mismatch"); }
  }

} // namespace btgly
