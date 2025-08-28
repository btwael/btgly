//
// Created by Wael-Amine Boutglay on 26/08/2025.
//

#pragma once

#include <vector>
#include <string>
#include <optional>
#include <variant>
#include <cstdint>
#include <bit>
#include "btgly/codepoint.hh"
#include "btgly/radix.hh"

namespace btgly {

  //*-- BitVec

  /// Fixed-width bit-vector with SMT-LIB–style semantics.
  class BitVec {
  public:
    /// Create a zero-initialised bit-vector of the requested width.
    //$ ensures width() == width
    //$ ensures is_zero()
    explicit BitVec(std::size_t width);

    /// Create a bit-vector of the given width filled with \p value.
    //$ ensures width() == width
    //$ ensures is_all_ones() == value
    BitVec(bool value, std::size_t width);

    /// Return a zero-filled bit-vector of \p width bits.
    //$ ensures result.width() == width
    //$ ensures result.is_zero()
    static BitVec zeros(std::size_t width);

    /// Return an all-ones bit-vector of \p width bits.
    //$ ensures result.width() == width
    //$ ensures result.is_all_ones()
    static BitVec ones(std::size_t width);

    /// Construct a bit-vector of \p width from an integer string.
    /// The string is parsed as unsigned decimal unless prefixed with
    /// \c 0b / \c 0o / \c 0x for binary, octal or hexadecimal. A leading
    /// '+' or '-' toggles the sign. The value is truncated to the low
    /// \p width bits (i.e. taken modulo 2^width).
    //$ ensures result.width() == width
    //$ excepts invalid_argument if the string contains invalid digits
    static BitVec from_int(std::string s, std::size_t width);

    //*- properties

    /// View the bits in least-significant-bit first order.
    //$ ensures return.size() == width()
    //$ ensures forall i : Int :: 0 <= i < width() => return[i] == bit(i)
    const std::vector<bool> &bits() const;

    /// Number of bits in this vector.
    std::size_t width() const;

    /// True iff every bit equals one (width()==0 returns true).
    //$ ensures return == forall i : Int :: 0 <= i < width() => bit(i)
    bool is_all_ones() const;

    /// True iff every bit equals zero.
    bool is_zero() const;

    /// True iff the most-significant bit is one and width()>0.
    bool is_negative() const;

    /// True iff width()>0 and the value is 1000...0.
    bool is_most_negative() const;

    //*- methods

    /// Concatenate this bit-vector (high part) with \p rhs (low part).
    //$ requires true
    //$ ensures result.width() == width() + rhs.width()
    BitVec concat(const BitVec &rhs) const;

    /// Extract bits [i:j] (inclusive) with i >= j.
    //$ requires j <= i && i < width()
    //$ ensures result.width() == i - j + 1
    //$ excepts invalid_argument when i < j || i >= width()
    BitVec extract(std::size_t i, std::size_t j) const;

    /// Repeat this bit-vector k times by concatenation.
    //$ ensures result.width() == k * width()
    BitVec repeat(std::size_t k) const;

    /// Sign-extend by k bits (two's-complement).
    //$ ensures result.width() == width() + k
    BitVec sign_extend(std::size_t k) const;

    /// Zero-extend by k bits.
    //$ ensures result.width() == width() + k
    BitVec zero_extend(std::size_t k) const;

    /// Rotate left by \p k (mod \c width()).
    //$ ensures result.width() == width()
    BitVec rotate_left(std::size_t k) const;

    /// Rotate right by \p k (mod \c width()).
    //$ ensures result.width() == width()
    BitVec rotate_right(std::size_t k) const;

    /// Bitwise NOT.
    //$ ensures result.width() == width()
    //$ ensures forall i : Int :: 0 <= i < width() =>
    //$   result.bit(i) == !bit(i)
    BitVec $not() const;

    /// Bitwise AND.
    //$ requires rhs.width() == width()
    //$ ensures result.width() == width()
    //$ ensures forall i : Int :: 0 <= i < width() =>
    //$   result.bit(i) == (bit(i) && rhs.bit(i))
    BitVec $and(const BitVec &rhs) const;

    /// Bitwise OR.
    //$ requires rhs.width() == width()
    //$ ensures result.width() == width()
    //$ ensures forall i : Int :: 0 <= i < width() =>
    //$   result.bit(i) == (bit(i) || rhs.bit(i))
    BitVec $or(const BitVec &rhs) const;

    /// Bitwise XOR.
    //$ requires rhs.width() == width()
    //$ ensures result.width() == width()
    //$ ensures forall i : Int :: 0 <= i < width() =>
    //$   result.bit(i) == (bit(i) ^ rhs.bit(i))
    BitVec $xor(const BitVec &rhs) const;

    /// Bitwise NAND: NOT(AND).
    //$ requires rhs.width() == width()
    //$ ensures result.width() == width()
    BitVec nand(const BitVec &rhs) const;

    /// Bitwise NOR: NOT(OR).
    //$ requires rhs.width() == width()
    //$ ensures result.width() == width()
    BitVec nor(const BitVec &rhs) const;

    /// Bitwise XNOR: NOT(XOR).
    //$ requires rhs.width() == width()
    //$ ensures result.width() == width()
    BitVec xnor(const BitVec &rhs) const;

    /// Reduction AND.
    //$ ensures return == forall i : Int :: 0 <= i < width() => bit(i)
    bool redand() const;

    /// Reduction OR.
    //$ ensures return == exists i : Int :: 0 <= i < width() && bit(i)
    bool redor() const;

    /// Two's-complement negation (modular).
    //$ ensures result.width() == width()
    BitVec neg() const;

    /// Modular addition.
    //$ requires rhs.width() == width()
    //$ ensures result.width() == width()
    BitVec add(const BitVec &rhs) const;

    /// Modular subtraction.
    //$ requires rhs.width() == width()
    //$ ensures result.width() == width()
    BitVec sub(const BitVec &rhs) const;

    /// Modular multiplication.
    //$ requires rhs.width() == width()
    //$ ensures result.width() == width()
    BitVec mul(const BitVec &rhs) const;

    /// Unsigned division (SMT-LIB bvudiv). Div/0 -> all ones.
    //$ requires rhs.width() == width()
    //$ ensures result.width() == width()
    BitVec udiv(const BitVec &rhs) const;

    /// Unsigned remainder (bvurem). Div/0 -> lhs.
    //$ requires rhs.width() == width()
    //$ ensures result.width() == width()
    BitVec urem(const BitVec &rhs) const;

    /// Signed division (bvsdiv). Div/0 -> -1. Overflow -> min.
    //$ requires rhs.width() == width()
    //$ ensures result.width() == width()
    BitVec sdiv(const BitVec &rhs) const;

    /// Signed remainder (bvsrem). Div/0 -> lhs.
    //$ requires rhs.width() == width()
    //$ ensures result.width() == width()
    BitVec srem(const BitVec &rhs) const;

    /// Signed modulo (bvsmod). Div/0 -> lhs.
    //$ requires rhs.width() == width()
    //$ ensures result.width() == width()
    BitVec smod(const BitVec &rhs) const;

    /// Logical left shift by an unsigned amount in \p rhs.
    //$ requires rhs.width() == width() || width() == 0
    //$ ensures result.width() == width()
    BitVec shl(const BitVec &rhs) const;

    /// Logical right shift by an unsigned amount in \p rhs.
    //$ requires rhs.width() == width() || width() == 0
    //$ ensures result.width() == width()
    BitVec lshr(const BitVec &rhs) const;

    /// Arithmetic right shift by an unsigned amount in \p rhs.
    //$ requires rhs.width() == width() || width() == 0
    //$ ensures result.width() == width()
    BitVec ashr(const BitVec &rhs) const;

    /// Unsigned comparison: *this < rhs.
    //$ requires rhs.width() == width()
    bool ult(const BitVec &rhs) const;

    /// Unsigned comparison: *this <= rhs.
    //$ requires rhs.width() == width()
    bool ule(const BitVec &rhs) const;

    /// Unsigned comparison: *this >= rhs.
    //$ requires rhs.width() == width()
    bool uge(const BitVec &rhs) const;

    /// Unsigned comparison: *this > rhs.
    //$ requires rhs.width() == width()
    bool ugt(const BitVec &rhs) const;

    /// Equality check.
    //$ requires rhs.width() == width()
    bool eq(const BitVec &rhs) const;

    /// Equality check (alias).
    //$ requires rhs.width() == width()
    bool equals(const BitVec &rhs) const;

    /// Signed comparison: *this < rhs.
    //$ requires rhs.width() == width()
    bool slt(const BitVec &rhs) const;

    /// Signed comparison: *this <= rhs.
    //$ requires rhs.width() == width()
    bool sle(const BitVec &rhs) const;

    /// Signed comparison: *this >= rhs.
    //$ requires rhs.width() == width()
    bool sge(const BitVec &rhs) const;

    /// Signed comparison: *this > rhs.
    //$ requires rhs.width() == width()
    bool sgt(const BitVec &rhs) const;

    /// Bit-vector compare (SMT-LIB bvcomp).
    //$ requires rhs.width() == width()
    //$ ensures result.width() == 1
    BitVec comp(const BitVec &rhs) const;

    /// Negation overflow predicate.
    //$ ensures return == is_most_negative()
    bool nego() const;

    /// Unsigned addition overflow.
    //$ requires rhs.width() == width()
    bool uaddo(const BitVec &rhs) const;

    /// Signed addition overflow.
    //$ requires rhs.width() == width()
    bool saddo(const BitVec &rhs) const;

    /// Unsigned multiplication overflow.
    //$ requires rhs.width() == width()
    bool umulo(const BitVec &rhs) const;

    /// Signed multiplication overflow.
    //$ requires rhs.width() == width()
    bool smulo(const BitVec &rhs) const;

    /// Unsigned subtraction overflow (borrow).
    //$ requires rhs.width() == width()
    bool usubo(const BitVec &rhs) const;

    /// Signed subtraction overflow.
    //$ requires rhs.width() == width()
    bool ssubo(const BitVec &rhs) const;

    /// Signed division overflow.
    //$ requires rhs.width() == width()
    bool sdivo(const BitVec &rhs) const;

    /// Return the unsigned decimal string representation.
    //$ ensures return.size() > 0
    std::string u_to_int() const;

    /// Return the signed decimal string representation.
    //$ ensures return.size() > 0
    std::string s_to_int() const;

  private:
    /// Number of significant bits in the vector.
    std::size_t _width{0};

    /// Inline representation for vectors of width <= 64 bits.
    using Small = std::uint64_t;
    /// Dynamic representation for wider vectors, stored LSB-first.
    using Large = std::vector<bool>;

    /// Storage variant holding either a Small or Large representation.
    mutable std::variant<Small, Large> _storage;
    /// Cached view of bits for Small values.
    mutable std::optional<Large> _cached_bits;

    /// Mask with the low \p w bits set.
    static constexpr Small mask(std::size_t w) noexcept;
    /// Trim a Small value to width \p w.
    static constexpr Small trim(Small v, std::size_t w) noexcept;
    /// True if the value fits in the Small representation.
    constexpr bool is_small() const noexcept;
    /// Access the Small value (only valid if is_small()).
    constexpr Small as_small() const noexcept;
    /// Mutable reference to the Large representation.
    constexpr Large &large_ref() noexcept;
    /// Const reference to the Large representation.
    constexpr const Large &large_ref() const noexcept;

    /// Return true if decimal string \p s represents zero.
    static bool _is_decimal_zero(const std::string &s);

    /// Divide decimal string \p s by two, returning the remainder bit.
    static int _div_decimal_by_2(std::string &s);

    /// Remove leading zeros from decimal string \p s.
    static void _trim_leading_zeros(std::string &s);

    /// Multiply \p a and \p b (LSB-first) and accumulate into \p acc.
    static void _mul(std::vector<bool> &acc, const std::vector<bool> &a, const std::vector<bool> &b);

    /// Unsigned lexicographic comparison.
    static int _compare_unsigned(const BitVec &a, const BitVec &b);

    /// Unsigned division: compute quotient \p q and remainder \p r.
    static void _udivrem_bits(const std::vector<bool> &num, const std::vector<bool> &den, std::vector<bool> &q,
                              std::vector<bool> &r);

    /// Compare two arbitrary-length vectors (unsigned).
    static int _cmp_arb_unsigned(const std::vector<bool> &a, const std::vector<bool> &b);

    /// In-place subtraction of \p b from \p a assuming a >= b.
    static void _sub_arb_unsigned_in_place(std::vector<bool> &a, const std::vector<bool> &b);

    /// Drop leading zero bits from \p v.
    static void _trim_bits(std::vector<bool> &v);

    /// Index of most significant set bit or -1 if none.
    static int _msb_index(const std::vector<bool> &v);

    /// Decimal helper: s = s * mul + add.
    static void _dec_mul_add(std::string &s, int mul, int add);

    /// Reduce \p amt modulo \p mod.
    static std::size_t _rhs_amount_mod(const BitVec &amt, std::size_t mod);

    /// Return true if \p amt >= width \p w.
    static bool _rhs_amount_ge_width(const BitVec &amt, std::size_t w);

    /// Materialise bits in LSB-first order.
    std::vector<bool> &_bits() const;

    /// Throw if widths differ in operation \p op.
    void _ensure_same_width(const BitVec &rhs, const char *op) const;
  };

} // namespace btgly
