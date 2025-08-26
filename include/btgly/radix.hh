//
// Created by Wael-Amine Boutglay on 26/08/2025.
//

#pragma once

#include <string>

namespace btgly {

  //*-- Radix
  enum class Radix { Binary, Octal, Decimal, Hexadecimal };

  constexpr int radix_base(Radix r) {
    switch(r) {
      case Radix::Binary:
        return 2;
      case Radix::Octal:
        return 8;
      case Radix::Decimal:
        return 10;
      case Radix::Hexadecimal:
        return 16;
    }
    return 10;
  }

  inline const std::string radix_prefix(Radix r) {
    switch(r) {
      case Radix::Binary:
        return "0b";
      case Radix::Octal:
        return "0o";
      case Radix::Decimal:
        return "";
      case Radix::Hexadecimal:
        return "0x";
    }
    return "";
  }

} // namespace btgly