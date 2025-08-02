//===- codepoint.hh - ASCII Code Point Utilities ----------------*- C++ -*-===//
//
// Created by Wael-Amine Boutglay
//
// This file defines the CodePoint class which provides numeric constants for
// ASCII characters and helper predicates for classifying individual code
// points.
//
//===----------------------------------------------------------------------===//

#pragma once

namespace btgly {

  /// CodePoint provides constants for ASCII characters and helper predicates
  /// for classifying code points.
  class CodePoint {
  public:
    static const int NUL = 0x0000;
    static const int SOH = 0x0001;          // start of heading
    static const int STX = 0x0002;          // start of text
    static const int ETX = 0x0003;          // end of text
    static const int EOT = 0x0004;          // end of transmission
    static const int ENQ = 0x0005;          // enquiry
    static const int ACK = 0x0006;          // acknowledgement
    static const int BEL = 0x0007;          // bell
    static const int BS = 0x0008;           // backspace ('\b')
    static const int HT = 0x0009;           // horizontal tab ('\t')
    static const int LF = 0x000a;           // line feed ('\n')
    static const int VT = 0x000b;           // vertical tab ('\v')
    static const int FF = 0x000c;           // form feed ('\f')
    static const int CR = 0x000d;           // carriage return ('\r')
    static const int SO = 0x000e;           // shift out
    static const int SI = 0x000f;           // shift in
    static const int DLE = 0x0010;          // data link escape
    static const int DC1 = 0x0011;          // device control 1
    static const int DC2 = 0x0012;          // device control 2
    static const int DC3 = 0x0013;          // device control 3
    static const int DC4 = 0x0014;          // device control 4
    static const int NAK = 0x0015;          // negative acknowledge
    static const int SYN = 0x0016;          // synchronous idle
    static const int ETB = 0x0017;          // end of trans. block
    static const int CAN = 0x0018;          // cancel
    static const int EM = 0x0019;           // end of medium
    static const int SUB = 0x001a;          // substitute
    static const int ESC = 0x001b;          // escape
    static const int FS = 0x001c;           // file separator
    static const int GS = 0x001d;           // group separator
    static const int RS = 0x001e;           // record separator
    static const int US = 0x001f;           // unit separator
    static const int SP = 0x0020;           // space (' ')
    static const int BANG = 0x0021;         // exclamation mark ('!')
    static const int DOUBLEQUOTE = 0x0022;  // double quote ('"')
    static const int HASH = 0x0023;         // hash ('#')
    static const int DOLLAR = 0x0024;       // dollar ('$')
    static const int PERCENT = 0x0025;      // percent ('%')
    static const int AMPERSAND = 0x0026;    // ampersand ('&')
    static const int SINGLEQUOTE = 0x0027;  // single quote ('\'')
    static const int LPAREN = 0x0028;       // left parenthesis ('(')
    static const int RPAREN = 0x0029;       // right parenthesis (')')
    static const int ASTERISK = 0x002a;     // asterisk ('*')
    static const int PLUS = 0x002b;         // plus ('+')
    static const int COMMA = 0x002c;        // comma (',')
    static const int MINUS = 0x002d;        // minus ('-')
    static const int DOT = 0x002e;          // dot ('.')
    static const int SLASH = 0x002f;        // slash ('/')
    static const int $0 = 0x0030;           // 0 ('0')
    static const int $1 = 0x0031;           // 1 ('1')
    static const int $2 = 0x0032;           // 2 ('2')
    static const int $3 = 0x0033;           // 3 ('3')
    static const int $4 = 0x0034;           // 4 ('4')
    static const int $5 = 0x0035;           // 5 ('5')
    static const int $6 = 0x0036;           // 6 ('6')
    static const int $7 = 0x0037;           // 7 ('7')
    static const int $8 = 0x0038;           // 8 ('8')
    static const int $9 = 0x0039;           // 9 ('9')
    static const int COLON = 0x003a;        // colon (':')
    static const int SEMICOLON = 0x003b;    // semicolon (';')
    static const int LESSTHAN = 0x003c;     // less than sign ('<')
    static const int EQUAL = 0x003d;        // equal sign ('=')
    static const int GREATERTHAN = 0x003e;  // greater than sign ('>')
    static const int QUESTIONMARK = 0x003f; // question mark ('?')
    static const int AT = 0x0040;           // at ('@')
    static const int $A = 0x0041;           // A ('A')
    static const int $B = 0x0042;           // B ('B')
    static const int $C = 0x0043;           // C ('C')
    static const int $D = 0x0044;           // D ('D')
    static const int $E = 0x0045;           // E ('E')
    static const int $F = 0x0046;           // F ('F')
    static const int $G = 0x0047;           // G ('G')
    static const int $H = 0x0048;           // H ('H')
    static const int $I = 0x0049;           // I ('I')
    static const int $J = 0x004a;           // J ('J')
    static const int $K = 0x004b;           // K ('K')
    static const int $L = 0x004c;           // L ('L')
    static const int $M = 0x004d;           // M ('M')
    static const int $N = 0x004e;           // N ('N')
    static const int $O = 0x004f;           // O ('O')
    static const int $P = 0x0050;           // P ('P')
    static const int $Q = 0x0051;           // Q ('Q')
    static const int $R = 0x0052;           // R ('R')
    static const int $S = 0x0053;           // S ('S')
    static const int $T = 0x0054;           // T ('T')
    static const int $U = 0x0055;           // U ('U')
    static const int $V = 0x0056;           // V ('V')
    static const int $W = 0x0057;           // W ('W')
    static const int $X = 0x0058;           // X ('X')
    static const int $Y = 0x0059;           // Y ('Y')
    static const int $Z = 0x005a;           // Z ('Z')
    static const int LBRACKET = 0x005b;     // left bracket ('[')
    static const int BACKSLASH = 0x005c;    // backslash ('\\')
    static const int RBRACKET = 0x005d;     // right bracket (']')
    static const int CARET = 0x005e;        // caret ('^')
    static const int UNDERSCORE = 0x005f;   // underscore ('_')
    static const int GRAVEACCENT = 0x0060;  // grave accent ('`')
    static const int $a = 0x0061;           // a ('a')
    static const int $b = 0x0062;           // b ('b')
    static const int $c = 0x0063;           // c ('c')
    static const int $d = 0x0064;           // d ('d')
    static const int $e = 0x0065;           // e ('e')
    static const int $f = 0x0066;           // f ('f')
    static const int $g = 0x0067;           // g ('g')
    static const int $h = 0x0068;           // h ('h')
    static const int $i = 0x0069;           // i ('i')
    static const int $j = 0x006a;           // j ('j')
    static const int $k = 0x006b;           // k ('k')
    static const int $l = 0x006c;           // l ('l')
    static const int $m = 0x006d;           // m ('m')
    static const int $n = 0x006e;           // n ('n')
    static const int $o = 0x006f;           // o ('o')
    static const int $p = 0x0070;           // p ('p')
    static const int $q = 0x0071;           // q ('q')
    static const int $r = 0x0072;           // r ('r')
    static const int $s = 0x0073;           // s ('s')
    static const int $t = 0x0074;           // t ('t')
    static const int $u = 0x0075;           // u ('u')
    static const int $v = 0x0076;           // v ('v')
    static const int $w = 0x0077;           // w ('w')
    static const int $x = 0x0078;           // x ('x')
    static const int $y = 0x0079;           // y ('y')
    static const int $z = 0x007a;           // z ('z')
    static const int LBRACE = 0x007b;       // left brace ('{')
    static const int BAR = 0x007c;          // vertical bar ('|')
    static const int RBRACE = 0x007d;       // right brace ('}')
    static const int TILDE = 0x007e;        // tilde ('~')

    /// Return true if `c` is either `0` or `1`.
    static bool isBinary(int c) { return $0 <= c && c <= $1; }

    /// Return true if `c` is an octal digit.
    static bool isOctal(int c) { return $0 <= c && c <= $7; }

    /// Return true if `c` is a decimal digit.
    static bool isDigit(int c) { return $0 <= c && c <= $9; }

    /// Return true if `c` is a hexadecimal digit.
    static bool isHexadecimal(int c) { return ($0 <= c && c <= $9) || ($A <= c && c <= $F) || ($a <= c && c <= $f); }

    /// Return true if `c` is an ASCII letter.
    static bool isLetter(int c) { return ($A <= c && c <= $Z) || ($a <= c && c <= $z); }

    /// Return true if `c` can start an identifier.
    static bool isNameStart(int c) { return isLetter(c); }

    /// Return true if `c` can appear after the first character of an
    /// identifier.
    static bool isNamePart(int c) { return isLetter(c) || isDigit(c) || c == UNDERSCORE; }
  };

} // namespace btgly
