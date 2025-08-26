//===- kind.hh - Runtime Kind Hierarchy Support ----------------*- C++ -*-===//
//
// Created by Wael-Amine Boutglay
//
// This file declares a simple `Kind` class template that can be used to build
// runtime type hierarchies.
//
//===----------------------------------------------------------------------===//

#pragma once

#include <string>

namespace btgly {

  //*-- Kind<T>

  /// Kind implements a simple hierarchical classification that can be used to
  /// describe relationships between runtime entities.
  template<class T>
  class Kind {
  public:
    /// Construct a new `Kind` with the given name and optional parent kind.
    explicit Kind(const char *name, const Kind<T> *parent_kind = nullptr) : _name(name), _parent_kind(parent_kind) {}

    /// Return the name of this kind.
    const std::string &name() const { return _name; }

    /// Return the parent kind, or `nullptr` if this is a root kind.
    const Kind<T> *parent_kind() const { return _parent_kind; }

    /// Return true if this kind is exactly `other`.
    bool is(const Kind<T> &other) const { return this == &other; }

    /// Return true if this kind is a subkind of `other`.
    bool is_subkind_of(const Kind<T> &other) const {
      const Kind<T> *kind = this;
      while(kind != nullptr) {
        if(kind == &other) { return true; }
        kind = kind->_parent_kind;
      }
      return false;
    }

  private:
    std::string _name;           /// Name associated with this kind.
    const Kind<T> *_parent_kind; /// Parent kind or nullptr.
  };

} // namespace btgly
