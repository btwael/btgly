//
// Created by Wael-Amine Boutglay on 05/06/2025.
//

#pragma once

#include <string>

namespace btgly {

  //*-- Kind
  template<class T>
  class Kind {
  public:
    explicit Kind(const char *name, const Kind<T> *parent_kind = nullptr) : _name(name), _parent_kind(parent_kind) {}

    const std::string &name() const { return _name; }

    const Kind<T> *parent_kind() const { return _parent_kind; }

    //*- methods

    bool is(const Kind<T> &other) const { return this == &other; }

    bool is_subkind_of(const Kind<T> &other) const {
      const Kind<T> *kind = this;
      while(kind != nullptr) {
        if(kind == &other) { return true; }
        kind = kind->_parent_kind;
      }
      return false;
    }

  private:
    std::string _name;
    const Kind<T> *_parent_kind;
  };

} // end namespace btgly
