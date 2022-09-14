#ifndef ADIAR_INTERNAL_DATA_TYPES_TUPLE_H
#define ADIAR_INTERNAL_DATA_TYPES_TUPLE_H

#include <functional>

#include <adiar/internal/data_types/uid.h>

namespace adiar {
  //////////////////////////////////////////////////////////////////////////////
  // Data structures
  struct tuple
  {
    ptr_t t1;
    ptr_t t2;
  };

  struct tuple_data : tuple
  {
    ptr_t data_low;
    ptr_t data_high;
  };

  //////////////////////////////////////////////////////////////////////////////
  // Ordered access
  inline ptr_t fst(const ptr_t t1, const ptr_t t2)
  {
    return std::min(t1, t2);
  }

  inline ptr_t fst(const tuple &t) { return fst(t.t1, t.t2); }

  inline ptr_t snd(const ptr_t t1, const ptr_t t2)
  {
    return std::max(t1, t2);
  }

  inline ptr_t snd(const tuple &t) { return snd(t.t1, t.t2); }

  //////////////////////////////////////////////////////////////////////////////
  // Priority queue functions
  struct tuple_label
  {
    static inline label_t label_of(const tuple &t)
    {
      return adiar::label_of(std::min(t.t1, t.t2));
    }
  };

  struct tuple_lt
  {
    bool operator()(const tuple &a, const tuple &b)
    {
      return a.t1 < b.t1 || (a.t1 == b.t1 && a.t2 < b.t2);
    }
  };

  struct tuple_fst_lt
  {
    bool operator()(const tuple &a, const tuple &b)
    {
      // Sort primarily by the element to be encountered first
      return fst(a) < fst(b) ||
        // Group requests to the same tuple together by sorting on the coordinates
        (fst(a) == fst(b) && tuple_lt()(a,b));
    }
  };

  struct tuple_snd_lt
  {
    bool operator()(const tuple &a, const tuple &b)
    {
      // Sort primarily by the element to be encountered second
      return snd(a) < snd(b) ||
        // Group requests to the same tuple together by sorting on the coordinates
        (snd(a) == snd(b) && tuple_lt()(a,b));
    }
  };
}
#endif // ADIAR_INTERNAL_DATA_TYPES_TUPLE_H
