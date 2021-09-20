#include "apply.h"

#include <adiar/file_stream.h>
#include <adiar/file_writer.h>
#include <adiar/tuple.h>

#include <adiar/internal/levelized_priority_queue.h>
#include <adiar/internal/product_construction.h>

#include <adiar/bdd/bdd.h>
#include <adiar/bdd/build.h>
#include <adiar/bdd/negate.h>

#include <adiar/assert.h>

namespace adiar
{
  //////////////////////////////////////////////////////////////////////////////
  // Apply policy for product construction.
  class apply_prod_policy : public bdd_policy, public prod_mixed_level_merger
  {
  public:
    static __bdd resolve_same_file(const bdd &bdd_1, const bdd &bdd_2,
                                   const bool_op &op)
    {
      ptr_t sink_1_F = create_sink_ptr(bdd_1.negate);
      ptr_t sink_2_F = create_sink_ptr(bdd_2.negate);

      // Compute the results on all children.
      ptr_t op_F = op(sink_1_F, sink_2_F);
      ptr_t op_T = op(negate(sink_1_F), negate(sink_2_F));

      // Does it collapse to a sink?
      if (op_F == op_T) {
        return bdd_sink(value_of(op_F));
      }

      return op_F == sink_1_F ? bdd_1 : ~bdd_1;
    }

  public:
    static __bdd resolve_sink_root(const node_t &v1, const bdd& bdd_1,
                                   const node_t &v2, const bdd& bdd_2,
                                   const bool_op &op)
    {
      if (is_sink(v1) && is_sink(v2)) {
        ptr_t p = op(v1.uid, v2.uid);
        return bdd_sink(value_of(p));
      } else if (is_sink(v1)) {
        if (can_left_shortcut(op, v1.uid)) {
          ptr_t p =  op(v1.uid, create_sink_ptr(false));
          return bdd_sink(value_of(p));
        } else if (is_left_irrelevant(op, v1.uid)) {
          return bdd_2;
        } else { // if (is_left_negating(op, v1.uid)) {
          return bdd_not(bdd_2);
        }
      } else { // if (is_sink(v2)) {
        if (can_right_shortcut(op, v2.uid)) {
          ptr_t p = op(create_sink_ptr(false), v2.uid);
          return bdd_sink(value_of(p));
        } else if (is_right_irrelevant(op, v2.uid)) {
          return bdd_1;
        } else { // if (is_right_negating(op, v2.uid)) {
          return bdd_not(bdd_1);
        }
      }
      adiar_unreachable();
    }

  private:
    static tuple __resolve_request(const bool_op &op, ptr_t r1, ptr_t r2)
    {
      if (is_sink(r1) && can_left_shortcut(op, r1)) {
        return { r1, create_sink_ptr(true) };
      } else if (is_sink(r2) && can_right_shortcut(op, r2)) {
        return { create_sink_ptr(true), r2 };
      } else {
        return { r1, r2 };
      }
    }

  public:
    static prod_rec resolve_request(const bool_op &op,
                                    ptr_t low1, ptr_t low2, ptr_t high1, ptr_t high2)
    {
      return prod_rec_output {
        __resolve_request(op, low1, low2),
        __resolve_request(op, high1, high2)
      };
    }

    static constexpr bool no_skip = false;
  };

  //////////////////////////////////////////////////////////////////////////////
  __bdd bdd_apply(const bdd &bdd_1, const bdd &bdd_2, const bool_op &op)
  {
    return product_construction<apply_prod_policy>(bdd_1, bdd_2, op);
  }

  //////////////////////////////////////////////////////////////////////////////
  __bdd bdd_and(const bdd &bdd_1, const bdd &bdd_2)
  {
    return bdd_apply(bdd_1, bdd_2, and_op);
  }

  __bdd bdd_nand(const bdd &bdd_1, const bdd &bdd_2)
  {
    return bdd_apply(bdd_1, bdd_2, nand_op);
  }

  __bdd bdd_or(const bdd &bdd_1, const bdd &bdd_2)
  {
    return bdd_apply(bdd_1, bdd_2, or_op);
  }

  __bdd bdd_nor(const bdd &bdd_1, const bdd &bdd_2)
  {
    return bdd_apply(bdd_1, bdd_2, nor_op);
  }

  __bdd bdd_xor(const bdd &bdd_1, const bdd &bdd_2)
  {
    return bdd_apply(bdd_1, bdd_2, xor_op);
  }

  __bdd bdd_xnor(const bdd &bdd_1, const bdd &bdd_2)
  {
    return bdd_apply(bdd_1, bdd_2, xnor_op);
  }

  __bdd bdd_imp(const bdd &bdd_1, const bdd &bdd_2)
  {
    return bdd_apply(bdd_1, bdd_2, imp_op);
  }

  __bdd bdd_invimp(const bdd &bdd_1, const bdd &bdd_2)
  {
    return bdd_apply(bdd_1, bdd_2, invimp_op);
  }

  __bdd bdd_equiv(const bdd &bdd_1, const bdd &bdd_2)
  {
    return bdd_apply(bdd_1, bdd_2, equiv_op);
  }

  __bdd bdd_diff(const bdd &bdd_1, const bdd &bdd_2)
  {
    return bdd_apply(bdd_1, bdd_2, diff_op);
  }

  __bdd bdd_less(const bdd &bdd_1, const bdd &bdd_2)
  {
    return bdd_apply(bdd_1, bdd_2, less_op);
  }
}
