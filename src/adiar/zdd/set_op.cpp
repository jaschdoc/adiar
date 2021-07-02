#include "set_op.h"

#include <tpie/sort.h>

#include <adiar/file_stream.h>
#include <adiar/file_writer.h>
#include <adiar/tuple.h>

#include <adiar/internal/product_construction.h>

#include <adiar/zdd/zdd.h>
#include <adiar/zdd/build.h>

#include <adiar/assert.h>

namespace adiar
{
  bool can_right_shortcut_zdd(const bool_op &op, const ptr_t sink)
  {
    ptr_t sink_F = create_sink_ptr(false);
    ptr_t sink_T = create_sink_ptr(true);

    return // Does it shortcut on this level?
         op(sink_F, sink) == sink_F && op(sink_T,  sink) == sink_F
      // Does it shortcut on all other levels below?
      && op(sink_F, sink_F) == sink_F && op(sink_T,  sink_F) == sink_F;
  }

  bool can_left_shortcut_zdd(const bool_op &op, const ptr_t sink)
  {
    ptr_t sink_F = create_sink_ptr(false);
    ptr_t sink_T = create_sink_ptr(true);

    return // Does it shortcut on this level?
      op(sink, sink_F) == sink_F && op(sink, sink_T) == sink_F
      // Does it shortcut on all other levels below?
      && op(sink_F, sink_F) == sink_F && op(sink_F,  sink_T) == sink_F;
  }

  bool zdd_skippable(const bool_op &op, ptr_t high1, ptr_t high2)
  {
    return (is_sink(high1) && is_sink(high2)
            && op(high1, high2) == create_sink_ptr(false))
      || (is_sink(high1) && can_left_shortcut_zdd(op, high1))
      || (is_sink(high2) && can_right_shortcut_zdd(op, high2));
  }

  //////////////////////////////////////////////////////////////////////////////
  // ZDD product construction policy
  class zdd_prod_policy : public zdd_policy, public prod_mixed_level_merger
  {
  public:
    static __zdd resolve_same_file(const zdd &zdd_1, const zdd &/* zdd_2 */,
                                   const bool_op &op)
    {
      // Compute the results on all children.
      ptr_t op_F = op(create_sink_ptr(false), create_sink_ptr(false));
      ptr_t op_T = op(create_sink_ptr(true), create_sink_ptr(true));

      // Does it collapse to a sink?
      if (op_F == op_T) {
        return zdd_sink(value_of(op_F));
      }

      return zdd_1;
    }

  public:
    static __zdd resolve_sink_root(const node_t &v1, const zdd& zdd_1,
                                   const node_t &v2, const zdd& zdd_2,
                                   const bool_op &op)
    {
      ptr_t sink_F = create_sink_ptr(false);

      if (is_sink(v1) && is_sink(v2)) {
        ptr_t p = op(v1.uid, v2.uid);
        return zdd_sink(value_of(p));
      } else if (is_sink(v1)) {
        if (can_left_shortcut_zdd(op, v1.uid))  {
          // Shortcuts the left-most path to {Ø} and all others to Ø
          return zdd_sink(false);
        } else if (is_left_irrelevant(op, v1.uid) && is_left_irrelevant(op, sink_F)) {
          // Has no change to left-most path to {Ø} and neither any others
          return zdd_2;
        }
      } else { // if (is_sink(v2)) {
        if (can_right_shortcut_zdd(op, v2.uid)) {
          // Shortcuts the left-most path to {Ø} and all others to Ø
          return zdd_sink(false);
        } else if (is_right_irrelevant(op, v2.uid) && is_right_irrelevant(op, sink_F)) {
          // Has no change to left-most path to {Ø} and neither any others
          return zdd_1;
        }
      }
      return __zdd(); // return with no_file
    }

  private:
    static tuple __resolve_request(const bool_op &op, ptr_t r1, ptr_t r2)
    {
      if (is_sink(r1) && can_left_shortcut_zdd(op, r1)) {
        return { r1, create_sink_ptr(true) };
      } else if (is_sink(r2) && can_right_shortcut_zdd(op, r2)) {
        return { create_sink_ptr(true), r2 };
      } else {
        return { r1, r2 };
      }
    }

  public:
    static prod_rec resolve_request(const bool_op &op,
                                    ptr_t low1, ptr_t low2, ptr_t high1, ptr_t high2)
    {
      // Skip node, if it would be removed in the following Reduce
      if (zdd_skippable(op, high1, high2)) {
        return prod_rec_skipto { low1, low2 };
      } else {
        return prod_rec_output {
          __resolve_request(op, low1, low2),
          __resolve_request(op, high1, high2)
        };
      }
    }

    static constexpr bool no_skip = false;
  };

  //////////////////////////////////////////////////////////////////////////////
  __zdd zdd_binop(const zdd &zdd_1, const zdd &zdd_2, const bool_op &op)
  {
    return product_construction<zdd_prod_policy, __zdd>(zdd_1, zdd_2, op);
  }

  //////////////////////////////////////////////////////////////////////////////
  __zdd zdd_union(const zdd &zdd_1, const zdd &zdd_2)
  {
    return zdd_binop(zdd_1, zdd_2, or_op);
  }

  __zdd zdd_intsec(const zdd &zdd_1, const zdd &zdd_2)
  {
    return zdd_binop(zdd_1, zdd_2, and_op);
  }

  __zdd zdd_diff(const zdd &zdd_1, const zdd &zdd_2)
  {
    return zdd_binop(zdd_1, zdd_2, diff_op);
  }

  //////////////////////////////////////////////////////////////////////////////
  typedef tpie::merge_sorter<arc_t, false, arc_target_lt> zdd_comp_sorter_t;

  // TODO: We cannot have them as constants, since any input with id's of the
  // form 0, 1, ... or ..., MAX_ID, MAX_ID-1 would overlap. We would need to
  // find two non-existent id's within the given input.
  const id_t zdd_comp_dont_care_id = MAX_ID;
  const id_t zdd_comp_alo_id = MAX_ID - 1;

  ptr_t zdd_comp_reroute(const ptr_t p, const bool has_next_label, const label_t next_label)
  {
    if (is_sink(p)) {
      if (has_next_label) {
        const id_t next_id = value_of(p) ? zdd_comp_alo_id : zdd_comp_dont_care_id;
        return create_node_ptr(next_label, next_id);
      }
      return negate(p);
    }
    return p;
  }

  void zdd_comp_recurse_out(std::unique_ptr<zdd_comp_sorter_t> &sorter, arc_writer &aw,
                            const ptr_t source, const ptr_t target,
                            const bool has_next_label, const label_t next_label)
  {
    if (is_sink(target)) {
      arc_t out_arc = { source, target };
      aw.unsafe_push_sink(out_arc);
    } else {
      adiar_debug(label_of(source) < label_of(target),
                  "should always push recursion for 'later' level");
      adiar_debug(!has_next_label || label_of(source) < next_label,
                  "should be in sync with domain");

      sorter -> push({ source, target });
    }
  }

  __zdd zdd_complement(const zdd &in, const label_file &dom)
  {
    node_stream<> in_nodes(in);
    node_t v = in_nodes.pull();

    label_stream<> in_labels(dom);
    label_t out_label = in_labels.pull();
    id_t out_id = 0u;

    bool has_next_label = false;
    label_t next_label;

    // Resolve sink cases
    if (is_sink(v)) {
      // TODO: If attribute edges are added, then merely complement the root of
      //       the powerset?
      return value_of(v)
        ? zdd_sized_sets(dom, 0u, std::greater<label_t>()) // 2^dom \ {Ø}
        : zdd_powerset(dom); // 2^dom \ Ø = 2^dom
    }

    arc_file out_arcs;
    arc_writer aw(out_arcs);

    // Set up merge sorters for recursion. Since all recursions always go to the
    // very next level, then we can merely do with
    //
    // TODO: Generalise this into a two-bucket levelized_priority queue, that in
    // code is much simpler (i.e. faster) than what is in the
    // 'levelized_priority_queue'.
    tpie::memory_size_type available_memory = tpie::get_memory_manager().available();

    bool curr_sorter_idx = 1;
    std::unique_ptr<zdd_comp_sorter_t> sorters[2];
    sorters[0] = std::make_unique<zdd_comp_sorter_t>();
    sorters[0] -> set_available_memory(available_memory/2,
                                       /* TODO: More fine-grained overlapping memory usage */);
    sorters[0] -> begin();

    // Use an at-least-once chain, where we wait for a single 1 to fall out of
    // the input.
    bool alo_chain = false;

    // Use a dont_care_chain whenever we have fallen out of the input.
    bool dont_care_chain = false;

    // Add nodes before root of 'in' and keep track of whether one is already
    // outside.
    if (out_label < label_of(v)) { aw.unsafe_push(create_meta(out_label,1u)); }

    while (out_label < label_of(v)) {
      adiar_debug(in_labels.can_pull(), "domain should cover the given ZDD");
      next_label = in_labels.pull();

      { // Seen nothing yet
        const ptr_t s = create_node_ptr(out_label, 0u);

        aw.unsafe_push_node({ s, create_node_ptr(next_label, 0u) });
        aw.unsafe_push_node({ flag(s), create_node_ptr(next_label, zdd_comp_dont_care_id) });
      }

      if (dont_care_chain) { // Seen something already
        const ptr_t s = create_node_ptr(out_label, zdd_comp_dont_care_id);
        const ptr_t t = create_node_ptr(next_label, zdd_comp_dont_care_id);

        aw.unsafe_push_node({ s, t });
        aw.unsafe_push_node({ flag(s), t });
      }

      aw.unsafe_push(create_meta(next_label,2u));
      dont_care_chain = true;

      out_label = next_label;
    }

    adiar_debug(out_label == label_of(v), "domain should include root node");

    has_next_label = in_labels.can_pull();
    if (has_next_label) { next_label = in_labels.pull(); }

    { // Resolve the root of the input and set up recursion
      const ptr_t low = zdd_comp_reroute(v.low, has_next_label, next_label);
      const ptr_t high = zdd_comp_reroute(v.high, has_next_label, next_label);

      const bool is_root = !dont_care_chain;
      if (is_root && is_sink(high) && !value_of(high)) {
        adiar_debug(is_sink(low),
                    "high is only the false sink, if ~has_next_label. So, neither should low be anything but a sink");
        return zdd_sink(value_of(low));
      }

      const uid_t out_uid = create_node_ptr(out_label, out_id++); // (out_label,0)
      const std::unique_ptr<zdd_comp_sorter_t>& sorter = sorters[curr_sorter_idx+1 % 2];

      zdd_comp_recurse_out(sorter, aw,
                           out_uid, low, has_next_label, next_label);
      zdd_comp_recurse_out(sorter, aw,
                           flag(out_uid), high, has_next_label, next_label);

      // Notice, that we have already output the in-going arcs to the root
      // above, so we don't need to do that again.
    }

    // Resolve recursion requests
    while (has_next_level) {
      adiar_invariant(!comp_pq_1.can_pull() && !comp_pq_2.can_pull(), "Entire prior level was emptied");

      // Unlike in the product construction, we never skip nodes. Except for
      // the very bottom_most nodes in the input, since we (almost) always
      // reroute the sinks to the two chains. So, here we really just leave it
      // for the following Reduce instead.
      id_t output_nodes = out_id + dont_care_chain + alo_chain;
      aw.unsafe_push(create_meta(out_label, output_nodes));

      adiar_debug(has_next_label, "Recursion requests should not exceed the domain");
      adiar_debug(!has_next_label || out_label < next_label, "Domain should be given in-order");
      out_label = next_label;

      has_next_label = in_labels.can_pull();
      if (has_next_label) { next_label = in_labels.pull(); }

      out_id = 0;

      curr_sorter_idx = curr_sorter_idx + 1 % 2;

      // TODO: Sort

      adiar_invariant(comp_pq_1.current_level() == out_label, "Priority queue 1 should be in sync");
      adiar_invariant(comp_pq_2.current_level() == out_label, "Priority queue 2 should be in sync");

      // Empty all requests for 'insert skipped node'. Stay within the input on
      // the low, but go to the don't care chain on the high.
      while (comp_pq_2.can_pull()) {
        ptr_t source = comp_pq_2.top().source;

        adiar_invariant(!is_sink(comp_pq_2.top().t1), "Extra nodes are not to-be between a node and a sink");
        const ptr_t low = comp_pq_2.top().t1;

        adiar_invariant(has_next_label, "Extra nodes are not to-be added at the very bottom");
        const ptr_t high = create_node_ptr(next_label, zdd_comp_dont_care_id);

        const uid_t out_uid = create_node_ptr(out_label, out_id++);

        zdd_comp_recurse_out(comp_pq_1, comp_pq_2, aw,
                             out_uid, low, has_next_label, next_label);
        zdd_comp_recurse_out(comp_pq_1, comp_pq_2, aw,
                             flag(out_uid), high, has_next_label, next_label);

        while (comp_pq_2.can_pull() && label_of(comp_pq_2.top().t2) == out_label && comp_pq_2.top().t1 == low) {
          source = comp_pq_2.pull().source;
          aw.unsafe_push_node({ source, out_uid });
        }
      }

      // Empty all requests for the current level
      while (comp_pq_1.can_pull()) {
        ptr_t source = comp_pq_1.top().source;
        const ptr_t target = comp_pq_1.top().target;

        uid_t out_uid;
        ptr_t low, high;

        if (id_of(target) == zdd_comp_dont_care_id || id_of(target) == zdd_comp_alo_id) {
          // Don't care or ALO nodes
          dont_care_chain = dont_care_chain || id_of(target) == zdd_comp_dont_care_id;
          alo_chain = alo_chain || id_of(target) == zdd_comp_alo_id;

          out_uid = target;

          low = has_next_label
            ? create_node_ptr(next_label, id_of(target))
            : create_sink_ptr(id_of(target) == zdd_comp_dont_care_id);

          high = has_next_label
            ? create_node_ptr(next_label, zdd_comp_dont_care_id)
            : create_sink_ptr(true);
        } else { // Node within the input
          while (v.uid < target) { v = in_nodes.pull(); }
          adiar_invariant(v.uid == target, "Should search/reach existing node");

          out_uid = create_node_ptr(out_label, out_id++);

          low = zdd_comp_reroute(v.low, has_next_label, next_label);
          high = zdd_comp_reroute(v.high, has_next_label, next_label);
        }

        zdd_comp_recurse_out(comp_pq_1, comp_pq_2, aw,
                             out_uid, low, has_next_label, next_label);
        zdd_comp_recurse_out(comp_pq_1, comp_pq_2, aw,
                             flag(out_uid), high, has_next_label, next_label);

        while (comp_pq_1.can_pull() && comp_pq_1.top().target == target) {
          source = comp_pq_1.pull().source;
          aw.unsafe_push_node({ source, out_uid });
        }
      }
    }
    return out_arcs;
  }
}
