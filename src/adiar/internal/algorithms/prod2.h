#ifndef ADIAR_INTERNAL_ALGORITHMS_PROD2_H
#define ADIAR_INTERNAL_ALGORITHMS_PROD2_H

#include <variant>

#include <adiar/bool_op.h>
#include <adiar/bdd/bdd.h>
#include <adiar/internal/cnl.h>
#include <adiar/internal/cut.h>
#include <adiar/internal/dd.h>
#include <adiar/internal/algorithms/build.h>
#include <adiar/internal/data_structures/levelized_priority_queue.h>
#include <adiar/internal/data_types/uid.h>
#include <adiar/internal/data_types/node.h>
#include <adiar/internal/data_types/tuple.h>
#include <adiar/internal/data_types/request.h>
#include <adiar/internal/io/arc_file.h>
#include <adiar/internal/io/arc_writer.h>
#include <adiar/internal/io/node_stream.h>

namespace adiar::internal
{
  //////////////////////////////////////////////////////////////////////////////
  /// Struct to hold statistics
  extern stats_t::prod2_t stats_prod2;

  //////////////////////////////////////////////////////////////////////////////
  // Data structures
  template<uint8_t nodes_carried>
  using prod2_request = request_data<2, with_parent, nodes_carried>;

  template<size_t LOOK_AHEAD, memory_mode_t mem_mode>
  using prod_priority_queue_1_t =
    levelized_node_priority_queue<prod2_request<0>, request_data_fst_lt<prod2_request<0>>,
                                  LOOK_AHEAD,
                                  mem_mode,
                                  2>;

  template<memory_mode_t mem_mode>
  using prod_priority_queue_2_t =
    priority_queue<mem_mode, prod2_request<1>, request_data_snd_lt<prod2_request<1>>>;

  // TODO: turn into 'tuple<tuple<ptr_uint64>>'
  struct prod2_rec_output {
    tuple<ptr_uint64> low;
    tuple<ptr_uint64> high;
  };

  typedef tuple<ptr_uint64> prod2_rec_skipto;

  typedef std::variant<prod2_rec_output, prod2_rec_skipto> prod2_rec;

  //////////////////////////////////////////////////////////////////////////////
  // Helper functions
  template<typename pq_1_t>
  inline void __prod2_recurse_out(pq_1_t &prod_pq_1, arc_writer &aw,
                                  const bool_op &op,
                                  ptr_uint64 source, tuple<ptr_uint64> target)
  {
    if (target[0].is_terminal() && target[1].is_terminal()) {
      arc out_arc = { source, op(target[0], target[1]) };
      aw.push_terminal(out_arc);
    } else {
      adiar_debug(source.label() < std::min(target[0], target[1]).label(),
                  "should always push recursion for 'later' level");

      prod_pq_1.push({ target, {}, {source} });
    }
  }

  template<typename out_policy, typename extra_arg, typename pq_1_t, typename pq_2_t>
  inline void __prod2_recurse_in(pq_1_t &prod_pq_1, pq_2_t &prod_pq_2,
                                 arc_writer &aw,
                                 const extra_arg &ea, ptr_uint64 t1, ptr_uint64 t2)
  {
    while (prod_pq_1.can_pull() && prod_pq_1.top().target[0] == t1 && prod_pq_1.top().target[1] == t2) {
      out_policy::go(prod_pq_1, aw, ea, prod_pq_1.pull().data.source);
    }

    while (!prod_pq_2.empty() && prod_pq_2.top().target[0] == t1 && prod_pq_2.top().target[1] == t2) {
      out_policy::go(prod_pq_1, aw, ea, prod_pq_2.top().data.source);
      prod_pq_2.pop();
    }
  }

  struct __prod2_recurse_in__output_node
  {
    template<typename pq_1_t>
    static inline void go(pq_1_t& /*prod_pq_1*/, arc_writer &aw,
                          node::uid_t out_uid, node::ptr_t source)
    {
      if (!source.is_nil()) {
        aw.push_internal({ source, out_uid });
      }
    }
  };

  struct __prod2_recurse_in__output_terminal
  {
    template<typename pq_1_t>
    static inline void go(pq_1_t& /*prod_pq_1*/, arc_writer &aw,
                          ptr_uint64 out_terminal, ptr_uint64 source)
    {
      aw.push_terminal({ source, out_terminal });
    }
  };

  struct __prod2_recurse_in__forward
  {
    template<typename pq_1_t>
    static inline void go(pq_1_t &prod_pq_1, arc_writer&,
                          const prod2_rec_skipto &r, ptr_uint64 source)
    {
      prod_pq_1.push({ { r[0], r[1] }, {}, {source} });
    }
  };

  inline shared_levelized_file<node>
  __prod2_terminal(const node::ptr_t &t1, const node::ptr_t &t2, const bool_op &op)
  {
    // TODO: Abuse that op(t1,t2) already is a pointer.
    return build_terminal(op(t1,t2).value());
  }

  //////////////////////////////////////////////////////////////////////////////
  class prod2_same_level_merger
  {
  public:
    static void merge_root(ptr_uint64 &low1, ptr_uint64 &high1, ptr_uint64 &low2, ptr_uint64 &high2,
                           node::label_t /* level */,
                           const node &v1, const node &v2)
    {
      low1 = v1.low();
      high1 = v1.high();

      low2 = v2.low();
      high2 = v2.high();
    }

  public:
    static void merge_data(ptr_uint64 &low1, ptr_uint64 &high1, ptr_uint64 &low2, ptr_uint64 &high2,
                           ptr_uint64 t1, ptr_uint64 t2, ptr_uint64 t_seek,
                           const node &v1, const node &v2,
                           ptr_uint64 data_low, ptr_uint64 data_high)
    {
      low1  = t1 < t_seek ? data_low  : v1.low();
      high1 = t1 < t_seek ? data_high : v1.high();

      low2  = t2 < t_seek ? data_low  : v2.low();
      high2 = t2 < t_seek ? data_high : v2.high();
    }
  };

  class prod2_mixed_level_merger
  {
  private:
    static void __merge_root(const node &v, ptr_uint64::label_t level,
                             ptr_uint64 &low, ptr_uint64 &high)
    {
      if (!v.is_terminal() && v.label() == level) {
        low = v.low();
        high = v.high();
      } else {
        low = high = v.uid();
      }
    }

  public:
    static void merge_root(ptr_uint64 &low1, ptr_uint64 &high1, ptr_uint64 &low2, ptr_uint64 &high2,
                           ptr_uint64::label_t level,
                           const node &v1, const node &v2)
    {
      __merge_root(v1, level, low1, high1);
      __merge_root(v2, level, low2, high2);
    }

  public:
    static void merge_data(ptr_uint64 &low1, ptr_uint64 &high1, ptr_uint64 &low2, ptr_uint64 &high2,
                           ptr_uint64 t1, ptr_uint64 t2, ptr_uint64 t_seek,
                           const node &v1, const node &v2,
                           ptr_uint64 data_low, ptr_uint64 data_high)
    {
      if (t1.is_terminal() || t2.is_terminal() || t1.label() != t2.label()) {
        if (t1 < t2) { // ==> t1.label() < t2.label() || t2.is_terminal()
          low1 = v1.low();
          high1 = v1.high();
          low2 = high2 = t2;
        } else { // ==> t1.label() > t2.label() || t1.is_terminal()
          low1 = high1 = t1;
          low2 = v2.low();
          high2 = v2.high();
        }
      } else {
        prod2_same_level_merger::merge_data(low1,high1, low2,high2,
                                           t1, t2, t_seek,
                                           v1, v2,
                                           data_low, data_high);
      }
    }
  };

  template<typename prod_policy, typename pq_1_t, typename pq_2_t>
  typename prod_policy::unreduced_t
  __prod2(const typename prod_policy::reduced_t &in_1,
          const typename prod_policy::reduced_t &in_2,
          const bool_op &op,
          const size_t pq_1_memory, const size_t max_pq_1_size,
          const size_t pq_2_memory, const size_t max_pq_2_size)
  {
    node_stream<> in_nodes_1(in_1);
    node_stream<> in_nodes_2(in_2);

    node v1 = in_nodes_1.pull();
    node v2 = in_nodes_2.pull();

    if (v1.is_terminal() || v2.is_terminal()) {
      typename prod_policy::unreduced_t maybe_resolved = prod_policy::resolve_terminal_root(v1, in_1, v2, in_2, op);

      if (!(maybe_resolved.template has<no_file>())) {
        return maybe_resolved;
      }
    }

    // Set-up for Product Construction Algorithm
    shared_levelized_file<arc> out_arcs;
    arc_writer aw(out_arcs);

    pq_1_t prod_pq_1({in_1, in_2}, pq_1_memory, max_pq_1_size, stats_prod2.lpq);
    pq_2_t prod_pq_2(pq_2_memory, max_pq_2_size);

    // Process root and create initial recursion requests
    typename prod_policy::label_t out_label = fst(v1.uid(), v2.uid()).label();
    typename prod_policy::id_t out_id = 0;

    typename prod_policy::ptr_t low1, low2, high1, high2;
    prod_policy::merge_root(low1,high1, low2,high2, out_label, v1, v2);

    // Shortcut the root (maybe)
    {
      prod_policy::compute_cofactor(v1.on_level(out_label), low1, high1);
      prod_policy::compute_cofactor(v2.on_level(out_label), low2, high2);

      prod2_rec root_rec = prod_policy::resolve_request(op, low1, low2, high1, high2);

      if (std::holds_alternative<prod2_rec_output>(root_rec)) {
        prod2_rec_output r = std::get<prod2_rec_output>(root_rec);
        const node::uid_t out_uid(out_label, out_id++);

        __prod2_recurse_out(prod_pq_1, aw, op, out_uid, r.low);
        __prod2_recurse_out(prod_pq_1, aw, op, flag(out_uid), r.high);
      } else { // std::holds_alternative<prod2_rec_skipto>(root_rec)
        prod2_rec_skipto r = std::get<prod2_rec_skipto>(root_rec);

        if (r[0].is_terminal() && r[1].is_terminal()) {
          return __prod2_terminal(r[0], r[1], op);
        } else {
          prod_pq_1.push({ { r[0], r[1] }, {}, { ptr_uint64::NIL() } });
        }
      }
    }

    size_t max_1level_cut = 0;

    // Process nodes in topological order of both BDDs
    while (!prod_pq_1.empty() || !prod_pq_2.empty()) {
      if (prod_pq_1.empty_level() && prod_pq_2.empty()) {
        if (prod_policy::no_skip || out_id > 0) {
          // Only output level_info information on prior level, if output
          aw.push(level_info(out_label, out_id));
        }

        prod_pq_1.setup_next_level();
        out_label = prod_pq_1.current_level();
        out_id = 0;

        max_1level_cut = std::max(max_1level_cut, prod_pq_1.size());
      }

      prod2_request<1> req;
      bool with_data;

      // Merge requests from prod_pq_1 or prod_pq_2
      if (prod_pq_1.can_pull() && (prod_pq_2.empty() ||
                                   prod_pq_1.top().target.fst() < prod_pq_2.top().target.snd())) {
        with_data = false;
        req = { prod_pq_1.top().target,
                {{ { node::ptr_t::NIL(), node::ptr_t::NIL() } }},
                { prod_pq_1.top().data } };
      } else {
        with_data = true;
        req = prod_pq_2.top();
      }

      adiar_invariant(req.target[0].is_terminal() || out_label <= req.target[0].label(),
                      "Request should never level-wise be behind current position");
      adiar_invariant(req.target[1].is_terminal() || out_label <= req.target[1].label(),
                      "Request should never level-wise be behind current position");

      // Seek request partially in stream
      ptr_uint64 t_seek = with_data ? req.target.snd() : req.target.fst();
      while (v1.uid() < t_seek && in_nodes_1.can_pull()) {
        v1 = in_nodes_1.pull();
      }
      while (v2.uid() < t_seek && in_nodes_2.can_pull()) {
        v2 = in_nodes_2.pull();
      }

      // Forward information across the level
      if (!with_data
          && req.target[0].is_node() && req.target[1].is_node()
          && req.target[0].label() == req.target[1].label()
          && (v1.uid() != req.target[0] || v2.uid() != req.target[1])) {
        node v_forwarded = req.target[0] == v1.uid() ? v1 : v2;

        while (prod_pq_1.can_pull() && prod_pq_1.top().target == req.target) {
          prod_pq_2.push({ req.target, { v_forwarded.children() }, prod_pq_1.pull().data });
        }
        continue;
      }

      // Resolve current node and recurse
      // remember from above: ptr low1, low2, high1, high2;
      // TODO: clean up...
      prod_policy::merge_data(low1,high1, low2,high2,
                              req.target[0], req.target[1], t_seek,
                              v1, v2,
                              req.node_carry[0][0], req.node_carry[0][1]);

      // Resolve request
      prod_policy::compute_cofactor(req.target[0].on_level(out_label), low1, high1);
      prod_policy::compute_cofactor(req.target[1].on_level(out_label), low2, high2);

      prod2_rec rec_res = prod_policy::resolve_request(op, low1, low2, high1, high2);

      if (prod_policy::no_skip || std::holds_alternative<prod2_rec_output>(rec_res)) {
        prod2_rec_output r = std::get<prod2_rec_output>(rec_res);

        adiar_debug(out_id < prod_policy::MAX_ID, "Has run out of ids");
        const node::uid_t out_uid(out_label, out_id++);

        __prod2_recurse_out(prod_pq_1, aw, op, out_uid, r.low);
        __prod2_recurse_out(prod_pq_1, aw, op, flag(out_uid), r.high);

        __prod2_recurse_in<__prod2_recurse_in__output_node>(prod_pq_1, prod_pq_2, aw, out_uid,
                                                      req.target[0], req.target[1]);

      } else { // std::holds_alternative<prod2_rec_skipto>(root_rec)
        prod2_rec_skipto r = std::get<prod2_rec_skipto>(rec_res);
        if (r[0].is_terminal() && r[1].is_terminal()) {
          if (req.data.source.is_nil()) {
            // Skipped in both DAGs all the way from the root until a pair of terminals.
            return __prod2_terminal(r[0], r[1], op);
          }
          __prod2_recurse_in<__prod2_recurse_in__output_terminal>(prod_pq_1, prod_pq_2, aw, op(r[0], r[1]),
                                                            req.target[0], req.target[1]);
        } else {
          __prod2_recurse_in<__prod2_recurse_in__forward>(prod_pq_1, prod_pq_2, aw, r,
                                                    req.target[0], req.target[1]);
        }
      }
    }

    if (prod_policy::no_skip || out_id > 0) {
      // Push the level of the very last iteration
      aw.push(level_info(out_label, out_id));
    }

    out_arcs->max_1level_cut = max_1level_cut;

    return out_arcs;
  }

  //////////////////////////////////////////////////////////////////////////////
  /// Derives an upper bound on the output's maximum i-level cut based on the
  /// product of the maximum i-level cut of both inputs.
  //////////////////////////////////////////////////////////////////////////////
  template<typename prod_policy, typename cut, size_t const_size_inc>
  size_t __prod2_ilevel_upper_bound(const typename prod_policy::reduced_t &in_1,
                                    const typename prod_policy::reduced_t &in_2,
                                    const bool_op &op)
  {
    // Cuts for left-hand side
    const safe_size_t left_cut_internal = cut::get(in_1, cut_type::INTERNAL);

    const cut_type left_ct = prod_policy::left_cut(op);
    const safe_size_t left_cut_terminals = cut::get(in_1, left_ct) - left_cut_internal;

    // Cuts for right-hand side
    const safe_size_t right_cut_internal = cut::get(in_2, cut_type::INTERNAL);

    const cut_type right_ct = prod_policy::right_cut(op);
    const safe_size_t right_cut_terminals = cut::get(in_2, right_ct) - right_cut_internal;

    // Compute cut, where we make sure not to pair terminals with terminals.
    return to_size(left_cut_internal * right_cut_internal
                   + left_cut_terminals * right_cut_internal
                   + left_cut_internal * right_cut_terminals
                   + const_size_inc);
  }

  //////////////////////////////////////////////////////////////////////////////
  /// Derives an upper bound on the output's maximum 2-level cut based on both
  /// using the max 1 and 2-level cuts and the number of relevant terminals.
  //////////////////////////////////////////////////////////////////////////////
  template<typename prod_policy>
  size_t __prod2_2level_upper_bound(const typename prod_policy::reduced_t &in_1,
                                    const typename prod_policy::reduced_t &in_2,
                                    const bool_op &op)
  {
    // Left-hand side
    const safe_size_t left_2level_cut = in_1.max_2level_cut(cut_type::INTERNAL);
    const safe_size_t left_1level_cut = in_1.max_1level_cut(cut_type::INTERNAL);

    const cut_type left_ct = prod_policy::left_cut(op);
    const safe_size_t left_terminal_vals = number_of_terminals(left_ct);

    const safe_size_t left_terminal_arcs =  in_1.max_1level_cut(left_ct) - left_1level_cut;

    // Right-hand side
    const safe_size_t right_2level_cut = in_2.max_2level_cut(cut_type::INTERNAL);
    const safe_size_t right_1level_cut = in_2.max_1level_cut(cut_type::INTERNAL);

    const cut_type right_ct = prod_policy::right_cut(op);
    const safe_size_t right_terminal_vals = number_of_terminals(right_ct);

    const safe_size_t right_terminal_arcs = in_2.max_1level_cut(right_ct) - right_1level_cut;

    // Compute cut, where we count the product, the input-terminal pairings, and the
    // connection from the product to the input-terminal pairings separately.
    return to_size(left_2level_cut * right_2level_cut
                   + (right_1level_cut * left_terminal_arcs) + left_terminal_vals * right_2level_cut
                   + (left_1level_cut * right_terminal_arcs) + right_terminal_vals * left_2level_cut
                   + 2u);
  }

  //////////////////////////////////////////////////////////////////////////////
  /// Upper bound on i-level cut based on the maximum possible number of nodes
  /// in the output.
  //////////////////////////////////////////////////////////////////////////////
  template<typename prod_policy>
  size_t __prod2_ilevel_upper_bound(const typename prod_policy::reduced_t &in_1,
                                   const typename prod_policy::reduced_t &in_2,
                                   const bool_op &op)
  {
    const cut_type left_ct = prod_policy::left_cut(op);
    const safe_size_t left_terminal_vals = number_of_terminals(left_ct);
    const safe_size_t left_size = in_1->size();

    const cut_type right_ct = prod_policy::right_cut(op);
    const safe_size_t right_terminal_vals = number_of_terminals(right_ct);
    const safe_size_t right_size = in_2->size();

    return to_size((left_size + left_terminal_vals) * (right_size + right_terminal_vals) + 1u + 2u);
  }

  //////////////////////////////////////////////////////////////////////////////
  /// Creates the product construction of the given two DAGs.
  ///
  /// Behaviour of the product construction is controlled with the 'prod_policy'
  /// class, which exposes static void strategy functions.
  ///
  /// - resolve_same_file:
  ///   Creates the output based on knowing both inputs refer to the same
  ///   underlying file.
  ///
  /// - resolve_terminal_root:
  ///   Resolves (if possible) the cases for one of the two DAGs only being a
  ///   terminal. Uses the _union in the 'out_t' to trigger an early termination. If
  ///   it holds an 'adiar::no_file', then the algorithm proceeds to the actual
  ///   product construction.
  ///
  /// - resolve_request:
  ///   Given all information collected for the two nodes (both children, if
  ///   they are on the same level. Otherwise, only the first-seen node),
  ///   returns whether (a) a node should be output and its two children to
  ///   recurse to or (b) no node should be output (i.e. it is skipped) and what
  ///   child to forward the request to.
  ///
  /// - no_skip:
  ///   Constexpr boolean whether the strategy guarantees never to skip a level.
  ///   This shortcuts some boolean conditions at compile-time.
  ///
  /// This 'prod_policy' also should inherit the general policy for the
  /// decision_diagram used (i.e. bdd_policy in bdd/bdd.h, zdd_policy in
  /// zdd/zdd.h and so on). This provides the following functions
  ///
  /// - compute_cofactor:
  ///   Used to change the low and high children retrieved from the input during
  ///   the product construction.
  ///
  /// Other parameters are:
  ///
  /// \param in_i  DAGs to combine into one.
  ///
  /// \param op    Binary boolean operator to be applied. See data.h for the
  ///              ones directly provided by Adiar.
  ///
  /// \return      A class that inherits from __dd and describes
  ///              the product of the two given DAGs.
  //////////////////////////////////////////////////////////////////////////////
  template<typename prod_policy>
  typename prod_policy::unreduced_t
  prod2(const typename prod_policy::reduced_t &in_1,
        const typename prod_policy::reduced_t &in_2,
        const bool_op &op)
  {
    if (in_1.file_ptr() == in_2.file_ptr()) {
      return prod_policy::resolve_same_file(in_1, in_2, op);
    }

    // Compute amount of memory available for auxiliary data structures after
    // having opened all streams.
    //
    // We then may derive an upper bound on the size of auxiliary data
    // structures and check whether we can run them with a faster internal
    // memory variant.
    const size_t aux_available_memory = memory_available()
      // Input streams
      - 2*node_stream<>::memory_usage()
      // Output stream
      - arc_writer::memory_usage();

    constexpr size_t data_structures_in_pq_1 =
      prod_priority_queue_1_t<ADIAR_LPQ_LOOKAHEAD, memory_mode_t::INTERNAL>::DATA_STRUCTURES;

    constexpr size_t data_structures_in_pq_2 =
      prod_priority_queue_2_t<memory_mode_t::INTERNAL>::DATA_STRUCTURES;

    const size_t pq_1_internal_memory =
      (aux_available_memory / (data_structures_in_pq_1 + data_structures_in_pq_2)) * data_structures_in_pq_1;

    const size_t pq_2_internal_memory = aux_available_memory - pq_1_internal_memory;

    const size_t pq_1_memory_fits =
      prod_priority_queue_1_t<ADIAR_LPQ_LOOKAHEAD, memory_mode_t::INTERNAL>::memory_fits(pq_1_internal_memory);

    const size_t pq_2_memory_fits =
      prod_priority_queue_2_t<memory_mode_t::INTERNAL>::memory_fits(pq_2_internal_memory);

    const bool internal_only = memory_mode == memory_mode_t::INTERNAL;
    const bool external_only = memory_mode == memory_mode_t::EXTERNAL;

    const size_t pq_1_bound = std::min({__prod2_ilevel_upper_bound<prod_policy, get_2level_cut, 2u>(in_1, in_2, op),
                                        __prod2_2level_upper_bound<prod_policy>(in_1, in_2, op),
                                        __prod2_ilevel_upper_bound<prod_policy>(in_1, in_2, op)});

    const size_t max_pq_1_size = internal_only ? std::min(pq_1_memory_fits, pq_1_bound) : pq_1_bound;

    const size_t pq_2_bound = __prod2_ilevel_upper_bound<prod_policy, get_1level_cut, 0u>(in_1, in_2, op);

    const size_t max_pq_2_size = internal_only ? std::min(pq_2_memory_fits, pq_2_bound) : pq_2_bound;

    if(!external_only && max_pq_1_size <= no_lookahead_bound(2)) {
#ifdef ADIAR_STATS
      stats_prod2.lpq.unbucketed += 1u;
#endif
      return __prod2<prod_policy,
                     prod_priority_queue_1_t<0, memory_mode_t::INTERNAL>,
                     prod_priority_queue_2_t<memory_mode_t::INTERNAL>>
        (in_1, in_2, op, pq_1_internal_memory, max_pq_1_size, pq_2_internal_memory, max_pq_2_size);
    } else if(!external_only && max_pq_1_size <= pq_1_memory_fits
                             && max_pq_2_size <= pq_2_memory_fits) {
#ifdef ADIAR_STATS
      stats_prod2.lpq.internal += 1u;
#endif
      return __prod2<prod_policy,
                     prod_priority_queue_1_t<ADIAR_LPQ_LOOKAHEAD, memory_mode_t::INTERNAL>,
                     prod_priority_queue_2_t<memory_mode_t::INTERNAL>>
        (in_1, in_2, op, pq_1_internal_memory, max_pq_1_size, pq_2_internal_memory, max_pq_2_size);
    } else {
#ifdef ADIAR_STATS
      stats_prod2.lpq.external += 1u;
#endif
      const size_t pq_1_memory = aux_available_memory / 2;
      const size_t pq_2_memory = pq_1_memory;

      return __prod2<prod_policy,
                     prod_priority_queue_1_t<ADIAR_LPQ_LOOKAHEAD, memory_mode_t::EXTERNAL>,
                     prod_priority_queue_2_t<memory_mode_t::EXTERNAL>>
        (in_1, in_2, op, pq_1_memory, max_pq_1_size, pq_2_memory, max_pq_2_size);
    }
  }
}

#endif // ADIAR_INTERNAL_ALGORITHMS_PROD2_H
