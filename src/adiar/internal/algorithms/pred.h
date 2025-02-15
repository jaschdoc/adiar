#ifndef ADIAR_INTERNAL_ALGORITHMS_PRED_H
#define ADIAR_INTERNAL_ALGORITHMS_PRED_H

#include <adiar/internal/dd.h>
#include <adiar/internal/algorithms/prod2.h>
#include <adiar/internal/data_structures/levelized_priority_queue.h>
#include <adiar/internal/data_types/uid.h>
#include <adiar/internal/data_types/node.h>
#include <adiar/internal/data_types/request.h>
#include <adiar/internal/data_types/tuple.h>
#include <adiar/internal/io/levelized_file.h>
#include <adiar/internal/io/levelized_file_stream.h>

namespace adiar::internal
{
  //////////////////////////////////////////////////////////////////////////////
  /// Struct to hold statistics for equality checking
  extern stats_t::equality_t stats_equality;

  //////////////////////////////////////////////////////////////////////////////
  /// \brief Compute whether two shared levelized node files (with associated
  ///        negation flags) are isomorphic.
  ///
  /// \details Checks whether the two files are isomorphic, i.e. whether there
  ///          is a structure-preserving mapping between f1 and f2. This
  ///          assumes, that both files are of a unique reduced form.
  ///
  /// \param fi      The two files of nodes to compare.
  /// \param negatei Whether the nodes of fi should be read in negated form
  ///
  /// \return  Whether <tt>f1</tt> and <tt>f2</tt> have isomorphic DAGs when
  ///          applying the given negation flags.
  //////////////////////////////////////////////////////////////////////////////
  bool is_isomorphic(const shared_levelized_file<node> &f1,
                     const shared_levelized_file<node> &f2,
                     bool negate1 = false,
                     bool negate2 = false);

  //////////////////////////////////////////////////////////////////////////////
  /// \brief Computes whether two decision diagrams are isomorphic; i.e. whether
  ///        they are equivalent (under the same deletion-rule).
  ///
  /// \details Checks whether the two files are isomorphic, i.e. whether there
  ///          is a structure-preserving mapping between f1 and f2. This
  ///          assumes, that both files are of a unique reduced form.
  ///
  /// \param a   The first decision diagram.
  /// \param b   The second decision diagram.
  ///
  /// \return    Whether <tt>a</tt> and <tt>b</tt> have isomorphic DAGs.
  //////////////////////////////////////////////////////////////////////////////
  bool is_isomorphic(const dd &a, const dd &b);

  //////////////////////////////////////////////////////////////////////////////
  // Data structures
  template<uint8_t nodes_carried>
  using pred_request = request<2, nodes_carried>;

  template<size_t LOOK_AHEAD, memory_mode_t mem_mode>
  using comparison_priority_queue_1_t =
    levelized_node_priority_queue<pred_request<0>, request_fst_lt<pred_request<0>>,
                                  LOOK_AHEAD,
                                  mem_mode,
                                  2u>;

  typedef request<2, 1> pred_request_2;

  template<memory_mode_t mem_mode>
  using comparison_priority_queue_2_t =
    priority_queue<mem_mode, pred_request<1>, request_snd_lt<pred_request<1>>>;

  template<typename comp_policy, typename pq_1_t, typename pq_2_t>
  bool __comparison_check(const shared_levelized_file<node> &f1,
                          const shared_levelized_file<node> &f2,
                          const bool negate1,
                          const bool negate2,
                          const tpie::memory_size_type pq_1_memory,
                          const tpie::memory_size_type pq_2_memory,
                          const size_t max_pq_size)
  {
    node_stream<> in_nodes_1(f1, negate1);
    node_stream<> in_nodes_2(f2, negate2);

    node v1 = in_nodes_1.pull();
    node v2 = in_nodes_2.pull();

    if (v1.is_terminal() || v2.is_terminal()) {
      bool ret_value;
      if (comp_policy::resolve_terminals(v1, v2, ret_value)) {
        return ret_value;
      }
    }

    if (v1.low().is_terminal() && v1.high().is_terminal() && v2.low().is_terminal() && v2.high().is_terminal()) {
      return comp_policy::resolve_singletons(v1, v2);
    }

    // Set up priority queue for recursion
    pq_1_t comparison_pq_1({f1, f2}, pq_1_memory, max_pq_size, stats_equality.lpq);

    // Check for violation on root children, or 'recurse' otherwise
    typename comp_policy::label_t level = fst(v1.uid(), v2.uid()).label();

    ptr_uint64 low1, high1, low2, high2;
    comp_policy::merge_root(low1,high1, low2,high2, level, v1, v2);

    comp_policy::compute_cofactor(v1.on_level(level), low1, high1);
    comp_policy::compute_cofactor(v2.on_level(level), low2, high2);

    if (comp_policy::resolve_request(comparison_pq_1, low1, low2)
        || comp_policy::resolve_request(comparison_pq_1, high1, high2)) {
      return comp_policy::early_return_value;
    }

    // Initialise level checking
    typename comp_policy::level_check_t level_checker(f1,f2);

    pq_2_t comparison_pq_2(pq_2_memory, max_pq_size);

    while (!comparison_pq_1.empty() || !comparison_pq_2.empty()) {
      if (comparison_pq_1.empty_level() && comparison_pq_2.empty()) {
        comparison_pq_1.setup_next_level();

        level_checker.next_level(comparison_pq_1.current_level());
      }

      pred_request_2 req;
      bool with_data;

      // Merge requests from comparison_pq_1 and comparison_pq_2
      if (comparison_pq_1.can_pull() && (comparison_pq_2.empty() ||
                                         comparison_pq_1.top().target.fst() < comparison_pq_2.top().target.snd())) {
        with_data = false;

        req = { comparison_pq_1.top().target,
                { {{ node::ptr_t::NIL(), node::ptr_t::NIL() }} } };
        comparison_pq_1.pop();
      } else {
        with_data = true;

        req = comparison_pq_2.top();
        comparison_pq_2.pop();
      }

      // Seek request partially in stream
      ptr_uint64 t_seek = with_data ? req.target.snd() : req.target.fst();

      while (v1.uid() < t_seek && in_nodes_1.can_pull()) {
        v1 = in_nodes_1.pull();
      }
      while (v2.uid() < t_seek && in_nodes_2.can_pull()) {
        v2 = in_nodes_2.pull();
      }

      // Skip all requests to the same node
      while (comparison_pq_1.can_pull() && (comparison_pq_1.top().target == req.target)) {
        comparison_pq_1.pull();
      }

      // Forward information across the level
      if (!with_data
          && req.target[0].is_node() && req.target[1].is_node()
          && req.target[0].label() == req.target[1].label()
          && (v1.uid() != req.target[0] || v2.uid() != req.target[1])) {
        const node v_forwarded = req.target[0] == v1.uid() ? v1 : v2;

        comparison_pq_2.push({ req.target, { v_forwarded.children() } });
        continue;
      }

      if (level_checker.on_step()) {
        return level_checker.termination_value;
      }

      ptr_uint64 low1, high1, low2, high2; // TODO: clean up...
      comp_policy::merge_data(low1,high1, low2,high2,
                              req.target[0], req.target[1], t_seek,
                              v1, v2,
                              req.node_carry[0][0], req.node_carry[0][1]);

      const typename comp_policy::label_t level = t_seek.label();
      comp_policy::compute_cofactor(req.target[0].on_level(level), low1, high1);
      comp_policy::compute_cofactor(req.target[1].on_level(level), low2, high2);

      if (comp_policy::resolve_request(comparison_pq_1, low1, low2)
          || comp_policy::resolve_request(comparison_pq_1, high1, high2)) {
        return comp_policy::early_return_value;
      }
    }

    return comp_policy::no_early_return_value;
  }

  //////////////////////////////////////////////////////////////////////////////
  /// Behaviour can be changed with the 'comp_policy'.
  ///
  /// - The 'resolve_terminals' function resolves the case of being given two terminals.
  ///
  /// - The 'resolve_request' function checks for early termination and places
  ///   new recursion requests in the priority queue if more recursions are needed.
  ///
  /// - If the constexpr 'request_capped_by_level_size' variable is set to true,
  ///   then the algorithm is guaranteed to only run in O(sort(N_1)) number of
  ///   I/Os.
  ///
  /// - The constexpr 'early_return_value' and 'no_early_return_value' change the
  ///   return value on early returns.
  ///
  /// This 'prod_policy' also should inherit (or provide) the general policy for
  /// the decision_diagram used (i.e. bdd_policy in bdd/bdd.h, zdd_policy in
  /// zdd/zdd.h and so on). This provides the following functions
  ///
  /// - compute_cofactor:
  ///   Used to change the low and high children retrieved from the input during
  ///   the product construction.
  //////////////////////////////////////////////////////////////////////////////
  template<typename comp_policy>
  bool comparison_check(const shared_levelized_file<node> &f1,
                        const shared_levelized_file<node> &f2,
                        const bool negate1,
                        const bool negate2)
  {
    // Compute amount of memory available for auxiliary data structures after
    // having opened all streams.
    //
    // We then may derive an upper bound on the size of auxiliary data
    // structures and check whether we can run them with a faster internal
    // memory variant.
    const size_t aux_available_memory = memory_available()
      // Input
      - 2*node_stream<>::memory_usage()
      // Level checker policy
      - comp_policy::level_check_t::memory_usage();

    constexpr size_t data_structures_in_pq_1 =
      comparison_priority_queue_1_t<ADIAR_LPQ_LOOKAHEAD, memory_mode_t::INTERNAL>::DATA_STRUCTURES;

    constexpr size_t data_structures_in_pq_2 =
      comparison_priority_queue_2_t<memory_mode_t::INTERNAL>::DATA_STRUCTURES;

    const size_t pq_1_internal_memory =
      (aux_available_memory / (data_structures_in_pq_1 + data_structures_in_pq_2)) * data_structures_in_pq_1;

    const size_t pq_2_internal_memory = aux_available_memory - pq_1_internal_memory;

    const size_t pq_1_memory_fits =
      comparison_priority_queue_1_t<ADIAR_LPQ_LOOKAHEAD, memory_mode_t::INTERNAL>::memory_fits(pq_1_internal_memory);

    const size_t pq_2_memory_fits =
      comparison_priority_queue_2_t<memory_mode_t::INTERNAL>::memory_fits(pq_2_internal_memory);

    const bool internal_only = memory_mode == memory_mode_t::INTERNAL;
    const bool external_only = memory_mode == memory_mode_t::EXTERNAL;

    const size_t pq_1_bound = comp_policy::level_check_t::pq1_upper_bound(f1, f2);

    const size_t max_pq_1_size = internal_only ? std::min(pq_1_memory_fits, pq_1_bound) : pq_1_bound;

    const size_t pq_2_bound = comp_policy::level_check_t::pq2_upper_bound(f1, f2);

    const size_t max_pq_2_size = internal_only ? std::min(pq_2_memory_fits, pq_2_bound) : pq_2_bound;

    // TODO: Only one element per node in pq_2, so maximum is width (or their product)!
    if(!external_only && max_pq_1_size <= no_lookahead_bound(comp_policy::lookahead_bound())) {
#ifdef ADIAR_STATS
      stats_equality.lpq.unbucketed += 1u;
#endif
      return __comparison_check<comp_policy,
                                comparison_priority_queue_1_t<0, memory_mode_t::INTERNAL>,
                                comparison_priority_queue_2_t<memory_mode_t::INTERNAL>>
        (f1, f2, negate1, negate2, pq_1_internal_memory, pq_2_internal_memory, max_pq_1_size);
    } else if(!external_only && max_pq_1_size <= pq_1_memory_fits
                             && max_pq_2_size <= pq_2_memory_fits) {
#ifdef ADIAR_STATS
      stats_equality.lpq.internal += 1u;
#endif
      return __comparison_check<comp_policy,
                                comparison_priority_queue_1_t<ADIAR_LPQ_LOOKAHEAD, memory_mode_t::INTERNAL>,
                                comparison_priority_queue_2_t<memory_mode_t::INTERNAL>>
        (f1, f2, negate1, negate2, pq_1_internal_memory, pq_2_internal_memory, max_pq_1_size);
    } else {
#ifdef ADIAR_STATS
      stats_equality.lpq.external += 1u;
#endif
      const size_t pq_1_memory = aux_available_memory / 2;
      const size_t pq_2_memory = pq_1_memory;

      return __comparison_check<comp_policy,
                                comparison_priority_queue_1_t<ADIAR_LPQ_LOOKAHEAD, memory_mode_t::EXTERNAL>,
                                comparison_priority_queue_2_t<memory_mode_t::EXTERNAL>>
        (f1, f2, negate1, negate2, pq_1_memory, pq_2_memory, max_pq_1_size);
    }
  }

  template<typename comp_policy>
  bool comparison_check(const dd &a, const dd &b)
  {
    return comparison_check<comp_policy>(a.file, b.file, a.negate, b.negate);
  }
}

#endif // ADIAR_INTERNAL_ALGORITHMS_PRED_H
