#ifndef ADIAR_ZDD_SET_OP_H
#define ADIAR_ZDD_SET_OP_H

#include <adiar/data.h>
#include <adiar/zdd/zdd.h>

namespace adiar
{
  //////////////////////////////////////////////////////////////////////////////
  /// \brief Given two ZDDs creates one as per an operator.
  ///
  /// \param zdd_i     ZDD to apply with the other.
  ///
  /// \param op        Binary boolean operator to be applied.
  ///
  /// \return Product construction of the two that represents the boolean
  ///         operator applied to the two family of sets.
  //////////////////////////////////////////////////////////////////////////////
  // TODO: Should this be exposed to the end user?
  __zdd zdd_binop(const zdd &zdd_1, const zdd &zdd_2, const bool_op &op);

  //////////////////////////////////////////////////////////////////////////////
  /// \brief Given two ZDDs creates a new ZDD that represents the union of their
  /// family of sets.
  //////////////////////////////////////////////////////////////////////////////
  __zdd zdd_union(const zdd &zdd_1, const zdd &zdd_2);

  //////////////////////////////////////////////////////////////////////////////
  /// \brief Given two ZDDs creates a new ZDD that represents the intersection
  /// of their family of sets.
  //////////////////////////////////////////////////////////////////////////////
  __zdd zdd_intsec(const zdd &zdd_1, const zdd &zdd_2);

  //////////////////////////////////////////////////////////////////////////////
  /// \brief Given two ZDDs creates a new ZDD that represents the difference
  /// between their family of sets.
  //////////////////////////////////////////////////////////////////////////////
  __zdd zdd_diff(const zdd &zdd_1, const zdd &zdd_2);

  //////////////////////////////////////////////////////////////////////////////
  /// \brief Given a ZDD for a Family F and a domain D (label_file), computes
  /// the complement of F within D faster than computing
  /// `zdd_diff(zdd_powerset(D), S)``.
  ///
  /// The label_file is expected to be given in-order.
  //////////////////////////////////////////////////////////////////////////////
  __zdd zdd_complement(const zdd &dd, const label_file &dom);

}

#endif // ADIAR_ZDD_SET_OP_H
