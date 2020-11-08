#ifndef COOM_EVALUATE_H
#define COOM_EVALUATE_H

#include <tpie/file_stream.h>

#include <coom/data.h>
#include <coom/file.h>

namespace coom
{
  //////////////////////////////////////////////////////////////////////////////
  /// \brief Evaluate an OBDD according to an assignment
  ///
  /// \param nodes The node-based OBDD graph in reverse topological order.
  /// \return Sink-value after traversal according to the assignment.
  //////////////////////////////////////////////////////////////////////////////
  bool bdd_eval(const node_file &nodes, const assignment_file &assignment);
}

#endif // COOM_EVALUATE_H