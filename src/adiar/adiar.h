#ifndef ADIAR_H
#define ADIAR_H

#include <string>

////////////////////////////////////////////////////////////////////////////////
/// ADIAR Core
#include <adiar/data.h>
#include <adiar/file.h>
#include <adiar/file_stream.h>
#include <adiar/file_writer.h>
#include <adiar/statistics.h>

////////////////////////////////////////////////////////////////////////////////
/// ADIAR BDD
#include <adiar/bdd/bdd.h>

// Simple constructors
#include <adiar/bdd/build.h>

// Algorithms
#include <adiar/bdd/apply.h>
#include <adiar/bdd/assignment.h>
#include <adiar/bdd/count.h>
#include <adiar/bdd/evaluate.h>
#include <adiar/bdd/if_then_else.h>
#include <adiar/bdd/negate.h>
#include <adiar/bdd/restrict.h>
#include <adiar/bdd/quantify.h>

////////////////////////////////////////////////////////////////////////////////
/// Statistics
#include <adiar/statistics.h>

////////////////////////////////////////////////////////////////////////////////
/// Debugging
#include <adiar/dot.h>

namespace adiar
{
  //////////////////////////////////////////////////////////////////////////////
  /// \brief Initiates ADIAR with the given amount of memory (given in bytes)
  ///
  /// TODO: Should we provide an option to change the maximum variable number?
  ///       What about opening files by others? Should we store that somehow in
  ///       the first element of the meta stream?
  //////////////////////////////////////////////////////////////////////////////
  void adiar_init(size_t memory_limit_bytes, std::string temp_dir = "");

  //////////////////////////////////////////////////////////////////////////////
  /// \brief Changes the memory limit used by ADIAR (given in bytes)
  //////////////////////////////////////////////////////////////////////////////
  void set_limit(size_t memory_limit_bytes);

  //////////////////////////////////////////////////////////////////////////////
  /// \brief Closes and cleans up everything by ADIAR
  //////////////////////////////////////////////////////////////////////////////
  void adiar_deinit();
}

#endif // ADIAR_H
