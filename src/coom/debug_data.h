#ifndef COOM_DEBUG_DATA_H
#define COOM_DEBUG_DATA_H

#include <tpie/tpie.h>
#include <tpie/file_stream.h>

#include <stdint.h>

#include "data.h"

namespace coom { namespace debug {
    void print_nil_ptr();
    void print_node_ptr(uint64_t n);
    void print_sink_ptr(uint64_t n);

    void print_child(uint64_t n);

    void print_node(const node& n);
    void println_node(const node& n);

    void print_arc(const arc& a);
    void println_arc(const arc& a);

    void print_file_stream(tpie::file_stream<node>& nodes);
    void print_file_stream(tpie::file_stream<node>& nodes, std::string name);
    void println_file_stream(tpie::file_stream<node>& nodes);
    void println_file_stream(tpie::file_stream<node>& nodes, std::string name);
    void print_file_stream(tpie::file_stream<arc>& arcs);
    void print_file_stream(tpie::file_stream<arc>& arcs, std::string name);
    void println_file_stream(tpie::file_stream<arc>& arcs);
    void println_file_stream(tpie::file_stream<arc>& arcs, std::string name);
  }
}

#endif // COOM_DEBUG_DATA_H