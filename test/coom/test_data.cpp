#include <coom/data.cpp>

using namespace coom;

go_bandit([]() {
    describe("COOM: Data", []() {

        describe("Nil", [&](){
            it("should recognise Nil (unflagged)", [&]() {
                auto some_value = NIL;
                AssertThat(is_nil(some_value), Is().True());
              });

            it("should recognise Nil (flagged)", [&]() {
                auto some_value = flag(NIL);
                AssertThat(is_nil(some_value), Is().True());
              });


            it("can see whether the flag is set", [&]() {
                AssertThat(is_flagged(flag(NIL)), Is().True());
              });

            it("can see whether the flag is not set", [&]() {
                AssertThat(is_flagged(NIL), Is().False());
              });
          });

        describe("Sink Ptr", [&](){
            it("should store and retrieve value", [&]() {
                ptr_t p = create_sink_ptr(true);
                AssertThat(value_of(p), Is().True());

                p = create_sink_ptr(false);
                AssertThat(value_of(p), Is().False());
              });

            it("should recognise Sinks as such", [&]() {
                ptr_t sink_f = create_sink_ptr(false);
                ptr_t sink_t = create_sink_ptr(true);

                AssertThat(is_sink_ptr(sink_f), Is().True());
                AssertThat(is_sink_ptr(sink_t), Is().True());
              });

            it("should not be confused with Node Ptr (unflagged)", [&]() {
                ptr_t arc_node_max = create_node_ptr(MAX_LABEL,MAX_ID);
                AssertThat(is_sink_ptr(arc_node_max), Is().False());

                ptr_t arc_node_min = create_node_ptr(0,0);
                AssertThat(is_sink_ptr(arc_node_min), Is().False());

                ptr_t arc_node = create_node_ptr(42,18);
                AssertThat(is_sink_ptr(arc_node), Is().False());
              });

            it("should not be confused with Node Ptr (flagged)", [&]() {
                ptr_t arc_node_max = flag(create_node_ptr(MAX_LABEL,MAX_ID));
                AssertThat(is_sink_ptr(arc_node_max), Is().False());

                ptr_t arc_node_min = flag(create_node_ptr(0,0));
                AssertThat(is_sink_ptr(arc_node_min), Is().False());

                ptr_t arc_node = flag(create_node_ptr(42,18));
                AssertThat(is_sink_ptr(arc_node), Is().False());
              });

            it("can see whether the flag is set", [&]() {
                ptr_t p = flag(create_sink_ptr(false));
                AssertThat(is_flagged(p), Is().True());

                p = flag(create_sink_ptr(false));
                AssertThat(is_flagged(p), Is().True());
              });

            it("can see whether the flag is not set", [&]() {
                ptr_t p = create_sink_ptr(true);
                AssertThat(is_flagged(p), Is().False());

                p = create_sink_ptr(false);
                AssertThat(is_flagged(p), Is().False());
              });

            it("should not be confused with Nil (unflagged)", [&]() {
                AssertThat(is_sink_ptr(NIL), Is().False());
              });

            it("should not be confused with Nil (flagged)", [&]() {
                AssertThat(is_sink_ptr(flag(NIL)), Is().False());
              });

            it("should take up 8 bytes of memory", [&]() {
                ptr_t sink = create_sink_ptr(false);
                AssertThat(sizeof(sink), Is().EqualTo(8u));
              });
          });

        describe("Node Ptr", [&]() {
            it("should store and retrieve 42 label Ptr (unflagged)", [&]() {
                ptr_t p = create_node_ptr(42,2);
                AssertThat(label_of(p), Is().EqualTo(42));
              });

            it("should store and retrieve 21 label Ptr (unflagged)", [&]() {
                ptr_t p = create_node_ptr(21,2);
                AssertThat(label_of(p), Is().EqualTo(21));
              });

            it("should store and retrieve MAX label Ptr (unflagged)", [&]() {
                ptr_t p = create_node_ptr(MAX_LABEL, MAX_ID);
                AssertThat(label_of(p), Is().EqualTo(MAX_LABEL));
              });

            it("should store and retrieve 42 label Ptr (flagged)", [&]() {
                ptr_t p = flag(create_node_ptr(42,2));
                AssertThat(label_of(p), Is().EqualTo(42));
              });

            it("should store and retrieve 21 label Ptr (flagged)", [&]() {
                ptr_t p = flag(create_node_ptr(21,2));
                AssertThat(label_of(p), Is().EqualTo(21));
              });

            it("should store and retrieve MAX label Ptr (flagged)", [&]() {
                ptr_t p = create_node_ptr(MAX_LABEL, MAX_ID);
                AssertThat(label_of(p), Is().EqualTo(MAX_LABEL));
              });

            it("should store and retrieve 42 id (unflagged)", [&]() {
                ptr_t p = create_node_ptr(2,42);
                AssertThat(id_of(p), Is().EqualTo(42));
              });

            it("should store and retrieve 21 id (unflagged)", [&]() {
                ptr_t p = create_node_ptr(2,21);
                AssertThat(id_of(p), Is().EqualTo(21));
              });

            it("should store and retrieve MAX id (unflagged)", [&]() {
                ptr_t p = create_node_ptr(MAX_LABEL, MAX_ID);
                AssertThat(id_of(p), Is().EqualTo(MAX_ID));
              });

            it("should store and retrieve 42 id (flagged)", [&]() {
                ptr_t p = flag(create_node_ptr(2,42));
                AssertThat(id_of(p), Is().EqualTo(42));
              });

            it("should store and retrieve 21 id (flagged)", [&]() {
                ptr_t p = flag(create_node_ptr(2,21));
                AssertThat(id_of(p), Is().EqualTo(21));
              });

            it("should store and retrieve MAX id (flagged)", [&]() {
                ptr_t p = create_node_ptr(MAX_LABEL, MAX_ID);
                AssertThat(id_of(p), Is().EqualTo(MAX_ID));
              });

            it("should create uid without being flagged", [&]() {
                coom::uid_t n_uid = create_node_uid(53, 4);
                AssertThat(is_flagged(n_uid), Is().False());

                n_uid = create_node_uid(42, 9);
                AssertThat(is_flagged(n_uid), Is().False());
              });

            it("should sort Sink arcs after Node Ptr (unflagged)", [&]() {
                // Create a node pointer with the highest possible raw value
                ptr_t p_node = create_node_ptr(MAX_LABEL,MAX_ID);

                // Create a sink pointer with the lowest raw value
                ptr_t p_sink = create_sink_ptr(false);

                AssertThat(p_node < p_sink, Is().True());
                AssertThat(flag(p_node) < p_sink, Is().True());
              });

            it("should sort Sink arcs after Node Ptr (flagged)", [&]() {
                // Create a node pointer with the highest possible raw value
                ptr_t p_node = flag(create_node_ptr(MAX_LABEL,MAX_ID));

                // Create a sink pointer with the lowest raw value
                ptr_t p_sink = create_sink_ptr(false);

                AssertThat(p_node < p_sink, Is().True());
                AssertThat(flag(p_node) < p_sink, Is().True());
              });

            it("should recognise Node Ptr (unflagged)", [&]() {
                ptr_t p_node_max = create_node_ptr(MAX_LABEL,MAX_ID);
                AssertThat(is_node_ptr(p_node_max), Is().True());

                ptr_t p_node_min = create_node_ptr(0,0);
                AssertThat(is_node_ptr(p_node_min), Is().True());

                ptr_t p_node = create_node_ptr(42,18);
                AssertThat(is_node_ptr(p_node), Is().True());
              });

            it("should recognise Node Ptr (flagged)", [&]() {
                ptr_t p_node_max = flag(create_node_ptr(MAX_LABEL,MAX_ID));
                AssertThat(is_node_ptr(p_node_max), Is().True());

                ptr_t p_node_min = flag(create_node_ptr(0,0));
                AssertThat(is_node_ptr(p_node_min), Is().True());

                ptr_t p_node = flag(create_node_ptr(42,18));
                AssertThat(is_node_ptr(p_node), Is().True());
              });

            it("should not be confused with Sinks", [&]() {
                ptr_t sink_f = create_sink_ptr(false);
                ptr_t sink_t = create_sink_ptr(true);

                AssertThat(is_node_ptr(sink_f), Is().False());
                AssertThat(is_node_ptr(sink_t), Is().False());
              });

            it("should not be confused with Nil (unflagged)", [&]() {
                AssertThat(is_node_ptr(NIL), Is().False());
              });

            it("should not be confused with Nil (flagged)", [&]() {
                AssertThat(is_node_ptr(flag(NIL)), Is().False());
              });

            it("can recognise the flag is set", [&]() {
                ptr_t p = flag(create_node_ptr(42,2));
                AssertThat(is_flagged(p), Is().True());

                p = flag(create_node_ptr(17,3));
                AssertThat(is_flagged(p), Is().True());
              });

            it("can recognise the flag is not set", [&]() {
                ptr_t p = create_node_ptr(42,2);
                AssertThat(is_flagged(p), Is().False());

                p = create_node_ptr(17,3);
                AssertThat(is_flagged(p), Is().False());
              });

            it("should sort by label, then by id", [&]() {
                auto node_1_2 = create_node_ptr(1,2);
                auto node_2_1 = create_node_ptr(2,1);
                auto node_2_2 = create_node_ptr(2,2);

                AssertThat(node_1_2 < node_2_1, Is().True());
                AssertThat(node_2_1 < node_2_2, Is().True());
              });

            it("should take up 8 bytes of memory", [&]() {
                auto node_ptr = create_node_ptr(42,2);
                AssertThat(sizeof(node_ptr), Is().EqualTo(8u));
              });
          });

        describe("Nodes", [&]() {
            it("should sort by label, then by id", [&]() {
                auto sink_f = create_sink_ptr(false);
                auto sink_t = create_sink_ptr(true);

                auto node_1_2 = create_node(1,2,sink_f,sink_t);
                auto node_2_1 = create_node(2,1,sink_t,sink_f);

                AssertThat(node_1_2 < node_2_1, Is().True());
                AssertThat(node_2_1 > node_1_2, Is().True());

                auto node_2_2 = create_node(2,2,sink_f,sink_f);

                AssertThat(node_2_1 < node_2_2, Is().True());
                AssertThat(node_2_2 > node_2_1, Is().True());
              });

            it("should be equal by their content", [&]() {
                auto sink_f = create_sink_ptr(false);
                auto sink_t = create_sink_ptr(true);

                auto node_1_v1 = create_node(42,2,sink_f,sink_t);
                auto node_1_v2 = create_node(42,2,sink_f,sink_t);

                AssertThat(node_1_v1 == node_1_v2, Is().True());
                AssertThat(node_1_v1 != node_1_v2, Is().False());
              });

            it("should be unequal by their content", [&]() {
                auto sink_f = create_sink_ptr(false);
                auto sink_t = create_sink_ptr(true);

                auto node_1 = create_node(42,2,sink_f,sink_t);
                auto node_2 = create_node(42,2,sink_f,sink_f);
                auto node_3 = create_node(42,3,sink_f,sink_t);
                auto node_4 = create_node(21,2,sink_f,sink_t);

                AssertThat(node_1 == node_2, Is().False());
                AssertThat(node_1 != node_2, Is().True());

                AssertThat(node_1 == node_3, Is().False());
                AssertThat(node_1 != node_3, Is().True());

                AssertThat(node_1 == node_4, Is().False());
                AssertThat(node_1 != node_4, Is().True());
              });

            it("should be a POD", [&]() {
                AssertThat(std::is_pod<node>::value, Is().True());
              });

            it("should take up 24 bytes of memory", [&]() {
                ptr_t node_ptr = create_node_ptr(42,2);
                ptr_t sink = create_sink_ptr(false);
                node node = create_node(1,
                                        8,
                                        node_ptr,
                                        sink);

                AssertThat(sizeof(node), Is().EqualTo(3u * 8u));
              });
          });

        describe("Sink nodes", [&]() {
            it("should recognise sink nodes as such", [&]() {
                node sink_node_T = create_sink(true);
                AssertThat(is_sink(sink_node_T), Is().True());

                node sink_node_F = create_sink(false);
                AssertThat(is_sink(sink_node_F), Is().True());
              });

            it("should recognise normal nodes not as sink nodes", [&]() {
                node node_1 = create_node(42,2,
                                          create_sink_ptr(false),
                                          create_sink_ptr(true));
                AssertThat(is_sink(node_1), Is().False());

                node node_2 = create_node(0,0,
                                          create_sink_ptr(true),
                                          node_1.uid);
                AssertThat(is_sink(node_2), Is().False());
              });

            it("should retrive value of a sink node", [&]() {
                node sink_node_T = create_sink(true);
                AssertThat(value_of(sink_node_T), Is().True());

                node sink_node_F = create_sink(false);
                AssertThat(value_of(sink_node_F), Is().False());
              });
          });

        describe("Arcs", [&]() {
            it("should be equal by their content", [&]() {
                ptr_t source = create_node_ptr(4,2);
                ptr_t target = create_node_ptr(42,3);

                arc arc_1 = { source, target };
                arc arc_2 = { source, target };

                AssertThat(arc_1 == arc_2, Is().True());
                AssertThat(arc_1 != arc_2, Is().False());
              });

            it("should unequal by their content", [&]() {
                ptr_t node_ptr_1 = create_node_ptr(4,2);
                ptr_t node_ptr_2 = create_node_ptr(4,3);
                ptr_t node_ptr_3 = create_node_ptr(3,2);

                arc arc_1 = { node_ptr_1, node_ptr_2 };
                arc arc_2 = { node_ptr_1, node_ptr_3 };

                AssertThat(arc_1 == arc_2, Is().False());
                AssertThat(arc_1 != arc_2, Is().True());

                arc arc_3 = { node_ptr_1, node_ptr_2 };
                arc arc_4 = { flag(node_ptr_1), node_ptr_2 };

                AssertThat(arc_3 == arc_4, Is().False());
                AssertThat(arc_3 != arc_4, Is().True());

                arc arc_5 = { node_ptr_1, node_ptr_2 };
                arc arc_6 = { node_ptr_3, node_ptr_2 };

                AssertThat(arc_5 == arc_6, Is().False());
                AssertThat(arc_5 != arc_6, Is().True());
              });

            it("should recognise low arcs from bit-flag on source", [&]() {
                ptr_t node_ptr_1 = create_node_ptr(4,2);
                ptr_t node_ptr_2 = create_node_ptr(4,3);

                arc arc_low = { node_ptr_1, node_ptr_2 };
                AssertThat(is_high(arc_low), Is().False());
              });

            it("should recognise high arcs from bit-flag on source", [&]() {
                ptr_t node_ptr_1 = create_node_ptr(4,2);
                ptr_t node_ptr_2 = create_node_ptr(4,3);

                arc arc_high = { flag(node_ptr_1), node_ptr_2 };
                AssertThat(is_high(arc_high), Is().True());
              });

            it("should be a POD", [&]() {
                AssertThat(std::is_pod<arc>::value, Is().True());
              });

            it("should take up 16 bytes of memory", [&]() {
                ptr_t node_ptr = create_node_ptr(42,2);
                ptr_t sink = create_sink_ptr(false);
                arc arc = { node_ptr, sink };

                AssertThat(sizeof(arc), Is().EqualTo(2u * 8u));
              });
          });

        describe("Converters", [&]() {
            it("should extract low arc from node", [&]() {
                node node = create_node(7,42,
                                        create_node_ptr(8,21),
                                        create_node_ptr(9,8));

                arc arc = low_arc_of(node);

                AssertThat(label_of(arc.source), Is().EqualTo(7));
                AssertThat(id_of(arc.source), Is().EqualTo(42));
                AssertThat(label_of(arc.target), Is().EqualTo(8));
                AssertThat(id_of(arc.target), Is().EqualTo(21));
              });

            it("should extract high arc from node", [&]() {
                node node = create_node(11,13,
                                        create_node_ptr(8,21),
                                        create_node_ptr(9,8));

                arc arc = high_arc_of(node);

                AssertThat(label_of(arc.source), Is().EqualTo(11));
                AssertThat(id_of(arc.source), Is().EqualTo(13));
                AssertThat(label_of(arc.target), Is().EqualTo(9));
                AssertThat(id_of(arc.target), Is().EqualTo(8));
              });

            it("should combine low and high arcs into single node", [&]() {
                arc low_arc = { create_node_ptr(17,42), create_node_ptr(9,8) };
                arc high_arc = { flag(create_node_ptr(17,42)), create_node_ptr(8,21) };

                node node = node_of(low_arc, high_arc);

                AssertThat(label_of(node), Is().EqualTo(17));
                AssertThat(id_of(node), Is().EqualTo(42));

                AssertThat(label_of(node.low), Is().EqualTo(label_of(low_arc.target)));
                AssertThat(id_of(node.low), Is().EqualTo(id_of(low_arc.target)));

                AssertThat(label_of(node.high), Is().EqualTo(label_of(high_arc.target)));
                AssertThat(id_of(node.high), Is().EqualTo(id_of(high_arc.target)));
              });
          });
      });
  });