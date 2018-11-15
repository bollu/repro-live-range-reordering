#include <isl/set.h>
#include <isl/map.h>
#include <isl/union_map.h>
#include <isl/union_set.h>
#include <iostream>
#include <isl/flow.h>
#include <isl/aff.h>

using namespace std;

isl_stat print_point(isl_point *pt, void *data) {
    std::cout <<"\n - pt: " << isl_point_to_str(pt);
    return isl_stat_ok;
}

//  Input dependences, i.e., pairs of statement instances that (may) read the
//  same value from the same memory element, can be computed by first taking
//  the may-reads as sinks and may-sources and the may-writes (and kills) as
//  the must-sources and then removing the dependences that have a may-write
//  (or kill) as source.
// 
// In PPCG, when the live-range reordering described in this paper is not
// enabled, the following dependences are computed.  The first application of
// dependence analysis takes the tagged may-reads as sinks, the tagged
// may-writes as may-sources and the union of the tagged must-writes and the
// tagged kills as must-sources. The domain of the tagged kills is subsequently
// removed from the result. The difference forms what are called the tagged
// flow dependences. That is, there is a flow dependence from a may-write to a
// later mayread as long as there is no intermediate must-write or kill.  The
// sinks for which no corresponding must-source is found during the dependence
// analysis are considered to be the livein accesses. That is, the live-in
// accesses are the may-reads that may read a value that was written before the
// start of the program fragment under analysis
//
// The second application takes the may-writes as sinks, the
// must-writes as must-sources and the union of the may-reads
// and the may-writes as may-sources. The resulting dependences
// are called the false dependences. Those with a mayread
// as source are also known as anti-dependences, while
// those with a may-write as source are also known as output
// dependences.
//
// The third application takes as may-sources the tagged
// may-writes and as sinks the union of the tagged must-writes
// and the kills. The domain of the resulting dependences consists
// of the pairs of statement instances and reference identifiers
// that access elements that are definitely overwritten or
// killed. Specializing to the shared array elements results in
// may-writes that write a value that is definitely overwritten
// or killed. Removing these from the set of all may-writes results
// in the may-writes that write a value that may survive
// the program fragment under analysis. These are called the
// live-out accesses. They are useful for dead code elimination
// (Verdoolaege 2015) and for determining which values should
// be copied back from the device to the host in the code generated
// by PPCG. If only the marked fragment of Listing 1 is
// analyzed, th
//
// CONDITIONAL VALIDITY CONSTRAINTS:
// Clearly, the intended use of conditional validity constraints
// in case of live-range reordering is for the conditions to be set
// to the live-ranges and the conditioned validity constraints to
// be set to the anti-dependences. In the running example, the


void loop1() {
    // DO j=0,1
    //     DO i=0,1
    //         S0: t = A(i,j-1) //R0 read
    //         S1: IF (t < 0) t = 0
    //         S2: A(i,j) = t
    //     ENDDO
    // ENDDO

    isl_ctx *ctx = isl_ctx_alloc();
    isl_printer *p =  NULL; 

    /*
    auto *may_reads = isl_union_map_read_from_str(ctx, 
            "{"
            "[S0[j, i] -> R0[]] -> A[i, j-1];"
            "[S1[i, j] -> R1[]] -> T[];"
            "[S2[i, j] -> R1[]] -> T[];"
            "}");
    // isl_map *may_writes = isl_map_read_from_str(ctx, "{}");
    auto *must_writes = isl_union_map_read_from_str(ctx,
            "{"
            "[S1[j, i] -> R1[]] -> T[];"
            "[S2[j, i] -> W0[]] -> A[i, j];"
            "}");


    auto *may_writes = isl_union_map_read_from_str(ctx,
            "{"
            "[S1[j, i] -> W2[]] -> A[i, j];"
            "}");

    auto *kills = isl_union_map_read_from_str(ctx, "{:1=0}");
    */

    auto *may_reads = isl_union_map_read_from_str(ctx, 
            "{"
            "S0[j, i] -> A[i, j-1];"
            "S1[i, j] -> T[];"
            "S2[i, j] -> T[];"
            "}");
    // isl_map *may_writes = isl_map_read_from_str(ctx, "{}");
    auto *must_writes = isl_union_map_read_from_str(ctx,
            "{"
            "S1[j, i] -> T[];"
            "S2[j, i] -> A[i, j];"
            "}");


    auto *may_writes = isl_union_map_read_from_str(ctx,
            "{"
            "S1[j, i] -> A[i, j];"
            "}");

    auto *kills = isl_union_map_read_from_str(ctx, "{:1=0}");

    p = isl_printer_to_str(ctx);
    isl_printer_print_union_map(p, may_reads);
    std::cout <<"\n may reads: "<<  isl_printer_get_str(p);
    isl_printer_free(p);


    p = isl_printer_to_str(ctx);
    isl_printer_print_union_map(p, must_writes);
    std::cout <<"\n must writes: "<<  isl_printer_get_str(p);
    isl_printer_free(p);

    p = isl_printer_to_str(ctx);
    isl_printer_print_union_map(p, may_writes);
    std::cout <<"\n may writes: "<<  isl_printer_get_str(p);
    isl_printer_free(p);


    auto *domain = isl_union_set_read_from_str(ctx, " {[i, j, k]}");
    isl_schedule *sched = nullptr;

    {
        auto *new_sched = isl_union_map_read_from_str(ctx,
                "{"
                "S0[i, j] -> [j, i, 0];"
                "S1[i, j] -> [j, i, 1];"
                "S2[i, j] -> [j, i, 2];"
                "}");
        sched =
            isl_schedule_from_domain(isl_union_map_domain(isl_union_map_copy(new_sched)));
        sched = isl_schedule_insert_partial_schedule(sched, 
          isl_multi_union_pw_aff_from_union_map(new_sched));
    }


    std::cout << "\nSCHEDULE: " << isl_schedule_to_str(sched);



    // Data 1
    // ------
    // SINK: tagged may read
    // MAY SOURCE: tagged may writes
    // MUST SOURCE: tagged must writes U tagged kills
    // OUTPUT: FLOW
    // OUTPUT': FLOW - tagged kills
    // tagged flow dependence: 
    //     may write ---> mayread, as long as there is no
    //     intermediate must write or kill
    
    {
        std::cout << "\n\n*** FLOW 1 (FLOW / RAW)";
        auto *access = isl_union_access_info_from_sink(isl_union_map_copy(may_reads));
        access = 
            isl_union_access_info_set_may_source(access, isl_union_map_copy(may_writes));
        access = 
            isl_union_access_info_set_must_source(access, isl_union_map_copy(must_writes));
        access = 
            isl_union_access_info_set_schedule(access, isl_schedule_copy(sched));
        std::cout << "\n\nACCESS: " << isl_union_access_info_to_str(access);

        auto *flow = isl_union_access_info_compute_flow(access);
        std::cout<<"\n\nFLOW: " << isl_union_flow_to_str(flow);
    }


    // Data 2
    // ------
    // SINK: may writes
    // MAY SOURCE: may read U may write
    // MUST SOURCE: must writes
    // OUTPUT: FALSE DEPENDENCES (WAR + WAW)
    // OUTPUT': FLOW - tagged kills
    // tagged flow dependence: 
    //     may write ---> mayread, as long as there is no
    //     intermediate must write or kill
    {
        std::cout << "\n\n*** FLOW 2 (FALSE DEPENDENCES / WAR + WAW)";
        auto *access = isl_union_access_info_from_sink(isl_union_map_copy(may_writes));
        access = 
            isl_union_access_info_set_may_source(access, 
                    isl_union_map_union(isl_union_map_copy(may_writes),
                        isl_union_map_copy(may_reads)));
        access = 
            isl_union_access_info_set_must_source(access, isl_union_map_copy(must_writes));
        access = 
            isl_union_access_info_set_schedule(access, isl_schedule_copy(sched));
        std::cout << "\n\nACCESS: " << isl_union_access_info_to_str(access);

        auto *flow = isl_union_access_info_compute_flow(access);
        std::cout<<"\n\nFLOW: " << isl_union_flow_to_str(flow);
    }




}

int main() {
    loop1();
}
