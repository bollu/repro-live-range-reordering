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

    auto *kills = isl_union_map_read_from_str(ctx, "{}");

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


    auto *domain = isl_union_set_read_from_str(ctx, " {[i, j] }");
    isl_schedule *sched = isl_schedule_from_domain(domain);

    {
        auto *new_sched = isl_union_map_read_from_str(ctx,
                "{"
                "S0[i, j] -> [j, i, 0];"
                "S1[i, j] -> [j, i, 1];"
                "S2[i, j] -> [j, i, 2];"
                "}");
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
    
    auto *access = isl_union_access_info_from_sink(isl_union_map_copy(may_reads));
    access = isl_union_access_info_set_kill(access, isl_union_map_copy(kills));
    access = isl_union_access_info_set_may_source(access, isl_union_map_copy(may_writes));
    access = isl_union_access_info_set_must_source(access, isl_union_map_copy(must_writes));
    access = isl_union_access_info_set_schedule(access, sched);
    std::cout << "\n\nACCESS: " << isl_union_access_info_to_str(access);

    auto *flow = isl_union_access_info_compute_flow(access);
    std::cout<<"\nFLOW: " << isl_union_flow_to_str(flow);

    // __isl_give isl_map *isl_map_power(__isl_take isl_map *map, int *exact);
    //isl_map *m = isl_map_read_from_str(ctx, "{ A[x] -> A[x] }");
    // app Cons nil xs = xs
    // app (Cons a b) xs = let b' = b ++ xs in Cons a b'
    // in:(nil, cons a b), | in:xs,   | out:nil, (cons a', cons b')
    //APP[ 0         1 2   | 3     ] |  OUT[4          5         6]
    //isl_map *m = isl_map_read_from_str(ctx, "{ A[0] -> A[0]; A[x] -> A[x + 1] : x > 0  }");
    // isl_map *m = isl_map_read_from_str(ctx, "{ a[x] -> a[x + 3]: x mod 3 = 0}");
    // 9k + 2 -> 9k + 4
    // 9k + 9 -> 9k + 7
    // 9k + 3 -> 9k + 5
    //
    //
    //TRANS: { a[x] -> a[o0] : (x) mod 7 = 6 and -4 + x <= o0 <= -3 + x; 
    //          a[x] -> a[-4 + x] : -5 + x <= 7*floor((x)/7) <= -4 + x; 
    // isl_map *m = isl_map_read_from_str(ctx, "{ a[x] -> a[x-4+0]: x mod 7 = 4; a[x] -> a[x-5+1]: x mod 7 = 5; a[x] -> a[x-6+2]: x mod 7 = 6; a[x] -> a[x-6+3]: x mod 7 = 6; \
    //         a[x] -> a[x-5-7+1]:x mod 7 = 5; a[x] -> a[x-6-7+2]: x mod 7 = 6 }");
    // std::cout << "built map\n";
    // isl_map *pow_ = isl_map_power(isl_map_copy(m), NULL);
    // isl_map *trans_ = isl_map_transitive_closure(m, NULL);


    // isl_printer *p = isl_printer_to_str(ctx);
    // isl_printer_print_map(p, pow_);
    // std::cout <<"\nPOWER: "<<  isl_printer_get_str(p);

    // isl_printer_free(p);
    // p = isl_printer_to_str(ctx);
    // isl_printer_print_map(p, trans_);
    // std::cout <<"\nTRANS: "<<isl_printer_get_str(p);


    // // ==================================
    // // TRANS: { a[x] -> a[o0] : (x) mod 7 = 6 and -4 + x <= o0 <= -3 + x; 
    // //          a[x] -> a[-4 + x] : -5 + x <= 7*floor((x)/7) <= -4 + x; 
    // //          a[x] -> a[-11 + x] : 7*floor((x)/7) <= -5 + x }

    // // CONSTRAINT 1
    // std::cout << "\n===========================\n";
    // isl_set *domain = isl_set_read_from_str(ctx, "{a[x]:  -5 + x <= 7*floor((x)/7) <= -4 + x and -20 <= x <= 20}");
    // std::cout << "\nDOMAIN: " << isl_set_to_str(domain);
    // isl_set_foreach_point(domain, print_point, NULL);
    // 
    // isl_set *app = isl_set_apply(domain, isl_map_copy(trans_));
    // std::cout<<"\nAPP: " << isl_set_to_str(app);
    // isl_set_foreach_point(app, print_point, NULL);

    // 
    // // CONSTRAINT 2
    // std::cout << "\n===========================\n";
    // domain = isl_set_read_from_str(ctx, "{a[x]:  7*floor((x)/7) <= -5 + x and -20 <= x <= 20}");
    // std::cout << "\nDOMAIN: " << isl_set_to_str(domain);
    // isl_set_foreach_point(domain, print_point, NULL);
    // 
    // app = isl_set_apply(domain, trans_);
    // std::cout<<"\nAPP: " << isl_set_to_str(app);
    // isl_set_foreach_point(app, print_point, NULL);
}

int main() {
    loop1();
}
