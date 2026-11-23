# EtaleHom M1 propagation (READY4.1)

The fresh O probe is `probes/mprwe/Original.lean`, using Lean 4.35.0 and
the READY4.1 kernel/analyzer from dataset commit `5ae674db0c7`. The current
import-closure revision is `15b8acba63e`. The expensive root is the
instantiated `hv` argument (root 2632) of
`derivedTensorHomShiftComparison_component`. It compares the stored
`IsEtaleHomTranspose X φ M v` proof against the instantiated expected
proposition; the raw heads are `IsEtaleHomTranspose` and `7`, and the first
divergence is at `root`. The displayed heads are summaries, not complete
expressions.

| Coverage/check | Fresh result |
|---|---:|
| O counters / analyzed calls | 3,180,470 / 3,180,470 |
| O counter root wall / comparison / reduction | 25,080.212 / 13,247.985 / 11,832.227 ms |
| Trace comparison exclusive | 23,299.515 ms |
| Aggregate / raw entered calls | 3,180,470 / 4,124 (0.130%) |
| M1 calls / exclusive / share | 2,390,795 / 23,235.154 ms / 99.724% |
| M2 / Matched / Unclassified share | 0.002% / 0.273% / 0.000% |

The calls equal the accepted READY3.2 O count. The M1 time share is
within the required 0.5 percentage-point tolerance. READY4.1 adds
observational transition/depth bookkeeping; counter and trace times are
separate runs and are not interchangeable. All label and depth aggregates
cover every call, including calls absent from the bounded raw stream.

## A2: propagation shape

M1 depth mean/median/p90/p99/max is
78.707/79/90/97/111. The narrowest bands holding 50% and 90% of M1
exclusive time are depths 71--83 and 63--92. M1 fan-out
mean/median/p90/max is 1.330/1/3/28. Its exact-count histogram grouped for
display is: 0: 767,999; 1: 949,645; 2: 255,285; 3: 243,978;
4--9: 157,254; 10+: 16,634. No depth was clamped. This is mixed
deep/wide propagation: costly nodes cluster near depth 79, while repeated
branching reaches 28 children.

Within the 4,124 raw entered calls, sampled M1 parents have 1,825 M1,
2,242 Matched, and 13 M2 child edges. These are sample counts, not
whole-root edge totals; READY4.1 does not aggregate edges by both parent
and child provenance.

## A3: transition matrix

These complete-root rows are parent branch/outcome by child kind. The first
five rows account for 22,097.666 ms, at least 94.8% of M1 exclusive time
even if every non-M1 microsecond were assigned to them. The instrument
does not split a row by child label or record row-specific mean fan-out.

| Parent | Child kind | Calls | Exclusive ms |
|---|---|---:|---:|
| projection | projection | 626,927 | 9,261.929 |
| application | argument | 1,268,544 | 6,402.993 |
| second_whnf | fallback | 255,588 | 3,409.944 |
| application | function-head | 589,257 | 1,759.095 |
| quick | dependent-body | 72,583 | 1,263.705 |

All 3,180,469 child edges sum to the root call count minus one. Projection
descent is the largest complete-root row; application argument descent is
second. Neither row can be called an exact M1-only total.

## A4: captured high-cost paths

The three highest-exclusive M1 calls in the root-filtered raw sample are
1026 (0.262 ms), 2634 (0.210 ms), and 2048 (0.200 ms). Their first
transitions share the same parent chain:

1. Root M0 `IsEtaleHomTranspose <> 7` becomes `Eq <> Eq` (call 3,
   dependent-body) when the binder is instantiated. This is the dependent
   body comparison in `is_def_eq_binding` (4.35.0 line 1479 in
   `M1P-KERNEL.md`); the instantiated body retains the mismatched `hv`
   lineage.
2. `Eq <> Eq` becomes `DFunLike.coe <> DFunLike.coe` (call 709,
   argument) through application congruence in `is_def_eq_app` (line 1628).
   Both displayed heads match, but the differing arguments carry the same
   first-divergence hashes and the child is M1.
3. `DFunLike.coe <> DFunLike.coe` becomes
   `EquivLike.coe <> EquivLike.coe` (call 710, fallback, reduced before
   child), then `Equiv.toFun` (711), `Equiv.invFun` (712), and
   `CategoryStruct.comp` (713). This is the WHNF/reduction continuation in
   `is_def_eq_core` (line 1909) and its second-WHNF path; the exposed pairs
   remain on the stored `hv` mismatch lineage.

The paths then differ. Call 1026 reaches
`MonoidalCategoryStruct.whiskerLeft` by an application argument child from
`Equiv.invFun` at depth 31. Call 2634 continues through `DFunLike.coe`,
`EquivLike.coe`, `Equiv.toFun`, and `Equiv.invFun` at depths 34--37. Call
2048 reaches `NatTrans.app` (argument), `NatTrans.proj` (function-head),
and `isRightDerivedFunctor_internalHomQhObj_comp_tensorLeft` (argument)
at depths 23--25. These branches are covered by `is_def_eq_app` (line
1628) and projection handling in `lazy_delta_proj_reduction` (line 1857).
The raw sample is 0.130% of the root, so these are the highest-cost
*captured* calls. The complete aggregate collapses 2,390,081 M1 calls
and 23,221.285 ms into the wildcard path
`root/binder_body[1]/argument[2]/argument[0]/argument[7]/argument[0]/*`.
READY4.1 cannot rank the global top 2--3 individual paths or their
complete inclusive subtree costs from that collapsed path and bounded
raw stream.

## C: M0-preserving cut point

The candidate is the dependent endpoint/domain beneath `hv`. The existing
`O1-hv-aligned` source transports the whole `hv` proposition. Its type is
the instantiated argument of the same dependent consumer; changing it
changes the expected proposition at the root and removes the original M0.
Keeping the original `hv` type while replacing only the dependent child
would require a term at a different instantiated endpoint type, so that
candidate is not a type-correct local replacement. No valid O-cut exists
at this selected point; no causal cut-point speedup is claimed.

The analyzer's missing label-specific transition rows, row mean fan-out,
whole-root label-edge counts, and complete global path ranking are recorded
here as instrumentation limits. The kernel patch was not changed.
