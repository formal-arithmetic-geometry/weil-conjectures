# FiniteBaseChange M1 propagation (READY4.1)

Fresh O is `probes/mprwe/Original.lean` on Lean 4.35.0, current import
revision `15b8acba63e`, READY4.1 kernel/analyzer revision `5ae674db0c7`.
The expensive original root is 16563: the dependent `hb` argument of
`transport_from_unit`, whose expected proposition uses the ordinary
site/right-square provider while the supplied `h` carries the ProEt
provider. The raw root heads both print `7`; its first structural
divergence is at `root/body/fn/fn/arg/fn/fn/fn/arg/fn/fn/fn/arg/fn`.
These printed heads are summaries, not full expressions.

| Coverage/check | Fresh result |
|---|---:|
| O counters / analyzed calls | 239,340,712 / 239,340,712 |
| O counter root wall / comparison / reduction | 744,636.581 / 744,578.605 / 57.976 ms |
| Trace comparison exclusive | 980,990.925 ms |
| Aggregate / raw entered calls | 239,340,712 / 3,828 (0.002%) |
| M1 calls / exclusive / share | 130,197,227 / 715,935.252 ms / 72.981% |
| M2 / Matched / Unclassified share | 25.478% / 1.542% / 0.000% |

The root and all label call counts equal the accepted READY3.2 run.
The M1 time share differs by more than 0.5 percentage points; this is
exclusively a time-weighting difference, consistent with READY4.1's
extra branch/depth bookkeeping and run-to-run variation in the mixed
failure path. Counter and trace timings are separate runs. The
aggregate labels and depth rows include every call, independently of
the bounded raw trace.

## A2: propagation shape

M1 depth mean/median/p90/p99/max is 74.992/75/79/80/87.
The narrowest bands holding 50% and 90% of M1 exclusive time are
depths 71--74 and 69--78. M1 fan-out mean/median/p90/max is
1.081/1/1/21. Its count histogram is 0: 20,705,452;
1: 105,697,962; 2: 2,241; 3: 1,848; 4--9: 1,321,435;
10+: 2,468,289. No depth was clamped. This is mixed propagation:
most M1 calls form a deep unary chain near depth 75, while millions
of nodes branch to ten or more children.

In the 3,828 raw entered calls, sampled M1 parents have 2,359 M1,
959 Matched, and 257 M2 child edges. These are sample counts, not
whole-root edge totals; the patch does not aggregate edges by both
parent and child label.

## A3: transition matrix

The five largest complete-root rows total 955,298.343 ms. Even if all
265,055.673 ms of non-M1 time fell in these rows, they would still
contain at least 96.4% of M1 time. The rows cover all labels;
READY4.1 does not emit per-row M1 child counts or mean child fan-out.

| Parent outcome/branch | Child kind | Calls | Exclusive ms |
|---|---|---:|---:|
| failure | projection | 98,780,391 | 293,296.879 |
| lazy_delta | dependent-body | 19,746,208 | 265,758.651 |
| failure | field | 39,536,116 | 221,066.630 |
| failure | argument | 48,903,475 | 121,585.524 |
| failure | function-head | 30,997,049 | 53,590.659 |

The matrix has 239,340,711 child calls, equal to the root count minus
one. `failure` records a parent's final outcome rather than the
specific branch that initiated each child. The raw M1-to-M1 sample
contains argument (987), projection (585), and function-head (382)
children. EtaleHom and the Cone have projection descent as their
largest complete-root row, while NativePullTensor emphasizes application
congruence (`M1P-KERNEL.md`). Here M2 contributes 25.478% of time,
and the largest rows include failure/projection and dependent-body
work. The same primary strategy cannot be certified as M1-dominant
without label-specific transition rows.

## C: dependent `hb` cut point

O's selected high-cost M1 region follows the `hb` proposition through
`CategoryStruct.comp`, `ModuleCat.Hom._mkInternal`,
`LinearMap.comp`, and `PresheafOfModules.proj`; the top captured M1
calls are `Add.add` (call 3136, 1.009 ms) and two
`PresheafOfModules.proj` nodes (calls 1973 and 125, 0.273 and
0.244 ms). The `hb := h` argument is checked against a dependent
proposition whose endpoints contain the ordinary and ProEt provider
choices. Replacing the provider inside that proposition changes the
expected type and the first M0 pair; keeping `h` at its original type
leaves the selected comparison intact.

The fresh `C-descendant-alignment.lean` diagnostic only adds a local
`have hSelected := h; change _ at hSelected` after the call. Its
expensive root still has 239,340,712 calls (counter root wall
700,375.556 ms), exactly O's call count, so it has not cut the M1
subtree. The supplied `Restored.lean` snapshot reaches a separate
6-call diagnostic root and does not restore O. The whole-`hb`
transport in `Aligned.lean` changes M0. Thus there is no demonstrated
type-correct M0-preserving cut at this dependent endpoint, and no
O/O-cut/O-restore causal speedup is claimed. The apparent root-time
difference between O and the no-op diagnostic does not establish a cut.

The missing label-specific transition rows, row mean fan-out,
whole-root label-edge counts, and global individual path ranking are
instrumentation limits. The kernel patch was not changed.
