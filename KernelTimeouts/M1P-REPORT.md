# M1 Propagation Report

## 8.1 Dataset and classification validity

The 16 original roots use READY4.2 (`0311a15b5f4`) and the accepted
READY3.2 provenance baseline. Current roots use Lean 4.35.0
(`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`); the full historical
Derived-Completion Cone uses Lean 4.33.1
(`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`). The current probes use
the reserved `m1p` import revision `105ac3f5b23`. The READY4.2 kernel keeps
the process-wide root serial and active-root pinning. Its label, transition,
depth, fan-out and exclusive-time aggregates cover every call of the selected
root. Bounded raw enter/exit records support path inspection, not time-share
estimation. Calls outside that window receive provenance from expression
hashes and parent divergence/reduction state; insufficient evidence is
`Unclassified` rather than silently inherited.

Counter and analyzed calls agree in all 16 rows. The Cone differs by one
call from its READY3.2 timeout-boundary control and agrees with READY4.1;
NativePullTensor agrees exactly. The other case reports record equal or
explained root counts against their accepted controls. M1 shares agree with
READY3.2/READY4.1 or have the documented repeat/import-closure timing
difference. FiniteBaseChange's median is 72.869% versus 74.113% in READY3.2;
its count is unchanged, and its report attributes the timing change to the
reserved import tree and READY4.2 accounting. PR2122's 0.783-point change
from READY4.1 is confined to exclusive-time attribution with unchanged
calls. PR1627's median differs from its single READY4.1 share by 1.254
points with identical calls and edges across three repeats. Its summary
prints the repeat endpoints to slightly different precision than the
per-case table; the common rounded interval is 64.1--65.2%.

The five roots below 95% M1 time (FiniteBaseChange, RealPurity,
OrderedSpectralRawLattices, RealPushforward, PR1627) each have three repeats
and a reported min--max spread. Shapes below apply the one rule in
`BUILD-M1P.md`: deep requires M1 median depth >=75, mean fan-out <=1.5 and
90%-time band width <=32; wide requires fan-out p90 >=8 and median depth
<75; all other roots are mixed. **No row fails the inclusion checks; none is
excluded.** RealPurity and RealPushforward are near-duplicate roots
(17,310,168 and 17,340,236 calls, both 46.148% M1 calls), so they provide
one mechanism, not independent confirmation.

Raw entered coverage is 0/2,685,580 for NativePullTensor and
223/12,220,822 for Cone; the other reports give bounded windows of
1,477--4,333 calls, each against a complete aggregate root. The top-cost
branch families were checked against the exact `type_checker.cpp` versions
in `M1P-KERNEL.md`. Raw windows cannot certify every individual path.
Tracing adds bookkeeping cost: separate counter/trace root spans and the
uninstrumented Native process wall are not matched root-exclusive controls,
so no normalized instrumentation-overhead percentage is claimed.

## 8.2 Cross-case M1 propagation summary

Calls in this table are both counter and analyzed counts. Time shares are
comparison-exclusive; bracketed intervals are three-repeat min--max values,
with the median outside the brackets. The transition column
names the largest M1-parent to M1-child row, not the most frequent child.

| Case | Calls | M1 call share | M1 time share | M1 calls | M1 depth median/p90/max | 50%-time band | M1 fan-out mean/p90 | Dominant transition | Shape | C result |
|---|---:|---:|---:|---:|---|---|---:|---|---|---|
| Derived-Completion Cone | 12,220,822 | 76.560% | 99.734% | 9,356,262 | 82/93/111 | 78--90 | 1.305/3 | projection -> projection | deep | telescope changes |
| NativePullTensor | 2,685,580 | 41.730% | 98.164% | 1,120,689 | 44/55/81 | 36--47 | 2.375/9 | application -> function-head | wide | provider-dependent type |
| PR1556 | 6,670,198 | 75.051% | 99.707% | 5,006,059 | 122/181/213 | 87--125 | 1.330/3 | projection -> projection | mixed | dependent domain |
| PR1625 | 11,757,788 | 68.984% | 99.546% | 8,111,028 | 101/112/125 | 95--107 | 1.448/3 | projection -> projection | deep | outer telescope changes |
| PR1624 | 6,598,545 | 79.035% | 99.848% | 5,215,138 | 60/70/88 | 57--68 | 1.265/3 | projection -> projection | mixed | no valid cut tested |
| PR1563 | 2,563,145 | 75.084% | 99.731% | 1,924,504 | 57/70/93 | 51--63 | 1.331/3 | projection -> projection | mixed | not tested |
| PR2122 | 2,257,184 | 79.648% | 98.113% | 1,797,805 | 50/60/87 | 42--54 | 1.219/3 | projection -> projection | mixed | not tested |
| PR1627 | 10,904,899 | 24.021% | 64.767% [64.1--65.2%] | 2,619,482 | 34/37/61 | 29--35 | 2.037/9 | quick -> dependent-body | wide | not tested |
| EtaleHom | 3,180,470 | 75.171% | 99.735% | 2,390,795 | 79/90/111 | 71--83 | 1.330/3 | projection -> projection | deep | dependent `hv` type |
| FiniteBaseChange | 239,340,712 | 54.398% | 72.869% [72.843--73.112%] | 130,197,227 | 75/79/87 | 71--74 | 1.081/1 | projection -> projection | deep | local no-op; whole `hb` changes M0 |
| RealPurity | 17,310,168 | 46.148% | 62.315% [62.170--64.097%] | 7,988,264 | 86/88/91 | 84--86 | 1.274/1 | projection -> projection | deep | not tested |
| OrderedSpectralRawLattices | 18,944,709 | 43.922% | 64.684% [62.351--64.750%] | 8,320,909 | 64/68/71 | 60--65 | 1.754/8 | application -> argument | wide | not tested |
| RealPushforward | 17,340,236 | 46.148% | 61.446% [61.312--63.086%] | 8,002,209 | 84/86/89 | 82--84 | 1.274/1 | projection -> projection | deep | not tested |
| IntegralComparison | 9,426,198 | 70.875% | 99.551% | 6,680,842 | 109/133/181 | 97--116 | 1.406/3 | projection -> projection | mixed | not tested |
| F66Adj | 3,897,905 | 75.968% | 99.803% | 2,961,163 | 90/102/121 | 85--98 | 1.316/3 | projection -> projection | mixed | not tested |
| ImageHomCounit | 6,359,958 | 75.178% | 99.768% | 4,781,271 | 162/173/204 | 155--167 | 1.330/3 | projection -> projection | deep | not tested |

Call share and time share describe different properties. PR1556 has 75.051%
M1 calls but 99.707% M1 time; its numerous Matched calls are cheap. The
same pattern appears across the M1-dominated roots, while PR1627's Matched
work is visible at 10.538% time despite 6,772,753 calls. Call counts show
branching; exclusive time identifies costly propagation.

## 8.3 M1-parent transition matrix

The matrix sums complete READY4.2 transition aggregate rows for all 16 roots,
keyed by initiating branch and child kind, **only for M1 -> M1 edges**.
It uses the first READY4.2 trace for a repeated root; the median time shares
in 8.2 describe repeats separately. Child exclusive time weights the rows;
the total is 158,278,957 M1 -> M1 edges and 1,186,459 ms. Rounded time
and percentages are cross-case sums, not new per-root measurements.

| Initiating branch | Child kind | M1 child calls | M1 child exclusive ms | Share of M1 -> M1 time | Representative roots |
|---|---|---:|---:|---:|---|
| projection | projection | 83,622,222 | 563,800 | 47.5% | Cone, FiniteBaseChange, PR1556, EtaleHom |
| application | argument | 21,988,931 | 228,114 | 19.2% | PR1625, OrderedSpectralRawLattices |
| quick | dependent-body | 9,885,302 | 177,793 | 15.0% | FiniteBaseChange, PR1627 |
| application | function-head | 31,403,559 | 119,535 | 10.1% | NativePullTensor, FiniteBaseChange |
| second_whnf | whnf-iota-exposure | 4,653,628 | 62,277 | 5.2% | Cone, EtaleHom |
| lazy_delta | argument | 3,125,111 | 19,627 | 1.7% | NativePullTensor, PR1625 |
| proof_irrelevance | proposition-type | 1,140,541 | 14,550 | 1.2% | Cone, NativePullTensor |
| quick | binder-domain | 2,334,385 | 746 | 0.1% | Cone, EtaleHom |
| eta_structure | field | 125,278 | 17 | <0.1% | PR1627 |

Projection -> projection is the largest M1-time row in 13 roots, including
Cone and seven of the eight KernelTimeouts roots. NativePullTensor is led by
application -> function-head (6,773.125 ms), OrderedSpectralRawLattices by
application -> argument (15,101.023 ms), and PR1627 by quick ->
dependent-body (8,807.387 ms). FiniteBaseChange contributes 257,589.129 ms
to the projection row, so the pooled percentage is workload-weighted, not
an equal-case vote. RealPurity/RealPushforward's similar projection rows
are one recurring mechanism. Thus projection descent dominates pooled time,
but no single branch explains every root. M1 -> Matched and M1 -> M2 edges
are omitted from this propagation matrix; their costs and counts remain in
the per-case tables.

## 8.4 Representative kernel paths

Source locations below are in `M1P-KERNEL.md` for the exact release trees.
The first transitions are expression-level A4 reconstructions; aggregate
rows establish their complete-root cost. Raw capture is bounded, and
NativePullTensor has no selected-root raw enter/exit events.

* **Cone, Lean 4.33.1.** M0 is the full `inlineCone` conversion against its
  declared `Cone (quotPowFunctor J I` composed with `tensorLeft K)` type, not the earlier
  small diagnostic root. `is_def_eq_app` (line 1661) enters corresponding
  application arguments; the inherited divergent argument is M1.
  `lazy_delta_proj_reduction` (line 1896) then exposes projection components
  and compares them, retaining that lineage. WHNF exposure can re-enter an
  application through `is_def_eq_core` (line 1948), while dependent fields
  use `is_def_eq_binding` (line 1512) and proof-valued fields compare inferred
  proposition types through `is_def_eq_proof_irrel` (line 1685). The
  projection -> projection row carries 2,951,502 M1 children and
  47,227.458 ms; application -> argument adds 2,514,418 and 24,738.319 ms.
  Median/max M1 depth is 82/111 with mean fan-out 1.305.
* **PR1556, Lean 4.35.0.** The M0 `Eq`/`Eq` pair has a Matched function
  head; its `Quiver.Hom` application argument enters M1 through
  `is_def_eq_app` (line 1628). A `CategoryStruct.comp` sibling enters M2
  after reduction, so it is not counted as continuation of the same M1
  path. The M1 path proceeds through `DFunLike.coe`, `Equiv.proj` and
  `equivShrink` projection components by `lazy_delta_proj_reduction`
  (line 1857). Corresponding components retain the parent divergence.
  Projection descent costs 24,136.670 ms; application arguments cost
  15,028.210 ms. Median/max depth 122/213 and a broad 90%-time band make
  this mixed under the common rule.
* **PR1625, Lean 4.35.0.** M0 is Pi/Pi. `is_def_eq_binding` (line 1479)
  instantiates the binder and enters the dependent `Eq`/`Eq` body at
  `dependent-body[15]`. `is_def_eq_app` (line 1628) next compares the
  `Quiver.Hom` argument, then the costly `CategoryStruct.comp` sibling.
  `DFunLike.coe`, `EquivLike.coe`, `Equiv.toFun`, `Equiv.proj` and
  `equivShrink` lead to projection children through
  `lazy_delta_proj_reduction` (line 1857). The instantiated body and
  corresponding components preserve the original divergence. Projection
  children cost 39,690.038 ms and application arguments 27,459.675 ms;
  median/max depth is 101/125.
* **EtaleHom, Lean 4.35.0.** M0 is the instantiated
  `IsEtaleHomTranspose` comparison at stored `hv`. Binder instantiation in
  `is_def_eq_binding` (line 1479) compares the dependent `Eq`/`Eq` body;
  `is_def_eq_app` (line 1628) compares `DFunLike.coe` arguments without
  erasing the `hv` divergence. WHNF and projection exposure then proceed
  through `EquivLike.coe`, `Equiv.toFun`, `Equiv.invFun` and projection
  components in `is_def_eq_core`/`lazy_delta_proj_reduction` (lines
  1909/1857). Projection children cost 9,131.177 ms; application arguments
  6,421.225 ms. Median/max depth is 79/111.
* **NativePullTensor, Lean 4.35.0.** The original provider is
  `(exists_nativePullTotalTensor ...).choose`, passed to
  `nativeRestrictionDerivedTensor` when forming `nativePullTensor`. The
  reconstructed path enters its dependent application domains through
  `is_def_eq_binding` (line 1479), compares function heads and arguments
  through `is_def_eq_app` (line 1628), and continues after hint-governed
  lazy-delta exposure through `lazy_delta_reduction_step`/
  `lazy_delta_reduction` (lines 1735/1826). The two `Exists.choose`
  domains keep the original provider divergence. Complete aggregate rows
  give application function-head 6,773.125 ms, application argument
  6,455.985 ms, and lazy-delta argument 4,672.640 ms. Median/max M1 depth
  is 44/81, with fan-out p90 9. This path is source-and-aggregate
  reconstruction; the selected READY4.2 root has zero raw entered calls.

`is_def_eq_core` tries quick comparison, WHNF, proof irrelevance, lazy
delta, projection handling, further WHNF, application congruence and
fallbacks in that order (4.35.0 line 1909; 4.33.1 line 1948). The
recorded branch is the call site's initiating branch, not the parent's
eventual success/failure outcome. `lazy_delta_reduction_step` reads actual
reducibility hints, tries same-head arguments for equal regular hints and
can expose the opposite projection before unfolding one side (4.35.0 line
1735; 4.33.1 line 1768). The rows show where this control flow continues
the mismatch; they do not identify an independent source mismatch at every
child.

## 8.5 M0-preserving cut points

No valid O/O-cut/O-restore sequence removed a selected M1 subtree while
preserving the same root conversion, M0 and dependent telescope.

| Case | Candidate and observed obstruction | Causal status |
|---|---|---|
| Cone | Aligning a dependent provider/field changes the telescope and root conversion. | O and original restoration exist; O-cut is invalid. |
| PR1556 | Major-premise replacement changes the inferred dependent domain and removes M0. | No valid local O-cut. |
| PR1625 | Nested major-premise alignment changes the outer dependent telescope and removes M0. | No valid local O-cut. |
| NativePullTensor | Replacing either `Exists.choose` provider changes the required dependent argument type and removes M0. | No valid local O-cut. |
| EtaleHom | Replacing the `hv` child at the original type is ill-typed; transporting the whole proposition changes M0. | No valid local O-cut. |
| FiniteBaseChange | Local `hb` alignment is a no-op at the original root; whole-`hb` transport changes M0. | The no-op gives no M1 reduction; no valid cut. |
| PR1624 | No separate cut was assigned or measured. | No causal result. |

The other roots were not cut-point targets. The transition matrix, depth
distributions and A4 paths are direct trace/aggregate and source evidence
for propagation. They do **not** measure the cost saved by a selective
intervention. No causal speedup, reversibility result or M2 effect is
inferred from an invalid replacement.

## 8.6 Main-line conclusion

The original M0 divergence reaches M1 descendants through ordinary kernel
recursive comparisons: instantiated Pi bodies, application function heads
and arguments, projection components, and WHNF/lazy-delta continuations.
Projection -> projection carries the largest pooled M1 exclusive time
(47.5%) and leads 13/16 roots; application argument (19.2%), dependent
body (15.0%) and function-head (10.1%) are also substantial. The shared
shape rule classifies seven roots deep, three wide and six mixed. The
historical full Cone and current roots use the same branch families, with
different cost concentrations; NativePullTensor and PR1627 show that
projection is not universal. RealPurity and RealPushforward count as one
mechanism. No valid M0-preserving cut provides direct causal savings
evidence. Bounded raw windows, unmatched instrumentation overhead and the
unavailable selective cuts limit claims about individual unseen paths and
counterfactual cost. The reason the original M0 arose, and the incremental
causal role of M2, remain outside this report.
