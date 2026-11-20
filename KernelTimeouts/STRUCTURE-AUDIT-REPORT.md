# Structure Exposure Audit: KernelTimeouts

Lean/Mathlib: 4.35.0. The retained timings use one Lean thread, normal
Kernel checking, `timeout 3600`, and `/usr/bin/time -v`; diagnostic
skip-Kernel probes are labelled as such in the case records. The exact
conversion site and all source changes are documented in each case's
`STRUCTURE-AUDIT.md`; the pre-existing HEAD/workplan records and probes are
preserved alongside them.

## R7 summary

| Case | Cost site | Initial mismatch | Boundary | Classification | Confidence | §6 outcome |
|---|---|---|---|---|---|---|
| RealPushforward | final `exact this` | `charpolyRev` / `localPolynomial` | `Polynomial.coeff` polynomial argument | N | Confirmed for necessary unfold | aligned polynomial succeeds; simple-unfolding control |
| OrderedSpectralRawLattices | final result/goal conversion | three instance routes in two ring lets | `continuousMapRingObj` topology instances | P2, P3 | Confirmed bundle alignment | R/H/D aligned succeeds; restored baseline times out |
| EtaleHomComparisonReversedExact | helper argument 26 (`hv`) | named predicate, then wrapper/raw quantified domain | instantiated dependent `forall K` | P2 | Confirmed whole-domain control | transported domain cheap; original restored |
| FiniteBaseChangeRestrictionMateTransport | helper argument 49 (`hb`) | `ProEt` / `Site .ordinary` in square domain | dependent `Quiver.Hom` site argument | P1 | Confirmed | `hb` transport cheap; original restored |
| F66Adj | helper argument 39 (`hR`) | `Over.left (Over.mk f.left)` / local `X` | dependent counit proposition | P1 | Confirmed | direct restriction control cheap; original restored |
| ImageHomCounit | final `exact h` | raw `DerivedCategory` / `DerivedCategoryModule` | `Quiver.Hom` derived-category endpoint | P2 | Confirmed full alignment; inner child unresolved | uniform alignment 2.60 s; raw restoration 54.94 s |
| IntegralComparisonPullbackRealizationShifts | explicit `change` | two `HasDerivedCategory` paths | `Functor.obj`/`DerivedCategory` instance | U (P4 candidate) | Plausible | first-leaf alignment negative; whole After is faster |
| RealPurity | final `exact h` in `hreal'` | two commutative-ring instance paths | `Polynomial.reverse`/`coeff` ring argument | U | Not supported for ring sufficiency | both-side alignment still times out |

## §6 restoration experiments

| Case | Original | Aligned | Restored | Same consumer/obligation | Footprint result |
|---|---:|---:|---:|---|---|
| ImageHomCounit | 54.94 s, raw/wrapper final conversion | 2.60 s, exact inferred target | 54.94 s, original raw target | yes; original `h` and final `exact h` | wrapper-only expansion is 83.45 s; full alignment removes the measured `Add.add`/`Functor.obj`/`DFunLike.coe` chain |
| OrderedSpectralRawLattices | 40.23 s timeout, all three routes | 10.11 s, all R/H/D routes disabled | 40.23 s timeout, routes re-enabled | yes; same declaration and three lets | first two ring values align only in the full control; original `Functor.obj` footprint returns |

The restored rows reuse the immutable original probes after reintroducing the
same source mismatch. No claim is made that the remaining third-let or inner
endpoint work is absent; those fields are explicitly marked unresolved in the
case reports.

## §10 project-level counts

The audit covers **8/8 cases** for an exact timed site, an initial expression
difference, a candidate boundary, and an exposed-structure inventory. The
inventory is structurally inferred where the ordinary probes do not expose an
internal Kernel trace; this limitation is strongest in RealPurity and the
negative IntegralComparison control.

For causal coverage, **5/8 cases** have a same-consumer, normal-Kernel
alignment that removes the measured expensive conversion and a substantial
predicted footprint: OrderedSpectralRawLattices, EtaleHomComparison,
FiniteBaseChange, F66Adj, and ImageHomCounit. RealPushforward has a successful
alignment but is deliberately classified N; IntegralComparison and RealPurity
are negative/unknown controls.

For cost coverage, use the isolated exact sites (so parent and child timings
are not added):

* P1/P2/P3 cases: 736.98 s across 5 cases.
* All eight isolated sites: 935.82 s.
* P1/P2/P3 coverage: **78.7%** of the measured Kernel-time total.

The total is a coverage accounting device, not a sum of inclusive declaration
and child timings. Full declaration timings and RSS remain in the case
README/HEAD-AUDIT records.

## Observations

* Every case has a large normal-Kernel versus skip-Kernel gap at its audited
  site or parent declaration.
* Confirmed positive controls fall into three recurring shapes: complete
  dependent-proposition transport, complete instance-bundle alignment, and
  full endpoint representation alignment.
* Single-leaf controls fail in OrderedSpectralRawLattices, ImageHomCounit,
  IntegralComparison, and RealPurity; these are retained as negative controls.
* RealPushforward is a small regular-head unfolding reference rather than a
  data-exposure claim.

## Interpretations and limits

The measured controls support a representation-and-conversion model for most
Kernel-time coverage, especially the five P1/P2/P3 cases. They do not show the
Kernel's internal reduction order. Unfold counters are therefore reported as
downstream footprints, not as independent causes. The exact dominant child
after alignment remains unknown in ImageHomCounit, IntegralComparison, and
RealPurity; those cases are not promoted to a stronger classification.
