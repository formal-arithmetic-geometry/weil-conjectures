## What changed

The unchanged theorem `AlgebraicGeometry.fan_center_local_blowup_charts` is proved by
assembling three strict subarguments with the existing
`AlgebraicGeometry.coherentLogIdeal_chart_construction` declaration. The assembly retains
one global fs log blowup from the existing construction, specializes its chart family to
`D.idealChart (hgen D)`, extracts its saturated tensor cover, and applies the single-chart
comparison for each supplied fan blowup and selected generator. Thus the chart-cover
existence part of the original plan is now actual Lean, rather than another existence hole.

The eight existing data declarations move, with identical names, signatures, attributes
and bodies, to `Sheaf.AlgebraicGeometry.FanCenterTensorChartData`, which the item publicly
imports. This prevents a cycle between the original theorem and its proof-step modules.
Only their blueprint tags change. The data node records this relocation, not a second
construction of any notion. Searched the live Lean tree, DAG, STATE and landed change
records; no alternative definition of these local input/comparison notions was found.
The item changes from the legacy import layout to the required module layout.
The theorem signature is byte-for-byte unchanged. No adopted source-library file changes.

All five modules compile through lcompile.py. Initial timings were 5.7 s for data,
3.7 s for Zariski descent, 3.7 s for coherence, 6.0 s for comparison, and 15.7 s
for the assembly. Final compilation and the delivery preflight validate the cleaned imports.
There are no direct Lean importers of the item and no forced consumer adaptations.

## Proved and sorry left

Closed the original single hole in `AlgebraicGeometry.fan_center_local_blowup_charts`
(node `lem-trf-fan-center-local-blowup-charts`). Its assembly proof is complete.
Added three holes, each the entire proof of a named public theorem in its own module:

- `AlgebraicGeometry.fan_center_pullback_coherence`, node
  `lem-trf-fan-center-pullback-coherence`: only coherence and the ideal-generation calculation.
- `AlgebraicGeometry.fan_center_blowup_zariski`, node
  `lem-trf-fan-center-blowup-zariski`: only the Zariski property of an already supplied blowup.
- `AlgebraicGeometry.fan_center_tensor_chart_comparison`, node
  `lem-trf-fan-center-tensor-chart-comparison`: only comparison for one already supplied
  affine input, generation proof, tensor cover and generator; no construction or coherence.

This is a decomposition, not a net proof gain: 1 original hole closed, 3 added,
0 left in the item module, net -2. No definition contains a hole and no arbitrary
witness is defined by choosing from an unproved existence theorem. Existing sorry-bearing
construction results are eliminated propositionally in the theorem proof only.

## No longer needed

No module is withdrawn and no mathematical branch is claimed globally pruned.
The assembly no longer directly needs the original proof dependencies
`lem-trf-fan-chart-local-monoid-lift`, `lem-trf-fine-fan-point-localization`,
`lem-trf-monoid-chart-characteristic-fan`, or `lem-trf-affine-fan-hom-universal`:
they now belong to the documented proof plans of the smaller statements.
The definitions `def-trf-fs-log-blowup` and `def-trf-fine-fan-blowup` remain needed
through the data and theorem statements.

The assembly also no longer needs its separate Noetherian argument
(`pqf-lem-affine-open-locnoeth`, `lem-weil-pbc-finite-type-algebra-noetherian`,
`pqf-def-locnoeth`): the existing construction already supplies an object of
`FineSaturatedLogScheme`, whose scheme is locally Noetherian by its structure.
These nodes can still be needed by that construction; they are not withdrawn.
The direct imports `Mathlib.AlgebraicGeometry.Noetherian` and
`Mathlib.RingTheory.FiniteType` are removed. The former remains available through
the statement imports. The original direct imports of LogFanChartBlowup,
LogIdealChartPresentation and StrictFanChartLocalComparison move to the data module.
The redundant direct imports AffineFanHomUniversal and FaceLocalizationFs disappear;
the data imports already expose their required definitions transitively.
No speculative proof-only imports remain in the three new sorried statement files.

## Where the brief, the DAG or earlier work was wrong

The original node's Noetherian step need not be repeated after applying the existing
chart-construction theorem: its supplied fs log scheme already includes that property.
The declared lemmas do not directly state the pullback-coherence calculation, Zariski
descent for a supplied blowup, or the normalized comparison for a supplied ambient tensor
cover. Their interfaces leave these substantial glue steps open, now stated separately
with source references and complete proofs in words. There is no disputed statement.
The unit route is retained; the item is not itself a realized unit statement or step.

Edge cases checked against the definitions and ILO VIII pp.101--102,107--109:
the empty base permits vacuous local statements; generators are explicitly nonempty;
a singleton or unit ideal gives the corresponding (possibly saturated) trivial chart;
no quasi-compactness, cancellation of a ring element or regularity of the scheme is used.
Comparisons use Associates of the face localization, so units in a saturated fraction
monoid are allowed. The local comparison is conditional on the actual supplied chart,
including its chartMap and chartAlpha normalization, rather than an arbitrary isomorphism.

## New nodes

`def-trf-fan-center-tensor-chart-data` attaches the relocated existing input and
comparison definitions. It introduces no new mathematical object and no hole.

`lem-trf-fan-center-pullback-coherence` is original proof step 1, independent of blowup
construction, with both coherence and the equality on every prescribed affine chart.

`lem-trf-fan-center-blowup-zariski` is the Zariski gluing part of original proof step 4
for an already supplied universal blowup. It asserts neither existence nor fan comparison.

`lem-trf-fan-center-tensor-chart-comparison` is original proof steps 4--5 on a fixed
supplied tensor chart and fixed generator, including every original normalization equation.

Each new node records the three search kinds and its source proof. The existing node's
proof and dependencies are updated to the actual Lean assembly.
Change record: `coord/changes/M1-fan-center-tensor-chart-data.md`.

## Second reading by M1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
