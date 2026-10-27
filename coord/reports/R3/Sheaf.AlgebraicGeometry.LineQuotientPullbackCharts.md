## What changed

Replaced the proof of
`AlgebraicGeometry.ProjectiveBundleQuotientGeometry.lineQuotient_pullback_charts`
without changing its signature, definitions, or public imports. All new helpers are private
and proved in the item module. Added private proof imports of the existing homogeneous
fraction map and atlas modules (using their proved private coefficient helpers), pullback
free generators, invertible tensor pullback, and preservation of epimorphisms.

The normalized adjunction comparison evaluates the pulled quotient on actual sections.
Cancellation against the pulled free frame proves the generator coefficient equation.
The existing atlas coefficient-ring construction turns each frame's homogeneous
coefficients into a ring homomorphism. Symmetric-algebra induction then proves all
homogeneous coefficient equations from the scalar and generator equations. Finally,
canonical away-localization maps compare the chart morphisms on a generator-open cover.
The existing fraction-map existence theorem supplies all chart clauses for the pulled
quotient, and equality of its morphism with the composite transfers that entire predicate.

Updated the item's DAG proof and dependencies to record this argument. No other existing
module or node is changed. The mathematical source is Stacks Constructions,
`section-projective-bundle` and `lemma-apply-relative` (Tags 01OA and 01O4), read in the
local source. The unit route is retained.

## Proved and sorry left

Closed the single hole in
`AlgebraicGeometry.ProjectiveBundleQuotientGeometry.lineQuotient_pullback_charts`
(node `lem-trf-line-quotient-pullback-charts`). Added zero holes and split off zero
statements. The item module contains no `sorry`. Its single-file server compile passed
without warnings in 21.6 seconds. The theorem statement was also compared verbatim
with the repository version and is unchanged.

The proof uses the existing declaration
`AlgebraicGeometry.Scheme.Modules.line_quotient_homogeneous_fraction_map`; its existing
fraction-atlas dependency remains an obligation outside this delivery. No proof of an
imported obligation is claimed here.

## No longer needed

No existing public import or declaration is removed, and no module is withdrawn.

The original plan's direct use of
`lem-weil-pbc-module-pullback-affine-sections`
(`WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections`) is unnecessary:
naturality of the normalized adjunction unit gives the required formula on actual
sections without an affine tensor-sections comparison. This node may remain needed
elsewhere, including below the existing fraction-map theorem.

`lem-pc-module-pullback-identity-composition` is not used directly: its unnormalized
existence witnesses are replaced by the normalized comparison already defined by
`def-pc-module-pullback`. The direct use of
`lem-weil-pbc-invertible-pullback-invertible` is subsumed by the existing stronger
`lem-weil-pbc-invertible-pullback-tensor`; its internal dependencies are retained.
`def-per-projective-bundle-quotient-data` is not a proof dependency of this theorem:
no tautological quotient datum is required for the arbitrary-pullback chart comparison.
Its definitions and the unchanged public data import remain in place.

The proof uses only the proved coefficient-ring helpers of
`lem-trf-graded-line-homogeneous-fraction-atlas` directly, not its chart-construction
conclusion a second time. No new tensor-power pullback comparison or chart-transport
obligation is introduced.

## Where the brief, the DAG or earlier work was wrong

The original first proof step discusses an auxiliary tautological quotient on Proj,
although the theorem has no such datum. The proof needs only invertibility and
epimorphism preservation for the given quotient. The original all-degree tensor
comparison can be shortened to equality of coefficient ring homomorphisms on symmetric
algebra generators. The item statement itself is unchanged and no mathematical error
is asserted.

Empty source schemes are covered by the vacuous pointwise equality argument; empty affine
opens and zero rings are allowed by frame bijectivity and the localization formulas.
Degree zero is handled explicitly by the structural unit and scalar axioms. Denominators
may be zero, nilpotent, or zero divisors; no step cancels a denominator in its original
ring. No flatness, finite generation, separatedness, or affine-intersection hypothesis
is added.

## Second reading by R3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
