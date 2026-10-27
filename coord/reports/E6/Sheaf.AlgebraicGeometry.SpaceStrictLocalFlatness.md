## What changed

Proved `AlgebraicGeometry.AlgebraicSpace.flatAt_iff_chart_stalk` in the assigned module.
The forward direction now compares the existential witness and the prescribed chart on
common source and target scheme fibre products. A common-field refinement gives a point
over the two prescribed points. Faithfully flat descent handles source refinements;
`AlgebraicGeometry.etale_local_ring_flatness` handles target refinements. The reverse
direction inserts the given chart directly into `MapIsFlatAt`.

All six private helper theorems are proved: equivalence of the common-field relation,
point lifting to a represented pullback, independence of the representing scheme test,
source and target stalk comparisons, and their combination for a commutative square.
The common-field equivalence uses the residue field at a point of a scheme fibre product,
so it works for arbitrary fields and does not require algebraically closed representatives.
No algebraic-space atlas is required to be surjective. An empty chart cannot satisfy the
given point hypothesis; no additional nonemptiness or finiteness assumption is introduced.

The public declarations, signatures, definitions, public imports, and existing docstrings
are preserved. The node's proof, proof dependencies, and proof origin now record the direct
chart-refinement route alongside the retained plan for the other three obligations.
No existing module besides the item is changed, and no change record is needed.

Mathlib and source-library searches found the scheme stalk flatness tools, but no direct
proof of the algebraic-space chart-independence statement. The proof uses the existing
proved etale module-flatness declaration and faithful-flat descent API.

## Proved and sorry left

Closed 1 of the original 4 holes:
`AlgebraicGeometry.AlgebraicSpace.flatAt_iff_chart_stalk`.
Added 0 holes and split off 0 statements.

The following three declarations retain their original whole-proof `sorry`, all attached
to `lem-sfb-space-strict-local-flatness` with their original sources and proof docstrings:

- `AlgebraicGeometry.AlgebraicSpace.schemeStrictLocal_presentation`.
- `AlgebraicGeometry.AlgebraicSpace.strictLocalChartComparison`.
- `AlgebraicGeometry.AlgebraicSpace.geometricStalk_flat_iff`.

Validation: `lcompile.py` compiled the module in 8.3 seconds. A temporary
`#print axioms flatAt_iff_chart_stalk` reported exactly `propext`, `Classical.choice`,
and `Quot.sound`; the diagnostic has been removed from the delivered file.

## No longer needed

The completed chart-independence proof does not use any of those three open theorems,
strict-henselization presentations, or geometric-point specified lifts. It does not need
the broader chartwise stack calculus or algebraic-space fibre-product permanence results:
`IsEtale` itself supplies the two representing scheme squares needed here.

Removed the following unused private imports:

- `Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`.
- `WeilConjectures.AlgebraicGeometry.EtaleLocalRingTriples`.
- `WeilConjectures.RingTheory.EtaleResidueTriplesLocalizedStrictHenselization`.
- `WeilConjectures.RingTheory.EtaleResidueTriplesStrictHenselization`.
- `WeilConjectures.RingTheory.StrictHenselizationFaithfullyFlat`.
- `Sheaf.RingTheory.StrictHenselizationModuleFlatness`.
- `Mathlib.RingTheory.Flat.Stability`.
- `Mathlib.CategoryTheory.Limits.HasLimits`.
- `Mathlib.AlgebraicGeometry.AffineScheme`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`.
- `Mathlib.AlgebraicGeometry.Scheme`.

The strict-local prerequisites remain in the DAG plan for the three untouched obligations;
no node is withdrawn, and no whole library module is declared globally unnecessary.
The unit's statement and steps are preserved. In particular, this delivery does not
claim to prune the strict-henselization route of `geometricStalk_flat_iff`.

## Where the brief, the DAG or earlier work was wrong

No false statement or tool defect was found. The original final proof paragraph routes
chart independence through the geometric-stalk theorem. The direct etale source-and-target
refinement argument is shorter for that clause and proves it independently of the three
strict-local obligations. Its sources are spaces-morphisms.tex
`lemma-local-source-target-at-point`, descent.tex `lemma-flat-at-point`, and flat.tex
Tag 05BA (`lemma-etale-flat-up-down-local-ring`). The source point relation and its
common-field interpretation are Tag 03BU; Mathlib's scheme pullback point theorem supplies
transitivity of that relation.

## Second reading by E6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
