## What changed

Proved `AlgebraicGeometry.exists_affine_surjective_finite_etale_thickening_of_isQuasiFinite`
with its original signature. The Lean proof carries out Noetherian approximation, finite
stratification, the existing finite affine section cover, disjoint section selection,
finite coproduct assembly, and pullback to the original base.

Added `Sheaf.AlgebraicGeometry.ClosedSectionAffinePartition`, with the proved theorem
`AlgebraicGeometry.exists_closed_section_affine_partition`. Its three private helpers
construct Boolean-compatible reduced affine pieces, identify a lifted section square as
a pullback, and select distinct disjoint closed sections. No new unproved statement is used.
The final closed immersion is assembled using its stalk maps and the fact that a finite
union of closed images is closed. Etaleness is checked on the source coproduct components;
finiteness follows from the already finite ambient map.

Attached the existing, proved source-library declaration
`AlgebraicGeometry.Scheme.Hom.exists_stratification_isFinite` to a new source-reuse node.
Its source module is unchanged. Also reattached the existing reduced-source factorization
node to the proved source-library theorem with uniqueness; its reduction clause is the
specialization to the nilradical immersion. The old holed wrapper is not imported. Updated the item's proof, proof dependencies, and proof
origin to match this route. All added imports in the item are proof-only imports.
No existing public signature, definition, or visibility changed, so no consumer adaptation
or change record is needed.

Both sandbox modules compile together via `lcompile.py --all`, with no warnings and zero
`sorry` occurrences. Empty bases, zero sections, empty sources, repeated sections, and
nonreduced original bases are included: Boolean atoms cover all points, reduced affine
pieces permit factorization, and finite-image deduplication also works for empty index sets.

## Proved and sorry left

Closed 1 of the item's 1 holes:
`AlgebraicGeometry.exists_affine_surjective_finite_etale_thickening_of_isQuasiFinite`.

The new theorem `AlgebraicGeometry.exists_closed_section_affine_partition` is proved in full
(node `lem-weil-pbc-closed-section-affine-partition`). The attached finite-stratification
theorem was already proved; this delivery does not count it as a newly closed hole.

Holes left in the item: none. Holes added: none. Split-offs left unproved: zero.
Existing dependencies are used through their declarations as required by stage 3;
this does not claim that all transitive dependencies of the targets are proved.

## No longer needed

Removed direct imports from the item:

- `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`
- `Mathlib.AlgebraicGeometry.Noetherian`
- `Mathlib.RingTheory.Ideal.Quotient.Operations`
- `Sheaf.AlgebraicGeometry.Morphisms.GenericFiniteOpenNeighborhood`
- `Sheaf.AlgebraicGeometry.QuasiFiniteIffFiniteFibres`
- `Sheaf.AlgebraicGeometry.QuasiFiniteLocallyQuasiFinite`
- `Sheaf.AlgebraicGeometry.SeparatedLqfBaseChange`
- `Sheaf.RingTheory.ReducedIdealsZeroIntersection`
- `WeilConjectures.AlgebraicGeometry.Morphisms.ProperQuasiFinite`
- `WeilConjectures.AlgebraicGeometry.Thickening`

These are replaced by direct Mathlib quasi-finite APIs, the already proved source finite
stratification, and the new proved section-partition module. The explicit Noetherian and
Thickening imports were redundant through retained public imports.

Removed from the item's direct planned proof dependencies:

- `def-pc-reduced-scheme`
- `def-weil-closed-immersion`
- `def-weil-pbc-scheme-reduction`
- `lem-pc-crt-ideal-quotient-product`
- `lem-pc-quasi-compact-base-change`
- `lem-sc-affine-noetherian-underlying-space`
- `lem-sc-reduced-ideals-zero-intersection`
- `lem-weil-pbc-closed-finite-etale-zariski-local`
- `lem-weil-pbc-generic-finite-morphism-open-neighborhood`
- `lem-weil-pbc-noetherian-boolean-affine-refinement`
- `lem-weil-pbc-scheme-coproduct-copies`
- `lem-weil-pbc-separated-lqf-base-change`
- `pqf-lem-qf-finitefibres`
- `pqf-lem-qf-locqf-qc`

The generic finite-neighborhood and base-change ingredients are now encapsulated in the
already proved source finite-stratification theorem; its new attachment records that
mathematical proof. The old Sheaf modules for those intermediate steps are not imported.
The finite-fibres criterion and quasi-finite/locally-quasi-finite theorem are unnecessary:
their needed implications are proved directly from the discrete-fibre Mathlib API.
The separate Boolean-refinement node is bypassed by the explicit Boolean construction in
the new module. The reduced-ideal and CRT lemmas are replaced by the proved closed-immersion
factorization API and finite disjoint closed-image assembly. The special coproduct-of-copies
node and the combined closed/finite/etale target-locality node are unnecessary: the proof
uses general coproducts and the existing source and target locality APIs directly.

Pruned obsolete top-level tool approvals `lem-sc-reduced-ideals-zero-intersection` and
`pqf-lem-qf-locqf-qc`. Retained the finite-presentation descent and affine-partition approvals.
No Lean module is withdrawn: other parents may still use any of these statements.

## Where the brief, the DAG or earlier work was wrong

The planned dependency `Sheaf.AlgebraicGeometry.NoetherianBooleanAffineRefinement` has a
Lean attachment in its node, but its source file was absent from the shared repository.
The delivery does not depend on that missing module: it proves the needed Boolean
construction and section selection together in the new module.

The source library already proves the Noetherian finite-stratification argument in
`WeilConjectures.AlgebraicGeometry.EtaleFiniteRefinement.FiniteStrata`. Reusing it is shorter
than rebuilding the planned generic-finiteness induction from the Sheaf declarations.
The finite coproduct of disjoint closed immersions can be proved closed directly, so the
planned CRT ring calculation is unnecessary. The original theorem's docstring remains a
valid alternative natural-language proof; the node records the actual Lean route.
The proper-base-change unit's own statement and realized steps are unchanged.

## New nodes

`lem-weil-pbc-closed-section-affine-partition` records the fully proved section-refinement
step. It is strictly part of the original argument: it assumes the finite closed-section
cover and concludes disjoint sections after reduced affine refinement. It contains no
Noetherian approximation, finite-cover production, finite-etale thickening assembly, or
pullback to a non-Noetherian original base. Nothing remains to prove in its module.

`lem-weil-pbc-quasifinite-noetherian-finite-stratification` attaches the existing proved
source theorem `AlgebraicGeometry.Scheme.Hom.exists_stratification_isFinite`. Its exact
hypotheses include locally quasi-finite, locally finite type, separated, quasi-compact,
and Noetherian base. No new Lean file or hole is introduced for this attachment.

Existing node reattachment: `lem-weil-pbc-reduced-source-factors-through-closed-subscheme`
now names `AlgebraicGeometry.IsClosedImmersion.existsUnique_fac_of_range_subset_range` in
the source library. It supplies the general factorization and, by specialization, the
reduction clause; no statement was changed and no old Lean module was edited.

Change records: none (no existing signature or definition changed).

## Second reading by J7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
