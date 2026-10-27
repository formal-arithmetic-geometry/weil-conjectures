## What changed

The ambient theorem `WeilConjectures.podReindexingCompletionUnit` now assembles
strict tower comparisons, quotient comparisons, normalized completion, and derived
comparisons. Its statement is unchanged. The actual counit equation is proved from
the unit equation by adjunction, rather than made a separate assumption. The unit
on complete objects and invertibility of the specified ordinary-to-completed map
are proved using normalized reconstruction. The Roos boundary square is proved
by every product projection.

Eight new modules isolate completion normalization, preservation of good complexes,
the signed Roos shift, the canonical additive Roos comparison, restricted towers,
signed-shift compatibility, strict assembly, and derived comparison normalization.
The strict constructions and ambient assembly concern the original unbounded
categories. No existing public signature, definition, attribute, or public import changes.

## Proved and sorry left

Original holes: 2. The proof body of `podReindexingCompletionUnit` is replaced by
a complete assembly argument. This is a decomposition until its remaining derived
comparison theorem is proved; it is not claimed as a net hole closure.

The original `WeilConjectures.podReindexingCompletionUnitTensor` remains open in
node `lem-pod-reindexing-completion-unit-tensor`. The delivery adds
`WeilConjectures.podReindexingDerivedComparisons` in
`lem-pod-reindexing-derived-comparisons`: localization and simultaneous normalization
of reduction, total limit, finite evaluation, restriction, extension, and pullback.
Its statement is strictly part of the ambient argument: it assumes the strict
comparisons and normalized quotient maps, and does not assert completion-unit
normalization, preservation of good complexes, signed shifts, the counit equation,
completeness, or invertibility on complete objects.

The completed proof bodies are:
`podReindexingCompletionNormalization`, `podCompletedCoefficientMap_eq`,
`podReindexingGoodComplex`, `podReindexingSignedRoosShift`,
`podReindexingRoosCoordinates`, `podReindexingRoosNaturality`,
`podReindexingRoosComparison`, `podReindexingRestrictedTower`,
`podReindexingRoosShiftCompatibility`, `podReindexingStrictComparisons`, and
`PodReindexingStrictData.good`. The item also proves private helpers
`podOrdinaryToCompleted_isIso`, `podCompleteUnit`, `podCounit_of_unit`, and
`podRoosBoundary_reindex`, and combines them in `podReindexingCompletionUnit`.
“Proved” here means complete Lean proof bodies from the named library dependencies;
it does not assert that their transitive axiom closure is already sorry-free.

Hole accounting: one original hole replaced (`podReindexingCompletionUnit`), one
original hole retained (`podReindexingCompletionUnitTensor`), one new hole
(`podReindexingDerivedComparisons`), net zero holes closed. No holes occur in
any definition or private helper. No downstream module is adapted. The original
module has one remaining hole; the added modules together have one remaining hole.

Validation: all nine delivered Lean modules compile through `lcompile.py`.
The final dependency-ordered check compiled signed-shift compatibility, strict
assembly, the derived comparison statement, and the item with exit code 0 and
no warnings. Final delivery preflight supplies the independent packet checks.

Edge cases: the strict proofs are generic in an abelian category, use every integer
shift, and impose neither boundedness nor completeness. Completion normalization
uses a singleton index family but does not choose a point of the scheme; thus it
also applies to the empty scheme. The new localization statement retains all
ambient systems, quotient transitions and the K-injective normalization; it does
not infer equality of derived maps from finite projections alone.

## No longer needed

Removed proof imports from the item:
`Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`,
`Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`,
`Sheaf.Paper.ExactProductFunctorStrictLimit`,
`Sheaf.Paper.IntegralDerivedOperationsOnSlices`,
`Sheaf.Algebra.Homology.ChangeOfRingsKFlat`,
`Sheaf.Algebra.Homology.KFlatTotalTensorModel`,
`Sheaf.Paper.IntegralOperationsWellDefined`,
`Sheaf.Paper.PurInverseImageTensorHom`, and
`Sheaf.Paper.PodReindexingHomResolutionModel`.
The strict assembly retains `import all Sheaf.Paper.IsomorphismReductionTower`
to reuse the existing private equivalence proof.
The ambient proof uses the existing `isomorphismReductionTower` through the public
model interface, canonical scalar Roos maps, and the native signed Roos calculus.
It does not use the larger exact-product-functor limit specification.

No module is withdrawn or asserted globally unreachable. The original tensor
family theorem is still open, so the original eight-step unit route and its
remaining dependencies are retained in the original node. In particular the
removed imports may remain needed below the open tensor/coherence argument.

## Where the brief, the DAG or earlier work was wrong

The original ambient plan treated the counit compatibility as an independent
calculation. Its whole-system equation follows formally from the unit equation
and the two triangle identities. The signed Roos shift already exists in the
native Roos cone calculus; its product comparison agrees with the prescribed
inverse projection comparison by product extensionality. The two completed
coefficient maps in the existing interfaces agree by their finite projections;
no change to either definition is needed.

## New nodes

`lem-pod-reindexing-completion-normalization`: identify original completion and its
augmentation with the selected reduction/limit composite and its actual unit.

`lem-pod-reindexing-good-complex`: identify coefficient maps and specialize the
existing K-flat preservation theorem to the identity coefficient extension.

`lem-pod-reindexing-signed-roos-shift`: specialize native signed Roos shifts and
identify the product comparison by every projection.

`lem-pod-reindexing-roos-comparison`: the canonical scalar Roos map has both product
coordinate formulas, is natural on strict towers, and is invertible for an additive
equivalence by the degreewise biproduct matrix.

`lem-pod-reindexing-restricted-tower`: transpose the actual coherent-system
inverse-image unit, retaining its section formula in every cochain degree.

`lem-pod-reindexing-roos-shift-compatibility`: compare diagonal Roos maps and signed
shifts through both cone coordinates.

`lem-pod-reindexing-strict-comparisons`: assemble the canonical Roos and actual
restricted-tower comparisons before localization.

`lem-pod-reindexing-derived-comparisons`: the remaining localization and
normalization argument for the simultaneous derived comparisons.

## Second reading by Z5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
