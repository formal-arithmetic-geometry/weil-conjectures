## What changed

Constructed the chain isomorphism degreewise from the normalized ordinary scalar/tensor
identifications and ordinary balancing. Proved its section formula by unit naturality
and cancellation of the ordinary tensor identification. The parent comparison is
assembled from a universal scalar-counit square and a fixed K-flat tensor square;
its proof cancels invertible scalar counits and exact factors, then uses naturality
along an actual flat-term K-flat resolution to handle every derived object.
The new proofs locally keep SheafOfModules.monoidalCategory irreducible, as in
DerivedScalarMateData, to match tensor APIs without unfolding the monoidal
construction. A private local siteEssentiallySmall instance fixes the site size to
u+1 via Mathlib essentiallySmallSelf, avoiding the imported integralOperationsSiteSmall
instance whose unused universe parameter leaves max(u+1, ?v) undetermined. Neither
setting changes any global instance or definition.

Corrected the unused final-theorem public imports in ProEtaleScalarBalancingChain and
UnboundedCoefficientPullbackModel to identification-only imports. This removes the
cycle that otherwise prevents the planned dependency from being imported. Their
signatures, attributes, definitions and proofs are unchanged.

The scalar square reuses the already proved ordinary lifting and mate-identification
helpers of UnboundedCoefficientPullbackModel, the universal representative formula
of PulledReductionNormalizationComparison, and the exact factorization helper of
DerivedExactSquareComposition. These are tools from their existing nodes
lem-exc-unbounded-coefficient-pullback-model,
lem-weil-pbc-pulled-reduction-normalization-comparison and
lem-pod-derived-exact-square-composition: the item unit has no separate declaration
of these generic cochain localization calculations. Their proved helpers supply the
same scalar counit argument, without invoking another unit's geometric theorem.
No maintainer tool_uses approvals are added or changed.

Change record: coord/changes/H7-scalar-normalization-foundation-imports.md.

## Proved and sorry left

The item originally has one hole, in
AlgebraicGeometry.ProEtale.proEtaleScalarTensorNormalization. Its proof is assembled
from existing declarations and the new tensor compatibility statement, with an actual
chain construction and an explicit extension from flat K-flat resolutions.

AlgebraicGeometry.ProEtale.scalarTensorChainCounitSquare has been compiled with a
complete proof, and scalarTensorChainIso is an explicit definition. The private
section-formula helpers and the parent theorem compile. The final proof check took
27.6 seconds. TensorColimitsIndependentCoefficients supplies the site/monoidal tensor
isomorphism that converts the resolution flatness witness. The direct importer of
the corrected balancing foundation, UnboundedCoefficientPullbackModel, has also
compiled against that change.

One new hole remains: AlgebraicGeometry.ProEtale.scalarTensorRepresentativeSquare,
node lem-sp-scalar-tensor-representative-square. Its proof is exactly `:= by sorry`.
The delivered existing balancing module retains its original hole in
AlgebraicGeometry.ProEtale.proEtaleScalarBalancingChain, node
lem-sp-proetale-scalar-balancing-chain. That hole is unchanged, not newly added.
UnboundedCoefficientPullbackModel retains its complete proof and zero holes.

Thus this packet closes one original hole, adds one strictly smaller
tensor-compatibility hole, and leaves the existing balancing hole unchanged. This is
a decomposition, with zero net holes closed among the changed declarations, rather
than a claim of a complete axiom-free proof of normalization. The pinned-baseline
sorry ledger determines the separate target-closure count.

## No longer needed

Removed the following direct proof imports from the item:

- Sheaf.AlgebraicGeometry.ProEtaleInverseImageTensorComparison
- Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
- Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
- WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
- WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
- Sheaf.Algebra.Homology.KFlatTotalTensorModel
- Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
- Sheaf.Paper.TensorPullbackRepresentativeDescent

These arguments remain in the DAG through the scalar and coefficient-resolution
compatibility steps; they are delegated rather than withdrawn. The split tensor
statement does not add a proof-only import of its future coefficient-square proof.
The exact-functor import is retained. KFlatResolutionGeneral replaces the
independent-universe resolution import: here coefficients already live in the maximum
of the actual site universes, so its proved theorem applies directly. No library
module is withdrawn.

The parent delegates the following former direct node dependencies to the new
compatibility steps (or their existing prerequisites):

- lem-pur-derived-change-of-rings
- def-weil-pbc-proetale-operations
- lem-weil-pbc-ring-sheaf-change-adjunction
- lem-weil-pbc-exact-functor-derived-factorization
- def-sp-constant-scalar-pullback-comparison
- lem-sp-proetale-tensor-coefficient-resolution-square

The final ProEtaleScalarMateNormalization theorem is not needed by either corrected
foundation. Their definitions come from ProEtaleScalarMateIdentifications.

## Where the brief, the DAG or earlier work was wrong

The DAG's balancing dependency could not be imported as published: it imported the
parent's consumer theorem, causing an actual import cycle. Both ordinary foundation
modules only require the already separated identification declarations. The theorem
statement and the unit route require no change.

The two compatibility steps are separate mathematical arguments. The scalar-counit
square contains no derived tensor model and holds on arbitrary complexes. The tensor
square contains no geometric scalar mate or restriction/pullback comparison and only
concerns a fixed flat-term K-flat first factor. Neither repeats the parent theorem.
Empty schemes, zero modules, identity morphisms, identity coefficient maps and nonflat
finite-ring maps obey these constructions: only the first factor is required K-flat,
and no scalar counit is assumed invertible on a general complex.

## New nodes

lem-sp-scalar-chain-counit-square: constructs the actual chain comparison and records
the universal scalar-counit square. It refines Step 2 of the parent proof.

lem-sp-scalar-tensor-representative-square: the coefficient-resolution tensor square in
scalar coordinates, only on flat-term K-flat representatives, with no scalar mate.
It refines Step 3 and retains the existing coefficient-resolution-square dependency.

## Second reading by H7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
