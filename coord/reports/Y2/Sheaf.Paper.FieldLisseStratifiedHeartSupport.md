## What changed

Proved `AlgebraicGeometry.ProEtale.field_lisse_stratified_heart_support` with its
original signature and public imports. The field hypothesis at the chosen terminal
profinite set is transported to PUnit. A finite-dimensional basis, transported through
the internal-module equivalence, makes each finitely presented scalar model finite free.
The existing scalar-extension comparison then identifies finite constant models with
lisse modules in both directions.

The proof uses the actual fibre-product intersection of adapted scheme stratifications.
Exact pullback and the assumed lisse closure properties give kernel, cokernel and
extension closure. Existing generic open-extension and closed-pushforward stratification
helpers give constructibility of the locally closed extension. Condensed recollement,
the open unit and closed counit give all three restrictions and exactness. Two natural
single-complex comparisons give the derived degree-zero assertion.

The `import all` imports use already proved generic private helpers, whose hypotheses
allow arbitrary commutative condensed coefficients. In particular the specialized
public coefficient-family theorem is not applied to an arbitrary field. All new helpers
are private and proved. No definitions, target statements or other modules were changed.
The node proof, proof dependencies and proof origin follow this argument.

## Proved and sorry left

Closed: `AlgebraicGeometry.ProEtale.field_lisse_stratified_heart_support` (the item's
only original hole).

Added: none. Remaining: none. This is one proof, not a decomposition.

## No longer needed

The following direct proof imports were removed. Some foundational results remain
available through the imports which actually provide the interfaces used by the proof;
removal of an import here is not a claim that its whole module is globally unused.

- `Mathlib.LinearAlgebra.Basis.VectorSpace`.
- `Sheaf.CategoryTheory.ConstantFiniteFreePresentationExtension`.
- `WeilConjectures.ConstructibleSheaf.Pullback`.
- `WeilConjectures.AlgebraicGeometry.ConstructibleStratificationAssembly`.
- `Sheaf.AlgebraicGeometry.CondensedModulePullbackExact`.
- `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`.
- `Sheaf.AlgebraicGeometry.ProEtaleIdentifiedOpenClosed`.
- `WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme`.
- `Sheaf.AlgebraicGeometry.ProEtaleOpenRestrictionCounit`.
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs`.

The old separate stratification assembly/pullback route is replaced by actual
fibre-product intersection and pullback of finite constant models. Generic scalar
extension replaces the planned specialized finite-presentation-extension route.
Generic condensed recollement and the existing stratified-support helpers replace the
separate coefficient-identification, reduced-complement and finite-coefficient steps.
The following nodes are therefore removed from this item's direct proof dependencies:

- `lem-sfb-constant-finite-free-presentation-extension`.
- `lemma-constructible-pullback-stratification`.
- `lem-sfb-coefficient-heart-locally-closed-extension`.
- `def-weil-constructible-subset`.
- `lem-weil-pbc-constructible-stratification-assembly`.
- `lem-sfb-lisse-module-inverse-image`.
- `sk-def-sfb-coefficient-morphisms`.
- `lem-sfb-proetale-identified-open-closed`.
- `sk-def-sfb-module-objects`.
- `lem-weil-pbc-reduced-induced-closed-subscheme`.
- `def-sfb-finite-lower-star`.
- `lem-sfb-proetale-open-restriction-counit`.
- `lem-sfb-noetherian-complementary-stratifications`.
- `def-constructible-stratification`.

No module is withdrawn and no claim is made that any of these nodes is unnecessary
for other consumers or for the proofs of the imported interfaces. The blueprint unit's
statement and realized route are preserved.

## Where the brief, the DAG or earlier work was wrong

No statement was disputed or changed. The original DAG planned several intermediate
constructions that existing proved generic interfaces already supply. The common
refinement can be constructed directly by `Scheme.Stratification.inter`, with actual
projection morphisms; it does not require assembling strata from subset containments.
For the final comparison of single complexes one only needs preservation of zero
morphisms, so descending an exact functor to derived categories is unnecessary for that
particular assertion. Exactness itself is still established as required.

## Second reading by Y2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
