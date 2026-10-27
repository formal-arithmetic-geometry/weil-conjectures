## What changed

Proved both naturality laws of
`Sheaf.AlgebraicGeometry.SfEtaleCompactProjectionCoherence` from the naturality
of the existing forward projection transformation, cancelling its invertible
components using `sfEtaleAmbientAdjointProjection`. All original public
signatures, definitions, public imports and docstrings are unchanged.
This is a partial delivery of two of the module's four original holes.
No new statements, assumptions or holes were added. The complete item file
compiled with `lcompile.py` in 9.1 seconds, with no errors or warnings.

## Proved and sorry left

Closed two existing holes:

- `AlgebraicGeometry.Etale.sfEtaleCompactProjectionInverse_naturality_left`.
- `AlgebraicGeometry.Etale.sfEtaleCompactProjectionInverse_naturality_right`.

Two original holes remain unchanged, both attached to
`lem-sf-etale-compact-projection-coherence`:

- `AlgebraicGeometry.Etale.sfEtaleCompactProjectionInverse_associativity`.
- `AlgebraicGeometry.Etale.sfEtaleCompactProjectionInverse_composition`.

Holes closed: 2. Holes added: 0. No decomposition.

## No longer needed

Removed unused direct private imports:

- `WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection`.
- `WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection`.
- `Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`.
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`.
- `Sheaf.AlgebraicGeometry.OpenImmersionProjectionComposition`.
- `Sheaf.Paper.RingedProjectionTensorComposition`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`.

Naturality requires only the existing natural transformation API and the
invertibility supplied by the unchanged public imports. No whole node or
module is obsolete: the original associativity and composition holes retain
all their original DAG dependencies and proof plans.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. Forward associativity is already proved in
`WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionAssoc`, theorem
`projectionMapOfCompactification_assoc`. Attempts to specialize an inverse
form to the present concrete coefficient category exceeded the single-file
compile limit; no such attempt is included or claimed as proved. The source
`TensorStructure.lean` documents the expensive concrete-coefficient monoidal
instance comparison relevant to this calculation.

The compatible-tower composition theorem does not immediately prove the law
for the specified `sfGraphCompactSupportCompIso`. Its graph-model and
proper/open projection squares still require an explicit pasting argument;
an unspecified composition isomorphism does not replace that specified map.

## Second reading by E1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
