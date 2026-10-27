## What changed

Proved `WeilConjectures.PurityFiniteSetting.ordinaryDerivedIsomorphismTransport_transpose`
in the assigned module, preserving its complete signature and the transport definition.
Two fully proved private helpers normalize the exact-pullback derived adjunction and
identify the specified finite direct-image compositor with the conjugate of the specified
left-derived pullback compositor. The proof then uses counit naturality and the triangle
identity. Full faithfulness of derived pullback along the scheme isomorphism proves that
the actual unit, hence the transport, is invertible.

Added proof imports of
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CompConjugate` and
`WeilConjectures.Mathlib.CategoryTheory.Functor.Derived.Adjunction`.
Updated the node's proof, proof dependencies and proof origin to describe this route,
and removed its obsolete top-level tool approvals. Updated the proof docstring.
The final module compiled without errors or warnings after pruning the imports.
No source-library module, target, public declaration signature or definition changed.

## Proved and sorry left

Closed 1 of 1 existing holes:
`WeilConjectures.PurityFiniteSetting.ordinaryDerivedIsomorphismTransport_transpose`
(node `lem-pur-ordinary-derived-isomorphism-transport-transpose`).
Both private helpers, `mapDerivedAdjunction_eq` and `derivedComposition_conjugate`,
are proved. Holes added: 0. Holes remaining in the delivered module: 0.
No split-off statements and no new axioms.

## No longer needed

Removed the following original imports:

- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingComposition`
- `Sheaf.Paper.IntegralFinitePullbackComposition`
- `Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`
- `Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage`
- `Sheaf.AlgebraicGeometry.IsomorphismDerivedPullbackEquivalence`

The original proof dependencies below are no longer used by this proof:

- `def-weil-pbc-proetale-operations`: use the existing fixed-scalar adjunction API.
- `lem-coef-adjunction-equivalence-counit-iso`: use Mathlib's unit-isomorphism
  instance for a fully faithful left adjoint directly.
- `lem-pur-proetale-constant-ring-composition`: the fixed-scalar compositor
  already has the required coefficient presentation.
- `lem-sfb-ringed-derived-monoidal-comparisons`: the proved source-library
  right-derived compositor conjugacy theorem gives the exact comparison directly.
- `lem-weil-isomorphism-derived-pullback-equivalence`: the source equivalence
  of upperStar and its termwise derived equivalence suffice.
- `lem-weil-pbc-proetale-derived-pullback-composition`: use the actual fixed-scalar
  `leftDerivedUpperStarComp`, already present in the theorem's signature.
- `lem-weil-proetale-isomorphism-inverse-image`: use the source fixed-scalar
  `isEquivalence_upperStar` instance; no sectionwise ringed equivalence is needed.

Removed all three obsolete top-level `tool_uses` entries:
`lem-sfb-ringed-derived-monoidal-comparisons`,
`lem-weil-isomorphism-derived-pullback-equivalence`, and
`lem-pur-proetale-constant-ring-composition`.
These are removals from this item's proof route, not global withdrawals. Existing
statement dependencies are preserved; no module or node is deleted.

## Where the brief, the DAG or earlier work was wrong

The original argument is mathematically sound, but its planned ringed comparisons
are unnecessary for this fixed-scalar Lean statement. The source library already
proves that the universal right-derived compositor is the adjunction conjugate.
Its exact-pullback adjunction normalization must still be related to the actual
left-derived adjunction: the first private helper supplies that equality, so the
proof does not substitute arbitrary adjunctions or arbitrary comparison maps.
The DAG now records the finite-coefficient API actually used, rather than the
unused intrinsic ringed-presentation dependencies.

## Second reading by E1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
