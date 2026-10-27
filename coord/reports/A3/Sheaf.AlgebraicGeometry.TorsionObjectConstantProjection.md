## What changed

Proved `AlgebraicGeometry.Etale.isIso_rightDerivedLowerStarProjectionMap_constant_of_torsion_object`
in `Sheaf.AlgebraicGeometry.TorsionObjectConstantProjection`, preserving its exact signature and
all public imports. The proof restricts the existing projection transformation to derived
constant complexes and applies `CategoryTheory.derivedModuleFreeGeneration`.

The substantive coproduct step proves annihilation of every tensor by applying the additive
right-tensor functor to `N • id_E = 0`. The existing fixed-exponent coproduct theorem then gives
preservation by derived direct image of this particular family. No preservation for all
objects over an arbitrary coefficient ring is assumed. The unit, shifts, triangle and retract
steps use existing etale and category-theory APIs. Evaluation at `M[0]` is transported by
`Functor.mapDerivedCategorySingleFunctor` to the original displayed map.

Added proof imports of `Sheaf.AlgebraicGeometry.FixedExponentDerivedCoproducts` and
`WeilConjectures.SixFunctors.Etale.Derived.ConstantTensorProjection`. Updated the existing
DAG node's proof, proof dependencies and proof origin, and removed its two obsolete generic
tool approvals. No definitions, statements, consumers or source-library files changed. The static checker
requires a change record for the added namespace/scoped-notation openings:
`coord/changes/a3-torsion-object-projection-proof-opens.md`. The consumer check reports no
downstream modules and only this item as a textual user.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Etale.isIso_rightDerivedLowerStarProjectionMap_constant_of_torsion_object`
(node `lem-sf-projection-torsion-object-constant`). Zero holes remain in the item; zero holes
were added or split off. This is a proof from existing declarations, including the existing
unfinished theorem
`AlgebraicGeometry.Etale.isIso_sigmaComparison_rightDerivedLowerStar_of_fixedExponent`
(node `lem-sf-fixed-exponent-derived-coproducts`); it is not a claim that the whole dependency
closure is now free of sorry.

The server single-file compiler checked the proof. Delivery preflight also checks the exact
statement, all declared axioms, formatting and packet consistency.

## No longer needed

Removed direct proof imports:

- `Sheaf.AlgebraicGeometry.Sites.TorsionEtaleCohomologicalDimension` (available through the
  finite-dimension and fixed-exponent interfaces).
- `Sheaf.AlgebraicGeometry.EtaleConstantProjectionMap`: the proof uses the existing relative
  etale projection transformation directly; no absolute global-sections projection map.
- `Sheaf.Paper.ProjectionMateExact`: existing etale shift, exactness and unit APIs suffice.
- `Sheaf.SixFunctors.GeometricInverseImageConstantModule`: the conclusion is already stated
  with the derived inverse image, so no separate ringed-site constant-module identification.
- `Mathlib.CategoryTheory.Adjunction.Limits`,
  `WeilConjectures.Mathlib.CategoryTheory.Triangulated.Functor`, and
  `Mathlib.Algebra.Homology.Additive`: needed APIs remain available transitively; these
  redundant direct imports are removed.

The proof no longer needs nodes `def-kun-constant-projection-morphism`,
`lem-weil-pbc-ringed-projection-mate-exact`, or
`lem-sfb-geometric-inverse-image-constant-module`; removed them from `proof_deps` and removed
the latter two obsolete `tool_uses` entries. The relative dimension definition, left-adjoint
coproduct result and triangle result remain used through their existing interfaces. No
module was withdrawn, and no assertion is made that a removed direct import is globally
unreachable: the ledger computes that independently.

## Where the brief, the DAG or earlier work was wrong

The proposed route is mathematically sound. Its detour through a separate general
`SheafOfModules` projection mate and constant inverse-image comparison is unnecessary for
the actual Lean conclusion. Existing etale APIs already refer to exactly the required mate.
The original imports also omitted the fixed-exponent coproduct module actually needed by
Step 3; it is now imported explicitly.

All original hypotheses remain, although the argument uses only the fixed annihilator and
finite relative torsion cohomological dimension. There is no finite-generation hypothesis
on M and no change of coefficient ring. Empty coproducts and zero objects are handled by
the same coproduct and generation interfaces; exponent 1 forces E to be zero and needs no
exception. The associated unit route is unchanged.

## Second reading by A3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
