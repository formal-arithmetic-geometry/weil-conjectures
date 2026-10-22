## What changed

Proved `AlgebraicGeometry.ProEtale.CondensedRing.upperStarTensorComplexHom_comm` in the
assigned source module. A proved private helper checks the total differential on each
bidegree summand. Naturality of the ordinary lax tensorator identifies the two differential
terms, and additivity preserves their sum and the sign. Coproduct extensionality then gives
the chain-map equation. This follows proof step 4 of
`new-proetale-derived-module-pullback-monoidal`.

Added private proof imports for the total-tensor differential formula and its cochain
instances. Proved private proposition caches reuse existing sheaf-category properties.
The factorization theorem supplies the six arguments to `Functor.leftDerived₂_fac`
explicitly. Synchronous elaboration retains full kernel checking. Public signatures, imports, attributes and
construction data are preserved.

Change record: `coord/changes/P1-derived-monoidal-differential-proof.md`.
The returned delivery changed the local priorities of two still-unproved upstream instances.
Removed both added priority attributes. The complete source blocks of
`isLeftDerivedFunctor₂_upperStarTensor` and `isIso_leftDerivedUpperStarTensor` now match
current main verbatim; neither their signatures, bodies nor attributes are changed.
The source-only hole gate reports no violations. The repaired source compiled successfully in 55.7 seconds. An importing axiom check
confirmed that `upperStarTensorComplexHom_comm` depends only on `propext`,
`Classical.choice` and `Quot.sound`. The unchanged direct consumer
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarUnitCoherence`
compiled against the repaired artifact in 37.9 seconds. Diagnostic files are excluded
from the delivery.

## Proved and sorry left

Closed one of the ten original holes:
`AlgebraicGeometry.ProEtale.CondensedRing.upperStarTensorComplexHom_comm`.
No holes were added or split off. Every private helper is proved.

The following nine original holes remain in the assigned module. They belong to the
construction described by `new-proetale-derived-module-pullback-monoidal`, whose existing
Lean attachment remains the companion module:

- `AlgebraicGeometry.ProEtale.CondensedRing.upperStarTensorCounit`: naturality in each variable
  (two holes).
- `AlgebraicGeometry.ProEtale.CondensedRing.isLeftDerivedFunctor₂_upperStarTensor`: one hole.
- `AlgebraicGeometry.ProEtale.CondensedRing.leftDerivedUpperStarTensorLeftCounit`:
  naturality in each variable (two holes).
- `AlgebraicGeometry.ProEtale.CondensedRing.isIso_leftDerivedUpperStarTensor`: one hole.
- `AlgebraicGeometry.ProEtale.CondensedRing.monoidal_leftDerivedUpperStar`: associativity,
  left unitality and right unitality (three holes).

## No longer needed

No adopted module, declaration or existing public import is withdrawn. The differential
proof needs only the elementary total-tensor formula; it does not require the full
canonical monoidal comparison on complexes, flatness preservation, derived-counit
normalization or derived coherence. The dependencies planned for the nine remaining
holes stay in the DAG. No global pruning is claimed. In particular,
`lem-weil-pbc-left-adjoint-preserves-colimits` is unnecessary for the closed chain-map
substep: coproduct descent defines its forward comparison. The colimit-preservation
edge stays available for the inverse comparison and the other parts of the node.

Removed two provisional private imports after pruning checks:
`Mathlib.CategoryTheory.Limits.HasLimits` and `Mathlib.Logic.Small.Defs`. These were
sandbox experiments, not adopted imports. The cochain instance import is retained:
removing it together with those two imports exceeds the compiler limit. The provisional API extractions, companion adaptations
and new nodes are also excluded.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy was found in the statement proved. The original module
already requires substantial typeclass elaboration even with its original holes.
The proof uses explicit differential formulas and proved proposition caches while
preserving the source-library data boundary and the compiler's time limit.

The return at c0005dcbb65 identified changed holed instance blocks. Those changes were
the two trailing local priority attributes, now removed. The original holed instances
are retained without modification; no replacement hole, witness or data is introduced.
No whole-library build is claimed.

## Second reading by P1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
