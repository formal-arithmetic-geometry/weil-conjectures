## What changed

Proved AlgebraicGeometry.Etale.scalarCompositeMateAdjunct with its signature unchanged.
Added three proved private helpers: transport of a mate counit along left-adjoint
isomorphisms, the exact-pullback/compositor counit equation, and the categorical
calculation combining those equations with scalar/pullback composition coherence.
The final specialization uses scalarPullback_composition and the defining scalarMate
counit equation. All scalar mates retain their given orientation.

Replaced the private RingedDerivedMonoidalComparisons import by private imports of
WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CompConjugate and
WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarAdjunctionCompat. Updated the
node's proof and proof dependencies to record the exact-adjunction normalization route.
No public signature, definition, or public import changed.

## Proved and sorry left

Closed 1 of 1 holes: AlgebraicGeometry.Etale.scalarCompositeMateAdjunct
(lem-pur-scalar-composite-mate-adjunct). Added 0 holes; split off 0 statements.
No sorry remains in any delivered module. All three private helpers have complete proofs.

## No longer needed

Removed private import Sheaf.SixFunctors.RingedDerivedMonoidalComparisons and removed
lem-sfb-ringed-derived-monoidal-comparisons from this node's proof dependencies and
obsolete tool_uses entry. The constant-ring specialization has an existing exact
adjunction normalization theorem, so the full simultaneous monoidal ringed-topos
system is unnecessary for this argument. This is pruning of this dependency edge;
other consumers may still need the module. Retained ScalarPullbackComposition and
all public imports used by the original interface. No module was withdrawn.

## Where the brief, the DAG or earlier work was wrong

The original proof plan was mathematically sound. Its first step requested more
structure than this calculation needs: the existing exact-adjunction compositor
normalization directly identifies the specified rightDerivedFunctorCompIso'.
The node now records this specialization. The unit route is preserved: the same
composite-mate adjunct equality is proved using the specified comparisons, without
boundedness, properness, or flatness assumptions. No new mathematical statements
or definition repairs were required.

## Second reading by P4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
