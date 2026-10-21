## What changed

Implemented the five-step argument for `AlgebraicGeometry.ProEtale.proEtaleOpenScalarCocycle`.
The ordinary coefficient/pullback pasting is proved by the mates equivalence and the
identity formulas for direct-image and restriction section maps. Exact-square composition
carries it to the unbounded derived categories. A generic conjugate-pasting argument gives
the normalized open cocycle, and a proved coordinate-transport lemma cancels the specified
open-model isomorphisms to obtain the exact displayed target equation.

The scalar-associator conjugate is separated into its own module and node. It is an
independent coefficient-normalization result and contains no geometric open functor.
It is needed at U and Z, and is strictly Step 3 of the original argument.

The unclaimed `Sheaf.Paper.BoundedConstructibleTower` uses direct aliases for the shared
ordinary extension, derived extension and counit interfaces; see the change record.
The old and new definitions are definitionally equal. No existing signature changes. The proof-only typeclass instances are local to their modules.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.ProEtale.proEtaleOpenScalarCocycle` (one of one).
The supporting `AlgebraicGeometry.ProEtale.scalarAssociatorConjugate` is also supplied
with a complete proof. There are no remaining `sorry`s in either module, and none in
the adapted `Sheaf.Paper.BoundedConstructibleTower` (which had zero originally).
Holes closed: one. Holes added: zero. No unfinished statement is split off.

All three modules passed packet compilation: bounded tower in 0.2 seconds (cached),
scalar-associator conjugate in 11.7 seconds, and the cocycle in 16.0 seconds.
The changed bounded-tower module also passed an uncached compile in 28.6 seconds.
The delivery command checks compilation and preflight of the complete packet before
pushing. Every compile uses the standard file limit; no limit is raised.

## No longer needed

No existing module or DAG node is withdrawn. The proof preserves the unit route.
Removed unused proof imports `Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction`
and `Mathlib.CategoryTheory.Localization.Predicate` from the working proof.
The scalar module uses the public bounded-tower interface through `FourCorners`,
without an additional `import all Sheaf.Paper.BoundedConstructibleTower`.
The main node no longer directly uses `lem-weil-pbc-localization-universal-property`,
`lem-sfb-successive-derived-quotient-normalization` or
`lem-weil-pbc-conjugate-iso-unit-equation`; the latter two belong to the new scalar node.
The localization step uses the existing exact-square composition theorem rather than
repeating a roof-level localization calculation. The successive-derived-quotient
normalization is used only inside the separate scalar-normalization lemma.

## Where the brief, the DAG or earlier work was wrong

The plan's mathematical argument is sound. Its Step 2 needs the ordinary mates calculation
and the canonical localization compositors to be explicit in Lean. The updated node names
the existing ordinary restriction-square and derived exact-square composition tools.
The generic and published scalar interfaces select the same tensor and universal counit
through different wrappers; aligning their aliases avoids expensive repeated unfolding.
The presentation uses the existing named object and map equations instead of projecting
the large existence specification again, and its functor definitions are locally
irreducible before the presentation is elaborated. The constructed comparison is
kept behind its proved defining equation, so projecting its hom or inverse after
specializing the coefficient rings does not expand the composite adjunction and
localization choices. Its selection theorem uniquely specifies the exact comparison
and is fully proved.
No target statement or coefficient interpretation changes.

## New nodes

`lem-sp-scalar-associator-conjugate`, attached to
`AlgebraicGeometry.ProEtale.scalarAssociatorConjugate` in
`Sheaf.SecSmoothPurity.ScalarAssociatorConjugate`: the right conjugate of the prescribed
balanced scalar associator is derived restriction composition.
The statement applies to arbitrary commutative ring maps, including identities,
nonflat maps and zero rings. It requires no finite, boundedness or nonempty assumption.

Change record: `coord/changes/E4-scalar-counit-alias.md`.

## Second reading by E4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
