## What changed

Filled the four theorem proofs in `Sheaf.Paper.ShriekCoefficientIsomorphism`.
Scalar restriction is an additive equivalence, so its derived functor is a triangulated
coproduct-preserving equivalence. Explicit inverse-restriction isomorphisms and the
existing constant-model theorem identify the constructible finite-Tor classes. Private
proved helpers establish their invariance under isomorphisms. Applying minimality to
inverse images of localizing properties identifies the localizing closures and their
full subcategories. Essential surjectivity and the canonical compactification comparison
transfer preservation. The canonical right mate gives the right-adjoint comparison;
the adjunction hom equivalence proves its counit equation and uniqueness, and the same
comparison transports constructibility in both directions.

Kept all public signatures. Scoped transparency during proof elaboration avoids
expanding geometric pullback constructions. Made the intermediate functors in the
existing compactification comparison explicit, preserving its canonical composite.
Updated the existing node's proof and dependency list to describe the implemented route.
The comparison elaboration refactor is recorded in
`coord/changes/shriek-coefficient-comparison-elaboration.md`.

## Proved and sorry left

Closed four holes:

- `AlgebraicGeometry.ProEtale.shriekCoefficientIso_transport`.
- `AlgebraicGeometry.ProEtale.shriekCoefficientIso_localizing`.
- `AlgebraicGeometry.ProEtale.shriekCoefficientIso_preservesLocalizing`.
- `AlgebraicGeometry.ProEtale.shriekCoefficientIso_adjoints`.

No holes added, no holes split off, and no `sorry` remains in the delivered Lean module.
The existing dependencies are used as stated; no claim is made that their transitive
proof dependencies are all sorry-free. The argument applies unchanged to zero
coefficient rings and empty schemes.

## No longer needed

Removed the unused public import
`Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions` (none of these
statements uses its alternate right-derived construction), the proof import
`Sheaf.CategoryTheory.GrothendieckDerivedCoproductsColimit`
and the dependency/tool-use `lem-kun-grothendieck-derived-coproducts` from this node.
No separate construction of coproducts is needed to prove preservation: equivalences
preserve every existing coproduct. The intersection argument only requires preservation
of those colimits that exist. No module is withdrawn, and this does not assert the
coproduct module is unnecessary to other consumers. The blueprint unit route is kept.

## Where the brief, the DAG or earlier work was wrong

The DAG's separate coproduct-construction step is unnecessary for this statement.
Its original exact-equivalence, compactification-comparison, and mate arguments work
with the existing declarations. No mathematical statement was changed and no disputed
statement was used to weaken the conclusion.

## Second reading by M2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
