## What changed

Proved `CategoryTheory.ringedDerivedPushforward_linear` in the assigned module,
with the original signature. Private constructions give the central section
endomorphisms and their ring maps into End(M), hence the required Hom scalar actions.
The adjunction calculation first proves that the zero generalized element transposes
to zero, then proves preservation of scalar identity endomorphisms.

The derived argument uses the full essentially surjective functor from K-injective
complexes with homotopy-class morphisms to the derived category. The canonical derived
unit is invertible on this category. Transporting additivity and linearity along that
unit and then descending along this functor proves the properties of exactly the
existing canonical right derived functor. No exactness of module direct image is used.

Validation: the final module compiles cleanly through `lcompile.py` in 21.0 seconds.
The theorem signature was compared verbatim with the repository original; all Lean
lines satisfy the 100-character limit. Both replacement proof/interface imports pass
`tools/import_direction.py may`. There are no current Lean importers to adapt.

Updated the node's proof, proof dependencies and proof origin to this route. Pruned
redundant direct imports; the public import change is recorded in
`coord/changes/B9-ringed-derived-pushforward-imports.md`.

## Proved and sorry left

Closed the original hole in `CategoryTheory.ringedDerivedPushforward_linear`
(node `lem-pur-ringed-derived-pushforward-linear`). One of one holes closed;
zero holes added or split off. No sorry remains in any delivered Lean declaration.
All private helpers are fully proved or explicit constructions.

## No longer needed

The direct public import `Sheaf.CategoryTheory.KInjectiveDerivedMapComputation`
and node `lem-sf-kinjective-derived-map-computation` are not used by this proof.
Its arbitrary-resolution map and transition formulas are replaced by restriction
of the derived unit to K-injective complexes. The needed canonical derived-functor
interface is imported directly from
`Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`.

The direct public import `Sheaf.CategoryTheory.Sites.RGammaDerivedLimit` is removed;
`Mathlib.Algebra.Category.Grp.FilteredColimits` supplies the standard small-site
abelian-sheaf prerequisites needed by the statement. This does not claim that RGamma
is globally unused: the existing Grothendieck theorem still imports it transitively.

The proof import
`WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective`
is replaced by `WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution`.
The injectivity of each resolution term is not needed. The existing stronger node
`lem-pur-kinjective-degreewise-existence` remains a dependency for its K-injective
quasi-isomorphism clause. No source-library declaration is changed or withdrawn.
No unit statement or realized proof step is bypassed; the item's unit has no
realized steps. No other planned dependency or maintainer-approved tool is pruned.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition was found. The planned map-by-map resolution
calculation is unnecessary: Mathlib's transfer lemmas give a shorter proof through
the restricted canonical unit. The right-derived-functor definition is used directly
and is now explicitly listed as a proof dependency; previously it was available only
through the arbitrary-resolution computation module.

## Second reading by B9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
