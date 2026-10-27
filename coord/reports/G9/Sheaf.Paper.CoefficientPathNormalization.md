## What changed

Repair of the return at delivery head `42b1aaf6ab3`: restore the full item module
and its Lean-attached node, retaining the completed proof. The current shared snapshot
has neither the item source nor the quarantine archive/rework row named in the return.
The retained sandbox is therefore the restoration source; G9 still holds the item claim.
No withdrawal is requested. The restored signature matches the recorded node verbatim.
The current parent node `lem-sfb-coefficient-projection-square` now explicitly cites
this normalization when passing from the independent scalar tensor path to the specified
conjugate pull comparison. Its statement and Lean module are unchanged.

Proved `AlgebraicGeometry.ProEtale.CondensedRing.coefficientScalarPathIso_eq_derivedPullIso_symm`
with its statement unchanged. The proof compares the specified left-derived counits and
right-derived units on the homotopy category, pastes their normalization equations, and
uses localization and the adjunction Hom bijection to identify the conjugate. Scalar
restriction uses its specified exact-factorization transport. Added private proved
helpers for these elementary categorical calculations and private proof imports of
`WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates` and
`WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategoryCounit`.
Updated the node's proof and proof dependencies to match this direct calculation.
Preflight's command-environment check requires the proof-context change record
`coord/changes/G9-coefficient-path-normalization-proof-context.md`; all added
attributes are local and the public signature remains unchanged.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.ProEtale.CondensedRing.coefficientScalarPathIso_eq_derivedPullIso_symm`.
No holes added or split off. No `sorry` remains in the delivered module.
The repaired module compiles cleanly through `lcompile.py` in 56.2 seconds.
Static checks confirm the theorem signature matches its retained node verbatim,
all Lean lines meet the 100-character limit, and proof dependencies equal the union
of proof-step uses in both delivered nodes.

## No longer needed

The proof does not use `lem-sfb-derived-composition-adjunction-normalization` or its
module `Sheaf.CategoryTheory.DerivedCategory.CompositionAdjunctionNormalization`:
the unit equations of the specified composition comparisons suffice directly.
No existing import was removed and no module was withdrawn. The other declared
proof dependencies remain used through their stated constructions and instances.

## Where the brief, the DAG or earlier work was wrong

The return describes a quarantine archive and rework row which are absent from the
current shared snapshot. This repair restores the retained source and DAG attachment
rather than treating their absence as authorization to withdraw them.

The planned auxiliary composition-adjunction normalization theorem is unnecessary
for this square. The source statement and its specified adjunctions need no repair.

## New nodes

No new mathematical statement is introduced. The returned node
`lem-sfb-coefficient-left-derived-path-normalization` is restored with its original
statement and Lean attachment, and the completed direct proof route. Its parent
`lem-sfb-coefficient-projection-square` again explicitly depends on this normalization.
Change record: `coord/changes/G9-coefficient-path-normalization-proof-context.md`.

## Second reading by G9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
