# AlgebraicGeometry.finiteFree_etale_local_actual (public imports)

## Reason

The new proof constructs local homotopies using the proved finite-free constant
sheaf lifting theorem and cone triangles. The ring-sheaf-module encoding in
`Sheaf.CategoryTheory.RingedSiteModules` is unused by both its statement and proof.
Remove that public import to prune the obsolete route. Import
`Mathlib.CategoryTheory.Sites.ConstantSheaf` publicly instead, since the existing
statement explicitly uses `constantSheaf`. Its old non-public import is thereby
promoted to its correct statement visibility. This is an import-surface change;
no existing declaration, binder, universe, hypothesis, definition or conclusion
changes. In particular no target statement changes and no target's meaning is
altered.

## Old

The original public imports, verbatim:

```lean
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.Homotopy
public import Sheaf.CategoryTheory.RingedSiteModules
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
```

## New

The replacement public imports, verbatim:

```lean
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
```

The theorem's complete signature is unchanged character for character. All other
new imports in the item are non-public proof imports. The supporting new module
has no existing consumers.

## Users

`tools/downstream.py Sheaf.Paper.FiniteFreeEtaleLocalActual --uses
AlgebraicGeometry.finiteFree_etale_local_actual` reports one downstream module,
`Sheaf.AlgebraicGeometry.FiniteRingDerivedLocalConstancy`. Its source imports the
item non-publicly and retains its original statement and proof. The queue lists
that module as unclaimed. It was copied unchanged into the sandbox for a server
compile against both new proof files, compiled successfully in 5.7 seconds, and
then removed from the delivery. No adaptation was needed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FiniteFreeEtaleLocalActual | K4 | Public imports pruned/replaced; theorem signature unchanged; one hole proved. |
| Sheaf.AlgebraicGeometry.FiniteRingDerivedLocalConstancy | unclaimed | Unchanged original compiles against the reduced public imports; no statement or proof change. |

The dependency scan's textual declaration-use list contains only the item's own
declaration; the consumer's theorem is still a named `sorry` in the repository.
That pre-existing consumer hole is not part of this delivery.

## Status

landed 20261018T062824-L-660524 2026-10-18 (merge of deliver/K4/Sheaf.Paper.FiniteFreeEtaleLocalActual)
