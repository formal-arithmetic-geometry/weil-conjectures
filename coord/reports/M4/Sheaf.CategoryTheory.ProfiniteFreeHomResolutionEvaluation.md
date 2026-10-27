## What changed

In `Sheaf.CategoryTheory.ProfiniteFreeHomResolutionEvaluation`, proved
`CategoryTheory.CondensedBar.ProfiniteHom.hom_additive_leftExact` using the existing
`Mod.ihom'Adjunction`: its right adjoint preserves limits, hence binary products, and
Mathlib's `Functor.additive_of_preserves_binary_products` gives additivity.
Added the private proof import `Mathlib.CategoryTheory.Preadditive.AdditiveFunctor`.
All declaration signatures and public imports are unchanged. The remaining existence
proof and its planned dependency route are unchanged.

## Proved and sorry left

Closed 1 of the item's original 2 holes:
`CategoryTheory.CondensedBar.ProfiniteHom.hom_additive_leftExact`.

One original hole remains, unchanged:
`CategoryTheory.CondensedBar.ProfiniteHom.exists_evaluation`, node
`lem-sfb-profinite-free-hom-resolution-evaluation`. Its existing docstring retains the
complete six-step proof plan and sources. No holes were added or split off.

The final module compiled cleanly with the server single-file compiler in 13.6 seconds,
with the cleaned imports and no linter warning. No consumer interface changed.

## No longer needed

Removed private proof imports:

- `WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian`
- `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives`
- `Mathlib.Topology.Separation.Hausdorff`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed`
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`

These direct imports are unnecessary for the current declarations and the proved
adjunction argument. The remaining K-injective-resolution import supplies the resolution
infrastructure used by `enough`. No DAG node or module is withdrawn or claimed pruned:
the unchanged `exists_evaluation` still requires its recorded proof plan. In particular,
removing unused direct imports here does not assert that their mathematical statements
are unnecessary for that remaining theorem.

## Where the brief, the DAG or earlier work was wrong

None. This is the partial delivery expressly allowed for a module with several holes:
one proved and the other untouched. The standalone additivity proof follows its existing
docstring directly and does not require the generator-evaluation theorem. Searches used
LeanFinder, Loogle, the Mathlib grep service, and local searches in both library roots.

## Second reading by M4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
