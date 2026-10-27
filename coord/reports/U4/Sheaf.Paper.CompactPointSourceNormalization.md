## What changed

Proved `AlgebraicGeometry.Etale.CompactPointSource.compactPointSourceNormalization` without changing its statement or any public definition. The proof uses exact finite direct image, the proved equivalence of module sheaves on a separably closed point with modules, and compatibility of total right-derived units with composition. It proves the underived unit/section equation from adjunction uniqueness and upgrades it by naturality of the canonical augmentation. The normalized isomorphism is the inverse of `pointSection`; cancellation proves both equations and uniqueness.

Clean single-file compilation through `lcompile.py` passed in 55.9 seconds, with no Lean warnings or errors. All added proof imports passed the import-cycle check. The first delivery preflight found attachment metadata and a missing proof-command change record; both are repaired in this packet. Final delivery validation follows. Public statements and definition bodies are unchanged. The concrete augmentation is connected to a private generic construction by an equality theorem; its naturality and invertibility calculations use abstract abelian categories, avoiding repeated expansion of concrete sheafification and derived-category structures.

## Proved and sorry left

Closed 1 of 1 original holes: `AlgebraicGeometry.Etale.CompactPointSource.compactPointSourceNormalization` (node `lem-pur-compact-point-source-normalization`). Zero `sorry` holes remain in the item, and zero holes are added elsewhere. No statements were split off. All private helpers are proved.

## No longer needed

The proof does not use the following original proof dependencies (this is pruning of this argument, not withdrawal of source declarations):

- `lem-weil-pbc-module-sheaves-enough-injectives` (`Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives`).
- `lem-weil-pbc-left-exact-injective-resolution-degree-zero` (`Mathlib or no module`).
- `lem-trf-derived-sections-finite-pushforward-modules` (`Sheaf.TraceFormula.DerivedSectionsFinitePushforwardModules`).
- `lem-weil-pbc-geometric-point-cohomology` (`Sheaf.AlgebraicGeometry.GeometricPointCohomology`).
- `lem-weil-pbc-constant-sheaf-geometric-stalk` (`WeilConjectures.AlgebraicGeometry.ConstantSheafGeometricStalk`).
- `lem-weil-pbc-ringed-site-module-abelian-evaluation-comparison` (`Sheaf.CategoryTheory.ModuleAbelianEvaluationComparison`).
- `lem-weil-pbc-derived-single-fully-faithful` (`Mathlib or no module`).
- `lem-weil-pbc-right-derived-plus-injective` (`Mathlib or no module`).
- `lem-kun-rgamma-unbounded-bounded` (`Sheaf.AlgebraicGeometry.RGammaUnboundedBounded`).

Removed the corresponding private imports of `Sheaf.TraceFormula.DerivedSectionsFinitePushforwardModules`, `Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives`, `Sheaf.AlgebraicGeometry.GeometricPointCohomology`, `WeilConjectures.AlgebraicGeometry.ConstantSheafGeometricStalk`, `Sheaf.CategoryTheory.ModuleAbelianEvaluationComparison`, and `Sheaf.AlgebraicGeometry.RGammaUnboundedBounded`. Also removed `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory` as a redundant direct import (it is already public-imported by `WeilConjectures.SixFunctors.Finite.Exact`), `Mathlib.CategoryTheory.Abelian.RightDerived`, `Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful`, and `Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus`.

The seven obsolete `tool_uses` approvals attached to the original route were removed in their original order. Public imports remain unchanged. The argument avoids choosing a bounded-below resolution and avoids the module/abelian cohomology comparison, geometric-stalk identification, and full faithfulness of the single-complex embedding. The blueprint unit route remains unchanged.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The original DAG route is longer than needed: exactness and derived-composition units already show the specified augmentation is invertible, while the constant-pullback comparison was defined by exactly the adjunction uniqueness needed for the unit/section equation. The existing proved source-library equivalence and exact-derived-unit instance lacked directly matching DAG attachments; this delivery records them.

## New nodes

`lem-pur-point-constant-equivalence` records the existing proved source-library instance `AlgebraicGeometry.Scheme.isEquivalence_constantSheaf_of_isSepClosed` in `WeilConjectures.AlgebraicGeometry.Sites.PointConstantSheaf` (Stacks 03QT). No new Lean declaration or hole is added.

`lem-pur-exact-derived-unit` records the existing proved source-library instance `CategoryTheory.Functor.isIso_rightDerivedFunctorUnit` in `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory`. No new Lean declaration or hole is added. The proof-command change record is `coord/changes/U4-compact-point-proof-commands.md`; the downstream check reports zero consumer modules, and all public signatures and definition bodies remain unchanged.

## Second reading by U4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
