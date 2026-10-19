## What changed

Completed `AlgebraicGeometry.Scheme.ProEt.isIso_of_isIso_basis_derivedEvaluation`
without changing its statement or any existing definition. Retained and checked the
previous attempt's proof against current sources, removed unused proof imports, and
updated its proof documentation and DAG route.

The proof represents both objects by bounded-below injective complexes and lifts the
morphism to a chain map. Naturality of the right-derived-functor unit shows that each
basis evaluation is a quasi-isomorphism. The proved private helpers
`sheafifiedHomologyIso` and `quasiIso_of_basis_evaluation` identify sheafified presheaf
homology with sheaf homology and apply dense-subsite detection on the affine basis.
Localization and conjugation finish the proof. No cones or slice-site comparison
are needed. Only the item module and its node are changed.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.ProEt.isIso_of_isIso_basis_derivedEvaluation`
(node `lem-weil-pbc-basis-derived-detection`).

No `sorry` remains in the item module; no holes or split-off modules are added.
Both private helpers are fully proved. The retained import-pruned module was rechecked against the current published build
through `lcompile.py`: it compiled cleanly in 15.9 seconds on 2026-10-19.

## No longer needed

Removed proof imports:

- `Sheaf.CategoryTheory.RingedSiteGrothendieckAbelian`
- `Mathlib.Algebra.Category.Grp.AB`
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian`
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits`
- `Mathlib.Algebra.Category.Ring.Limits`
- `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic`
- `Sheaf.CategoryTheory.ExtensionByZeroPresheaf`
- `Mathlib.Algebra.Homology.DerivedCategory.Plus`
- `WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic`
- `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`
- `Sheaf.AlgebraicGeometry.ProEtaleRestrictionInjectives`
- `WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian`

The removed basic imports are supplied by the retained public statement imports.
The extension-by-zero generator construction and the specialized Grothendieck
module are unnecessary: the existing `SheafOfModules.isGrothendieckAbelian` theorem
already supplies enough injectives. The cone module and module-presheaf
sheafification module are unnecessary for the direct abelian homology-map argument.

Removed proof dependencies:

- `lem-weil-pbc-proetale-restriction-injectives`
  (`Sheaf.AlgebraicGeometry.ProEtaleRestrictionInjectives`): evaluation's own
  right-derived-functor unit already computes evaluation on injective complexes.
- `lem-weil-pbc-derived-plus-iso-on-cohomology`: localization directly reflects
  quasi-isomorphisms of the evaluated chain map.
- `lem-pur-quasi-iso-cone-acyclic`
  (`WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic`): work with
  homology maps directly. Its obsolete top-level tool-use approval is withdrawn.
- `lem-weil-pbc-ringed-site-module-sheafification-exact` and
  `def-weil-presheaf-modules-sheafification`
  (`Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`): use exact abelian
  sheafification (`lem-weil-pbc-sheafification-exact`) and the exact, conservative
  forgetful functor to abelian sheaves instead.

The Grothendieck, enough-injectives, injective-representative, K-injective lifting,
affine-basis and derived-localization inputs remain needed. No unit statement or
unit proof step is bypassed. Existing public imports are preserved.

## Where the brief, the DAG or earlier work was wrong

The retained proof draft compiled, but its report omitted the change from cones to
homology maps and it had no corresponding DAG update. These records are corrected.
The mathematical statement needs no repair. The direct proof does not need
restriction to the localized site or module-valued presheaf sheafification; exact
abelian sheafification and dense-subsite comparison suffice. It never identifies
sections of sheaf homology with homology of sections.

## Second reading by T3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
