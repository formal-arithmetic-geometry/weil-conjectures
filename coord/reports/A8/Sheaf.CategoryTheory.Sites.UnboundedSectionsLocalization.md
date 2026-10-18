## What changed

Proved `CategoryTheory.UnboundedSectionsLocalization.unboundedSectionsLocalization`
in `Sheaf.CategoryTheory.Sites.UnboundedSectionsLocalization` using the already proved
`Functor.rightDerivedFunctorCompIso` for restriction followed by evaluation on the slice.
The underived composite is definitionally evaluation at W. The proof checks the specified
normalization on every K-injective representative from `rightDerivedNatTrans_app` and
naturality along `quotientCompQhIso`; applying homology to the resulting component proves
the assertion for every integer degree. The two private helpers `compUnit_app` and
`compIso_objQ` prove the categorical unit calculations completely.

Reproved the existing proposition-valued instance `modulesGrothendieck` with the already
proved source theorem `SheafOfModules.isGrothendieckAbelian`, specialized to the common
universe in this module. This removes the unproved independent-universe transport theorem
from the module's dependencies. Reproved `restrictionAdditive` directly by
sectionwise extensionality, removing its unnecessary reliance on the localized adjunction
and local Hom-complex interface. Its signature and every other existing signature are
unchanged. Updated the main theorem's proof docstring and the existing node's proof route.
The composition module and source small-site Grothendieck module are proof-only imports.
Added the direct public Mathlib `DerivedCategory.HomologySequence` import because the
unchanged statement uses its `homologyFunctor`, previously visible through a pruned import.
No definitions or target statements change.

## Proved and sorry left

Closed the original hole:
`CategoryTheory.UnboundedSectionsLocalization.unboundedSectionsLocalization`
(node `lem-sfb-unbounded-sections-localization`).

Original holes: 1. Closed: 1. Added: 0. Remaining in the item: 0. No split-offs.
The general independent-universe Grothendieck theorem is pruned in favor of its already
proved common-universe special case. Localized restriction preserving K-injectives is used
as an existing declaration; this delivery does not assert that all its dependencies are proved.

## No longer needed

Removed these direct imports:

- `Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses`: the existing proved
  source `SheafOfModules.isGrothendieckAbelian` applies directly because this module already
  puts the site, its morphisms, and coefficient values in one universe. The general
  independent-universe transport theorem and its derived-limit imports are unnecessary.
- `Sheaf.CategoryTheory.SiteCoveringAxioms`: no covering-family presentation is used;
  the statement takes a Grothendieck topology directly.
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`: the theorem already
  uses the source library's `rightDerivedFunctor`, so no separately chosen universal pair
  for arbitrary quasi-isomorphic resolutions is used.
- `Sheaf.Algebra.Homology.RhomIntoKInjectiveLocal`: its only previously used result was
  zero preservation for the additivity proof; additivity is proved directly sectionwise.
  The local sheaf Hom complex and its derived-Hom computation are unnecessary here.
- `Sheaf.Algebra.Homology.LocalizedRestrictionAdjunction`: no separate adjunction is
  needed for additivity; K-injective preservation is supplied by its existing theorem.
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`: the existing
  Grothendieck-abelian instance supplies the general K-injective-resolution instance.
  Neither the specified free-sheaf generator nor functorial resolutions with injective
  terms are needed. The corresponding node `prop-pur-kinjective-resolutions-exist` is
  removed from the direct proof dependencies and obsolete tool approvals.
- `Mathlib.Algebra.Homology.DerivedCategory.KInjective`: there is no separate invocation
  of `Qh_map_bijective`. The direct dependency `lem-weil-pbc-kinjective-hom-derived`
  is replaced by the existing proved derived-composition theorem, which encapsulates
  the descent from K-injective representatives.

`sk-def-sfb-derived-categories` remains a statement convention; its separate theorem
module and direct proof dependency are unnecessary. The parent unit and its route remain
in place. The retained direct proof dependencies are localized restriction preserving K-injectives, the sectionwise
localized-site definition, and the closed generic composition node
`lem-fin-kinjective-derived-composition` (using its underlying `rightDerivedFunctorCompIso`).
No new module is needed. The existing source small-site Grothendieck theorem supplies
the common-universe case of the Grothendieck property used by the statement.

Change record: `coord/changes/UnboundedSectionsLocalization.md`. The downstream
check found no consumers requiring adaptation.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was changed or found false. The original plan separately invoked
a resolution theorem for commutative ring sheaves even though this module permits arbitrary
ring sheaves; the already proved common-universe source Grothendieck theorem supplies all the
resolution hypotheses used here without the unproved general-universe theorem. The original imports also brought in a separate right
derived-functor construction and an entire local Hom-complex interface which the proof does
not use. The existing closed composition API gives naturality directly and allows a short,
explicit check of the required representative normalization.

The normalization and homology argument work equally for zero complexes, a final W,
negative cohomological degrees, and complexes unbounded in both directions. No boundedness,
commutativity, extra site hypothesis, or new existence assumption was introduced.

## Second reading by A8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
