## What changed

Proved `CategoryTheory.exists_perfect_constant_local_chain_representative` with its original
signature and three construction helpers unchanged. A right fraction gives an acyclic cone;
a local null homotopy and exactness of the distinguished cone triangle give a homotopy right
inverse. Naturality of the canonical derived-factorization comparison gives the stated equality.

Added two proved support modules: `PerfectConstantLocalNullHomotopy` implements finite descending
homotopy induction on actual covering presieves; `PerfectConstantLocalLift` proves degreewise
lifting on arbitrary slices and independent site universes. The latter lifts finitely many
generators, factors the whole map through the sectionwise image, applies module projectivity,
and extends by the sheafification universal property. Saturation induction refines covering
sieves to actual covering presieves using precisely `IsSiteForCoverings`.

Updated the DAG and proof docstrings to the implemented route. No existing statement, definition,
universe, or public import changed. No consumer adaptations or change records are needed.

## Proved and sorry left

Closed 1 of 1 original holes:
`CategoryTheory.exists_perfect_constant_local_chain_representative`
(`lem-sfb-perfect-constant-local-chain-representative`).

Both new support theorems are proved:
`CategoryTheory.exists_perfect_constant_local_null_homotopy`
(`lem-sfb-perfect-constant-local-null-homotopy`) and
`CategoryTheory.exists_perfect_constant_local_lift` (`lem-sfb-perfect-constant-local-lift`).
Every private helper is proved. No holes were added; no `sorry` remains in the three delivered
modules. This closes one original hole with zero unresolved split-offs. Existing exactness
infrastructure is used as declared; this does not assert that the entire target closure is
sorry-free. The degreewise lifting theorem itself uses no unproved existence theorem.

Validation: all three modules compiled through `lcompile.py --all`. On resumption, all three
compiled again; the existing theorem signature and three construction definitions are identical
to current sources. Added the missing LeanSearch records to both new nodes after the dry-run
metadata check identified their omission. The lifting theorem needs
an explicit elaboration heartbeat budget for scalar restrictions and slice comparisons, and
compiles within the unchanged 60-second file limit. Edge cases checked in the argument: zero
module, empty generating family, zero ring, identity and empty covers, nonfree projective
modules, and unrelated object/arrow universes. Neither the denominator nor target needs bounds.

## No longer needed

Removed the assigned module's direct proof imports
`Mathlib.CategoryTheory.Localization.CalculusOfFractions`,
`WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful`,
`Mathlib.CategoryTheory.Sites.EpiMono`,
`WeilConjectures.CategoryTheory.SiteCoveringsCommonRefinement`,
`Mathlib.CategoryTheory.Abelian.FunctorCategory`, `Mathlib.CategoryTheory.Sites.Abelian`, and
`Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`, and
`Sheaf.CategoryTheory.SiteConstantModuleFunctorGeneral` (already publicly available through
`SiteDerivedConstantModuleFunctor`).

The assigned node no longer directly uses `lem-pc-quasi-isomorphisms-multiplicative-system`,
`lem-weil-pbc-module-sheaves-colimits-forgetful`,
`lem-weil-pbc-site-abelian-sheaf-epi-locally-surjective`,
`lem-weil-pbc-site-coverings-common-refinement`, or
`lem-weil-pbc-site-module-presheaf-sheafification-exact`. The forgetful and local-epi facts
remain used below the lifting theorem. Mathlib's derived right-fraction API already packages
the multiplicative-system instance. The common-refinement module is unnecessary throughout
this reduction: finite intersection of covering sieves and the proved actual-cover refinement
replace it. Removed its and the forgetful lemma's obsolete direct `tool_uses` approvals from
the assigned node. The cone-acyclicity approval stays.

The new lifting module does not need `SiteDerivedConstantModuleFunctor` or
`RingedDerivedRestrictionGeneral`; it uses `SiteConstantModuleFunctorGeneral` directly.
It also needs no finite-free comparison, finite-free local-lift module, or exactness of the
constant-module functor. Those facts remain relevant to other declarations where indicated.
No whole existing module is withdrawn; no blueprint unit or unit proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No statement dispute. The original plan called general-slice finite-projective lifting
elementary without a declaration packaging it. The retained attempt isolated this obligation
but left it unproved. This session closes it using the module sheafification Hom API and the
projective lifting property. It also proves actual-cover refinement without strengthening the
site axioms to Mathlib's stronger indexed-composition axiom. Distinguished-triangle exactness
replaces the equivalent explicit cone-component calculation.

## New nodes

`lem-sfb-perfect-constant-local-null-homotopy`, module
`Sheaf.CategoryTheory.PerfectConstantLocalNullHomotopy`, isolates and proves original Step 5
from degreewise lifting, exact restriction, and actual-presieve transitivity.

`lem-sfb-perfect-constant-local-lift`, module `Sheaf.CategoryTheory.PerfectConstantLocalLift`,
isolates and proves original Steps 1 and 4 by finite generation, local epimorphism lifting,
projectivity and the constant-module sheafification universal property. No unresolved work
remains in either new node, and no definition chooses arbitrary data from an unproved theorem.

## Second reading by G7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
