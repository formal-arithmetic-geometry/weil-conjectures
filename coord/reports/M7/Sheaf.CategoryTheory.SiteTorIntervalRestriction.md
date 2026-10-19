## What changed

Proved `CategoryTheory.siteTorIntervalRestriction` without changing its signature.
The proof applies the existing ringed-site bounded flat model equivalence twice,
restricting the model termwise between the two applications. It transports flatness
between explicit site tensor and monoidal tensor using `siteSheafTensorRightIso`,
then applies `SheafOfModules.isFlat_over`. Mathlib's exact-functor derived-category
comparison identifies the canonical-representative restriction with this model,
with the two derived Hom universes kept independent.

Updated the declaration's proof explanation and its DAG proof route. All three public
imports remain unchanged. Added only proof imports of RingedSiteTorFlatModel,
TensorColimitsIndependentCoefficients, and Mathlib's DerivedCategory.ExactFunctor.
SliceRestrictionFlat and LocalizedModuleExactForSystems remain proof imports.

The new generic tool dependencies are `lem-sp-ringed-site-tor-flat-model` (the existing
arbitrary-ringed-site form of Stacks 08G1) and
`lem-weil-pbc-independent-sheaf-tensor-colimits` (its proved natural comparison of
site and monoidal tensor). Neither replaces a geometric step or a unit statement;
the unit's fixed-window local-model route is retained. Its realized fields are empty.

Validation: lcompile.py recompiled the complete proof against the current published library.
Corrected a docstring-ending style warning found during this retry.
The source passages read were sites-cohomology.tex, lemma-tor-amplitude (08G1) and
lemma-tor-amplitude-pullback (08H5). The proof works for a=b, E=0, a zero coefficient
ring, and sites without enough points: no nonzero term or stalk is selected. It uses
only the supplied a<=b and quantifies over every slice test sheaf.

## Proved and sorry left

Closed one of one original holes: `CategoryTheory.siteTorIntervalRestriction`
(node `lem-sf-site-tor-interval-restriction`). Zero holes remain in the item; zero
holes were added and zero statements were split off. This is a proof from existing
stated dependencies, including the existing holed bounded-flat-model equivalence
and localized exactness statement, not an axiom-free completion of those dependencies.

## No longer needed

Removed direct proof imports:

- Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
- Sheaf.Algebra.Homology.BoundedFlatReplacement
- Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
- Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorClosed
- Sheaf.CategoryTheory.RingedSiteGrothendieckAbelian
- Mathlib.Algebra.Category.Grp.AB
- Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
- Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
- Mathlib.Algebra.Category.Ring.Limits
- Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
- Sheaf.CategoryTheory.ExtensionByZeroPresheaf
- Sheaf.CategoryTheory.LocalizedModuleExactIndependent
- WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
- WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
- WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
- Sheaf.Algebra.Homology.KFlat
- Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
- Sheaf.Paper.SfCommonStageWeilCohomology
- WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian

The original direct proof dependencies now subsumed by the existing ringed-site
bounded-flat-model theorem are def-pc-kflat-complex,
def-pc-tensor-complex-sheaves, def-weil-derived-cohomology-sheaves,
lem-pc-bounded-above-flat-kflat-site, lem-pc-kflat-bounded-flat-replacement,
lem-pc-kflat-resolution, lem-pc-sheaf-modules-tensor-closed,
lem-pc-tensor-mapping-cone-iso, lem-pur-quasi-iso-cone-acyclic,
lem-weil-pbc-site-derived-tensor-descent. They are not individually used in this
proof, although some remain transitive dependencies of the model equivalence.
`lem-pur-ringed-site-grothendieck-abelian` and
`lem-sc-source-tor-amplitude-flat-model` are no longer direct inputs: no native
categorical tensor or functorial-flat-resolution instance needs to be assembled here.
Removed their obsolete top-level tool approvals, retaining the exact-restriction and
slice-flatness approvals. No global module withdrawal is claimed; the delivery checker
computes whether any removed direct imports also leave the target import closure.

## Where the brief, the DAG or earlier work was wrong

The original plan is mathematically valid, but an existing ringed-site specialization
already packages its flat-model construction and arbitrary-test-sheaf tensor calculation.
Using that equivalence avoids rebuilding the native tensor comparison. The original
LocalizedModuleExactIndependent import has successor-universe assumptions that do not
fit arbitrary small C : Type u; the recorded LocalizedModuleExactForSystems interface
specializes to the required universes, and all three exactness clauses are used.

No statement or definition was repaired. No new nodes were needed.

## Second reading by M7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
