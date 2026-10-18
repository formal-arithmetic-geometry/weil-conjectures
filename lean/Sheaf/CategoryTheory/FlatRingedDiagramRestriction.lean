/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q124; NA stage-2 revalidation
-/
module

public import Sheaf.CategoryTheory.FlatRingedDiagramRestrictionComparisonAdjuncts
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Sheaf.CategoryTheory.DiagramSiteRealization
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Sites.Limits
import Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral
import Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Sheaf.CategoryTheory.GeometricModuleTransport
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.CategoryTheory.KInjectiveTotalDerived
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
import Sheaf.CategoryTheory.DerivedCategory.EssentiallyConstantInd
import Sheaf.CategoryTheory.DerivedCategory.EssentiallyConstantPro
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Sheaf.CategoryTheory.RingedSiteModules

/-!
# Flat coefficient restriction on derived module diagrams

Source: Stacks Project, Derived Categories, Tags 0FND and 0DVC; Modules on Sites,
Tag 03D3, specialized to compatible flat coefficient changes on diagram sites
(blueprint: lem-weil-pbc-flat-ringed-diagram-restriction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory
namespace FlatRingedDiagramInput

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {K : GrothendieckTopology C} {H : GrothendieckTopology D}
  (x : FlatRingedDiagramInput K H) (J : Type u) [SmallCategory J]
  [HasDerivedCategory.{w} (x.diagramsRU J)]
  [HasDerivedCategory.{w} (x.diagramsSU J)]
  [HasDerivedCategory.{w} (x.diagramsRV J)]
  [HasDerivedCategory.{w} (x.diagramsSV J)]
/-- Flat coefficient restriction is exact, preserves K-injective diagram complexes,
and has canonical inverse-image and right-derived-direct-image comparisons compatible
with the normalized derived adjunctions. The supplied derived functors have universal
right-derived units, invertible on K-injectives, and the representative transpose
formula of 0FND. These specify the
chosen derived operations. The factor isomorphisms identify rU and rV
with exact localization of the actual termwise restriction functors. The b equation
is exact localization of the ordinary comparison. The d equation is its universal
right-derived-unit normalization, in particular the identity on K-injectives.

Source: Stacks 0FND, 0DVC and 03D3, specialized to compatible flat coefficient changes
on the product diagram sites
(blueprint: lem-weil-pbc-flat-ringed-diagram-restriction).

Proof plan (the ten steps of the node, grouped by construction):
1. Use lem-weil-pbc-diagram-site-realization to realize the four diagram categories
as sheaves of modules on the small product sites. All subsequent maps are maps of
these diagram categories; no equality is inferred only from derived evaluations.
2. Restriction changes only the scalar action. Kernels are computed sectionwise
and cokernels by sheafification, so restriction is exact. Tensor extension is its
left adjoint. Flatness makes that adjoint exact, also on diagrams, since kernels,
cokernels and tensor extension are pointwise. An exact left adjoint sends acyclic
complexes to acyclic complexes; the complex Hom adjunction and homotopy adjunction
therefore show that restriction preserves K-injectives.
3. The structural ring square identifies the two inverse-image actions. The
identity on identified inverse-image sheaves is linear and natural, giving b0.
The adjoint ring square similarly identifies the direct-image actions, giving d0.
These are identities on every sheaf and diagram transition. Exact localization
gives rU, rV and b with their displayed factor and normalization equations.
4. Choose K-injective diagram resolutions. Their restrictions remain K-injective
by step 2, so both right-derived images are computed by the same ordinary diagram
identity d0. This defines d and proves it invertible. The universal right-derived
units extend this construction naturally and give the displayed equation on all
complexes. On a K-injective I both units are isomorphisms, exactly the stated
normalization of d at QI; computesR and computesS supply these isomorphisms.
5. The underlying set-sheaf adjunction identifies b0 and d0 as mates, by the
transpose equations of the input. Apply the fraction-normalized Hom comparison
of lem-pc-pre-derived-adjoint-functors-general. For its representing cocone, choose
a resolution s0: K → I0 and set p_s = RF(Qs)⁻¹ β_I, with splitting
ρ = β_I0⁻¹ RF(Qs0). A common refinement into a K-injective diagram gives
QF(a) ρ p_s = QF(c). For the exact left-derived functor use the cone
u_t = QG(t)⁻¹ ∘ φ_M and splitting φ_M⁻¹; the dual fraction equation holds.
These supply the essential-constancy hypotheses, rather than assuming them.
On a K-injective target the identity
of step 4 and the ordinary transpose equation give the final displayed adjunct
equation. Represent arbitrary derived morphisms by fractions and use naturality
and invertibility of their denominators to obtain the equation for every M,N,t.
All constructions occur in full diagram categories, retaining every J-arrow. -/
theorem flatRingedDiagramRestriction
    (LR : derivedRV x J ⥤ derivedRU x J)
    (FR : derivedRU x J ⥤ derivedRV x J)
    (qLR : DerivedCategory.Q ⋙ LR ≅
      inverseRComplex x J ⋙ DerivedCategory.Q)
    (ηR : directRComplex x J ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ FR)
    (aR : LR ⊣ FR)
    (derivedR : FR.IsRightDerivedFunctor ηR
      (HomologicalComplex.quasiIso (x.diagramsRU J) (.up ℤ)))
    (computesR : ∀ I : cochainRU x J,
      I.IsKInjective → IsIso (ηR.app I))
    (transposeR : ∀ (P : cochainRV x J)
      (I : cochainRU x J)
      (f : (inverseRComplex x J).obj P ⟶ I),
      aR.homEquiv (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj I)
        (qLR.hom.app P ≫ DerivedCategory.Q.map f) =
      DerivedCategory.Q.map
        (((Adjunction.whiskerRight J x.R.adjunction).mapHomologicalComplex (.up ℤ)).homEquiv
          P I f) ≫ ηR.app I)
    (LS : derivedSV x J ⥤ derivedSU x J)
    (FS : derivedSU x J ⥤ derivedSV x J)
    (qLS : DerivedCategory.Q ⋙ LS ≅
      inverseSComplex x J ⋙ DerivedCategory.Q)
    (ηS : directSComplex x J ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ FS)
    (aS : LS ⊣ FS)
    (derivedS : FS.IsRightDerivedFunctor ηS
      (HomologicalComplex.quasiIso (x.diagramsSU J) (.up ℤ)))
    (computesS : ∀ I : cochainSU x J,
      I.IsKInjective → IsIso (ηS.app I))
    (transposeS : ∀ (P : cochainSV x J)
      (I : cochainSU x J)
      (f : (inverseSComplex x J).obj P ⟶ I),
      aS.homEquiv (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj I)
        (qLS.hom.app P ≫ DerivedCategory.Q.map f) =
      DerivedCategory.Q.map
        (((Adjunction.whiskerRight J x.S.adjunction).mapHomologicalComplex (.up ℤ)).homEquiv
          P I f) ≫ ηS.app I) :
    PreservesFiniteLimits (x.restrictU J) ∧
    PreservesFiniteColimits (x.restrictU J) ∧
    PreservesFiniteLimits (x.restrictV J) ∧
    PreservesFiniteColimits (x.restrictV J) ∧
    (∀ I : cochainSU x J, I.IsKInjective →
      CochainComplex.IsKInjective ((restrictUComplex x J).obj I)) ∧
    (∀ I : cochainSV x J, I.IsKInjective →
      CochainComplex.IsKInjective ((restrictVComplex x J).obj I)) ∧
    Nonempty (DerivedRestrictionComparison (x := x) (J := J) LR FR qLR ηR aR LS FS qLS ηS aS) := by
  sorry


end FlatRingedDiagramInput
end CategoryTheory
