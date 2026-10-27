/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q20
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.Sites.GeometricMorphism
public import Sheaf.CategoryTheory.Sites.ObjectDerivedSectionsPullback
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Sheaf.CategoryTheory.ContinuousCocontinuousToposAdjunctionForCoverings
import WeilConjectures.CategoryTheory.SiteCechComplex
import Sheaf.CategoryTheory.Sites.InjectiveModuleCechAcyclic
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Sheaf.CategoryTheory.LargeSetSheafification
import WeilConjectures.CategoryTheory.SiteCechVanishingCriterion
import Sheaf.CategoryTheory.Sites.ModuleDerivedEvaluationSlice
import Sheaf.CategoryTheory.Sites.CohomologyOverObjectLocalization

/-!
# Pulled-back injective modules are acyclic for object sections

Source: Stacks Project, Cohomology on Sites, Tag 0D6X and the Ext display in
Tag 07AC; Modules on Sites, Tags 03EJ and 03DI
(blueprint: lem-trf-module-pullback-injective-section-acyclic).

Ext is expressed in the injective-resolution convention of the node: the homology
of Hom from the sheafified free representable. The first conjunct identifies this
additive Hom functor naturally with object evaluation, fixing the identification
by evaluation on the identity generator. Applying it to an injective resolution
identifies the two complexes and hence their homology in every degree.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.ModulePullbackInjective

/-- The underlying ring sheaf of the specified commutative ring sheaf, using the
canonical forgetful functor. Source: Stacks, 0D6X
(blueprint: lem-trf-module-pullback-injective-section-acyclic). -/
abbrev coefficients {D : Type u} [SmallCategory D] (K : Precoverage D)
    (R : Sheaf K.toGrothendieck CommRingCat.{u}) : Sheaf K.toGrothendieck RingCat.{u} :=
  (sheafCompose K.toGrothendieck (forget₂ CommRingCat RingCat)).obj R

section

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  (J : Precoverage C) (K : Precoverage D)
  (hJ : J.IsSiteForCoverings) (hK : K.IsSiteForCoverings)
  (f : C ⥤ D)
  (hcover : ∀ (X : C) (S : Presieve X), S ∈ J X → S.map f ∈ K (f.obj X))
  (hpullback : ∀ (X Y Z : C) (S : Presieve X), S ∈ J X →
    ∀ (a : Y ⟶ X) (b : Z ⟶ X), S a → PreservesLimit (cospan a b) f)
  (R : Sheaf K.toGrothendieck CommRingCat.{u})

/-- The actual precomposition ring sheaf `R' = g⁻¹R`. Continuity is derived from
exactly the covering and covering-pullback conditions, using the existing public
helper `SiteObjectDerivedSections.continuous`. Cocontinuity identifies this
precomposition with inverse image under the induced geometric morphism.
Source: Stacks, Sites, 00WV and 00XR; Cohomology on Sites, 0D6X
(blueprint: lem-trf-module-pullback-injective-section-acyclic). -/
def inverseImageRing : Sheaf J.toGrothendieck RingCat.{u} :=
  letI := SiteObjectDerivedSections.continuous J K hJ hK f hcover hpullback
  (f.sheafPushforwardContinuous RingCat.{u} J.toGrothendieck K.toGrothendieck).obj
    (coefficients K R)

/-- The actual module precomposition, with its canonical action by the precomposed
ring. Mathlib calls this a continuous pushforward; by 00XR it is `g⁻¹` in the
cocontinuous variance used here. There is no independently chosen module or map.
Source: Stacks, Sites, 00XR and 00YV; Cohomology on Sites, 0D6X
(blueprint: lem-trf-module-pullback-injective-section-acyclic). -/
def inverseImage : ringedSiteModules.{u} (coefficients K R) ⥤
    ringedSiteModules.{u} (inverseImageRing J K hJ hK f hcover hpullback R) :=
  letI := SiteObjectDerivedSections.continuous J K hJ hK f hcover hpullback
  SheafOfModules.pushforward (F := f) (𝟙 (inverseImageRing J K hJ hK f hcover hpullback R))

end

/-- The object `E_U`: sheafification of the free module presheaf on `yoneda.obj U`.
Its sections before sheafification are finitely supported functions on arrows to U;
restrictions precompose their labels and apply the coefficient restriction.
Source: Stacks, Modules on Sites, 03EJ and 03DI; Cohomology on Sites, 07AC
(blueprint: lem-trf-module-pullback-injective-section-acyclic). -/
def freeRepresentable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (S : Sheaf J RingCat.{u}) (U : C) : ringedSiteModules.{u} S :=
  (PresheafOfModules.sheafification (𝟙 S.obj)).obj
    ((PresheafOfModules.free S.obj).obj (yoneda.obj U))

/-- The specified Hom/evaluation bijection, obtained from the actual sheafification
adjunction and the existing free-presheaf Yoneda equivalence. It sends a map to its
value on the identity basis vector after the sheafification unit.
Source: Stacks, Modules on Sites, 03EJ and 03DI; Cohomology on Sites, 07AC
(blueprint: lem-trf-module-pullback-injective-section-acyclic). -/
def homEvaluation {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (S : Sheaf J RingCat.{u}) (U : C) (N : ringedSiteModules.{u} S) :
    (freeRepresentable S U ⟶ N) ≃ N.val.obj (op U) :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 S.obj)).trans
    PresheafOfModules.freeYonedaEquiv

/-- The natural additive identification `Hom(E_U,-) = ev_U` and the vanishing
`Ext^p(E_U,g⁻¹I) = 0` in the node's module injective-resolution convention.
Positive integers are represented by natural numbers `p` with `0 < p`.
Source: Stacks, Cohomology on Sites, 0D6X and 07AC
(blueprint: lem-trf-module-pullback-injective-section-acyclic).

Proof:
1. The module category is Grothendieck abelian by
   lem-weil-pbc-ring-sheaves-grothendieck and has enough injectives by
   lem-sp-grothendieck-enough-injectives, so the resolutions quantified below exist.
2. The sheafification adjunction and lem-weil-pbc-free-yoneda-presheaf-module give
   homEvaluation. Its inverse sends r e_a to r times the restriction of the chosen
   section along a. These maps are additive and natural in the module; therefore
   they identify Hom(E_U,J^bullet) with J^bullet(U), including the differentials.
   Homology gives precisely Ext as right-derived module evaluation.
3. By lem-weil-pbc-continuous-cocontinuous-topos-adjunction, g⁻¹ is precomposition.
   Applying the finite-product-preserving functor to the module operations gives
   the ring and module precompositions used here, with the same restrictions.
4. For every source covering, continuity makes its image a target covering.
   Induction using preservation of pullbacks of covering arrows identifies each
   iterated fibre product after f with the target iterated fibre product.
   The face-map compatibilities follow from uniqueness in the universal properties
   of def-weil-pbc-site-cech-complex; no arbitrary pullback preservation is used.
5. Restriction along these comparisons identifies the two Cech complexes and their
   alternating differentials. Apply lem-weil-pbc-ringed-site-injective-module-cech-acyclic
   on the target to I. Its sheafification conditions follow from
   lem-cbc-module-sheafification-underlying-sets at integers and
   lem-weil-pbc-large-set-sheafification in the common universe.
6. Apply lem-weil-pbc-site-cech-vanishing-criterion with all objects and all covers.
   Every cover refines itself and every intersection is in the collection, giving
   zero positive ordinary abelian evaluation cohomology of the inverse image.
7. The module/abelian comparison lem-pe-ringed-site-derived-evaluation-slice and
   lem-weil-pbc-cohomology-over-object-localization identify module-derived object
   evaluation with that abelian evaluation cohomology, with the same slice topology.
   This does not assume that the underlying abelian sheaf of I is injective.
8. Apply the natural complex identification of step 2 to any module injective
   resolution of g⁻¹I. Its positive Hom homology is zero by steps 6 and 7. -/
theorem section_acyclic
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (J : Precoverage C) (K : Precoverage D)
    (hJ : J.IsSiteForCoverings) (hK : K.IsSiteForCoverings)
    (f : C ⥤ D)
    (hcover : ∀ (X : C) (S : Presieve X), S ∈ J X → S.map f ∈ K (f.obj X))
    (hpullback : ∀ (X Y Z : C) (S : Presieve X), S ∈ J X →
      ∀ (a : Y ⟶ X) (b : Z ⟶ X), S a → PreservesLimit (cospan a b) f)
    [f.IsCocontinuous J.toGrothendieck K.toGrothendieck]
    (R : Sheaf K.toGrothendieck CommRingCat.{u})
    (I : ringedSiteModules.{u} (coefficients K R)) [Injective I] (U : C) :
    (∃ e : preadditiveCoyoneda.obj
        (op (freeRepresentable (inverseImageRing J K hJ hK f hcover hpullback R) U)) ≅
        SheafOfModules.toSheaf (inverseImageRing J K hJ hK f hcover hpullback R) ⋙
          sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u} ⋙
          (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U),
      ∀ (N : ringedSiteModules.{u}
          (inverseImageRing J K hJ hK f hcover hpullback R))
        (a : freeRepresentable (inverseImageRing J K hJ hK f hcover hpullback R) U ⟶ N),
        (e.hom.app N) a = homEvaluation _ U N a) ∧
    ∀ (p : ℕ), 0 < p →
      ∀ L : InjectiveResolution ((inverseImage J K hJ hK f hcover hpullback R).obj I),
        IsZero (((preadditiveCoyoneda.obj
          (op (freeRepresentable (inverseImageRing J K hJ hK f hcover hpullback R) U)))
            |>.mapHomologicalComplex (.up ℕ)).obj L.cocomplex |>.homology p) := by
  sorry

end CategoryTheory.ModulePullbackInjective
