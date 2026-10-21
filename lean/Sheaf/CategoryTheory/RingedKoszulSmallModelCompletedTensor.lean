/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import Sheaf.CategoryTheory.LocallyDerivedRingedIdealComplete
public import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
public import Sheaf.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence

/-! # Local completeness and completed tensor through the canonical small model

Source: Stacks Project, Tags 0999, 099B and 0A0E
(blueprint: def-sf-koszul-small-model-completed-tensor).
The site, coefficient and derived morphism universes remain independent. The local
completeness predicate is transported from the existing small-site construction.
No completion reflector is chosen or asserted to exist by this definition module.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u v r w w₀
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory
namespace KoszulSmallModel

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{r})

/-- The coefficient sheaf restricted along the canonical small-model equivalence.
Source: Stacks 0A0E (blueprint: def-sf-koszul-small-model-completed-tensor). -/
def ring : Sheaf ((equivSmallModel.{r} C).inverse.inducedTopology J) CommRingCat.{r} :=
  ((equivSmallModel.{r} C).inverse.sheafPushforwardContinuous CommRingCat.{r}
    ((equivSmallModel.{r} C).inverse.inducedTopology J) J).obj R

/-- Restrict the finite global generating list to the canonical small model.
Source: Stacks 0A0E (blueprint: def-sf-koszul-small-model-completed-tensor). -/
def globalSection (b : (R.obj ⋙ forget CommRingCat.{r}).sections) :
    ((ring R).obj ⋙ forget CommRingCat.{r}).sections :=
  ⟨fun U ↦ b.val ((equivSmallModel.{r} C).inverse.op.obj U),
    fun f ↦ b.property ((equivSmallModel.{r} C).inverse.op.map f)⟩

/-- Module sheaves on the original site, using the recorded general-site category.
Source: Stacks 03DA (blueprint: def-sf-koszul-small-model-completed-tensor). -/
abbrev Modules := ringedSiteModules.{r}
  ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)

set_option backward.isDefEq.respectTransparency false in
/-- The canonical module-sheaf equivalence induced by restriction to the small model.
Both structural ring maps come from the equivalence unit; no arbitrary equivalence is used.
Source: Stacks 03DA and 0A0E
(blueprint: def-sf-koszul-small-model-completed-tensor). -/
def modulesEquiv : Modules R ≌ ringedSiteModules.{r}
    ((sheafCompose _ (forget₂ CommRingCat.{r} RingCat.{r})).obj (ring R)) := by
  let e := equivSmallModel.{r} C
  let K := e.inverse.inducedTopology J
  let S := (sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R
  let S' := (sheafCompose K (forget₂ CommRingCat.{r} RingCat.{r})).obj (ring R)
  let φ : S ⟶ (e.functor.sheafPushforwardContinuous RingCat.{r} J K).obj S' :=
    ⟨Functor.whiskerRight (NatTrans.op e.unitInv) S.obj⟩
  let ψ : S' ⟶ (e.inverse.sheafPushforwardContinuous RingCat.{r} K J).obj S := 𝟙 _
  exact (SheafOfModules.pushforwardPushforwardEquivalence.{r} e φ ψ
    (NatTrans.ext (funext fun U ↦ by
      change S.obj.map (e.inverse.map (e.counit.app U.unop)).op =
        S.obj.map (e.unitInv.app (e.inverse.obj U.unop)).op
      rw [e.unitInv_app_inverse]))
    (NatTrans.ext (funext fun U ↦ by
      change S.obj.map (e.unitInv.app U.unop).op ≫
        (𝟙 _ ≫ S.obj.map (e.unit.app U.unop).op) = 𝟙 _
      rw [Category.id_comp, ← S.obj.map_comp, ← op_comp, e.unitIso.hom_inv_id_app]
      exact S.obj.map_id _))).symm

variable [HasDerivedCategory.{w} (Modules R)]
  [HasDerivedCategory.{w₀} (ringedSiteModules.{r}
    ((sheafCompose _ (forget₂ CommRingCat.{r} RingCat.{r})).obj (ring R)))]

/-- The derived equivalence induced by the actual site restriction equivalence.
Source: Stacks 0A0E (blueprint: def-sf-koszul-small-model-completed-tensor). -/
def derivedEquiv : DerivedCategory (Modules R) ≌ ringedSiteDerived (ring R) :=
  letI : (modulesEquiv R).functor.Additive :=
    Functor.additive_of_preserves_binary_products _
  letI : (modulesEquiv R).inverse.Additive :=
    Functor.additive_of_preserves_binary_products _
  (modulesEquiv R).mapDerivedCategory

variable [∀ U : SmallModel.{r} C, HasDerivedCategory.{w₀} (SheafOfModules.{r}
  ((sheafCompose (((equivSmallModel.{r} C).inverse.inducedTopology J).over U)
    (forget₂ CommRingCat.{r} RingCat.{r})).obj ((ring R).over U)))]

/-- Local derived completeness, transported through the canonical equivalence of sites.
This is the existing local internal-Hom vanishing predicate, including all local ideal
sections on all slices; no cohomological boundedness or exactness of products is imposed.
Source: Stacks 0999 and 099F
(blueprint: def-sf-koszul-small-model-completed-tensor). -/
def complete
    (I : ringedSiteModules.{r}
      ((sheafCompose _ (forget₂ CommRingCat.{r} RingCat.{r})).obj (ring R)))
    (ι : I ⟶ SheafOfModules.unit.{r}
      ((sheafCompose _ (forget₂ CommRingCat.{r} RingCat.{r})).obj (ring R))) :
    ObjectProperty (DerivedCategory (Modules R)) :=
  fun M ↦ IsLocallyDerivedRingedIdealComplete (ring R) I ι ((derivedEquiv R).functor.obj M)

end KoszulSmallModel

namespace DerivedCompletedTensor

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{r})
  [HasDerivedCategory.{w} (KoszulSmallModel.Modules R)]
  [HasDerivedCategory.{w₀} (ringedSiteModules.{r}
    ((sheafCompose _ (forget₂ CommRingCat.{r} RingCat.{r})).obj (KoszulSmallModel.ring R)))]
  [∀ U : SmallModel.{r} C, HasDerivedCategory.{w₀} (SheafOfModules.{r}
    ((sheafCompose (((equivSmallModel.{r} C).inverse.inducedTopology J).over U)
      (forget₂ CommRingCat.{r} RingCat.{r})).obj ((KoszulSmallModel.ring R).over U)))]
  (I : ringedSiteModules.{r}
    ((sheafCompose _ (forget₂ CommRingCat.{r} RingCat.{r})).obj (KoszulSmallModel.ring R)))
  (ι : I ⟶ SheafOfModules.unit.{r}
    ((sheafCompose _ (forget₂ CommRingCat.{r} RingCat.{r})).obj (KoszulSmallModel.ring R)))

/-- Completed tensor is the specified K-flat-derived tensor restricted to complete objects,
followed by the supplied functor L. For a completion reflector this is B(M,N)=L(T(M,N)).
This specializes ordinary functor composition; no reflector is chosen by this definition.
Source: blueprint def-wf-tensor-product, coefficient tensor model; Stacks 0A0E
(blueprint: def-sf-koszul-small-model-completed-tensor). -/
abbrev tensor (L : DerivedCategory (KoszulSmallModel.Modules R) ⥤
    (KoszulSmallModel.complete R I ι).FullSubcategory) :=
  ((KoszulSmallModel.complete R I ι).ι.prod (KoszulSmallModel.complete R I ι).ι) ⋙
    SheafOfModules.siteDerivedTensorIndependentCoefficients J R ⋙ L

end DerivedCompletedTensor
end CategoryTheory
