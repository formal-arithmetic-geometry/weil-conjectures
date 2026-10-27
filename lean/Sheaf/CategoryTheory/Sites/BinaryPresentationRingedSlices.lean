/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V5
-/
module
public import Sheaf.CategoryTheory.Sites.BinaryPresentationModuleData
import all Sheaf.CategoryTheory.RingedEquivalenceSlices
import Sheaf.CategoryTheory.GeometricModuleConstruction
import Sheaf.CategoryTheory.RingedEquivalenceModuleHom
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Ringed localized nerve equivalences -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.MonoidalCategory
namespace CategoryTheory

section
variable {C E : Type u} [SmallCategory C] [SmallCategory E]
  {J : GrothendieckTopology C} {K : GrothendieckTopology E}
  (F : E ⥤ Sheaf J (Type u)) (N : Sheaf J (Type u) ≌ Sheaf K (Type u))
  (hN : N.functor ⋙ sheafToPresheaf K (Type u) ≅ sheafSubcategoryNerve F)
  (Z : E) (S : Over (F.obj Z) ≌ Sheaf (K.over Z) (Type u))
  (hS : S.functor ⋙ sheafToPresheaf (K.over Z) (Type u) ≅
    yoneda ⋙ (Functor.whiskeringLeft (Over Z)ᵒᵖ
      (Over (F.obj Z))ᵒᵖ (Type u)).obj (Over.post F).op)

private def productOverHomEquiv (M : Sheaf J (Type u)) (A : Over Z) :
    (F.obj A.left ⟶ M) ≃ ((Over.post F).obj A ⟶ (productOver (F.obj Z)).obj M) where
  toFun f := Over.homMk (CartesianMonoidalCategory.lift (F.map A.hom) f) (by
    exact CartesianMonoidalCategory.lift_fst _ _)
  invFun f := f.left ≫ CartesianMonoidalCategory.snd _ _
  left_inv f := CartesianMonoidalCategory.lift_snd _ _
  right_inv f := by
    apply Over.OverMorphism.ext
    apply CartesianMonoidalCategory.hom_ext
    · exact (CartesianMonoidalCategory.lift_fst _ _).trans (Over.w f).symm
    · change CartesianMonoidalCategory.lift _ _ ≫ _ = _
      simp only [CartesianMonoidalCategory.lift_snd]

private def productNerveIso :
    N.functor ⋙ K.overPullback (Type u) Z ≅ productOver (F.obj Z) ⋙ S.functor := by
  apply Functor.fullyFaithfulCancelRight (sheafToPresheaf (K.over Z) (Type u))
  refine ?_ ≪≫ (Functor.isoWhiskerLeft (productOver (F.obj Z)) hS).symm
  refine NatIso.ofComponents (fun M ↦ NatIso.ofComponents (fun A ↦
    ((((hN.app M).app (op A.unop.left)).toEquiv).trans
      (productOverHomEquiv F Z M A.unop)).toIso) ?_) ?_
  · intro A B f
    ext s
    apply Over.OverMorphism.ext
    change CartesianMonoidalCategory.lift (F.map B.unop.hom) _ =
      F.map f.unop.left ≫ CartesianMonoidalCategory.lift (F.map A.unop.hom) _
    apply CartesianMonoidalCategory.hom_ext
    · simp only [CartesianMonoidalCategory.lift_fst]
      exact (F.map_comp f.unop.left A.unop.hom).symm.trans
        (congrArg F.map (Over.w f.unop)) |>.symm
    · simp only [CartesianMonoidalCategory.lift_snd]
      exact ConcreteCategory.congr_hom ((hN.hom.app M).naturality f.unop.left.op) s
  · intro M M' f
    ext A s
    apply Over.OverMorphism.ext
    apply CartesianMonoidalCategory.hom_ext
    · ext T x
      rfl
    · have hn := congrArg (fun a ↦ a.app (op A.unop.left) s) (hN.hom.naturality f)
      exact hn

private def sliceSetComparison (R : Sheaf J RingCat.{u})
    (source : RingedSheafSliceAdjunctionData R (F.obj Z)) :
    N.functor ⋙ K.overPullback (Type u) Z ≅
      elementSheafPullback (F.obj Z) ⋙ (source.fibreEquivalence.functor ⋙ S.functor) := by
  let p := productFibreIso (F.obj Z) source
  exact productNerveIso F N hN Z S hS ≪≫
    (Functor.isoWhiskerRight (Functor.rightUnitor _).symm S.functor) ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (productOver (F.obj Z))
        source.fibreEquivalence.counitIso.symm) S.functor ≪≫
    Functor.isoWhiskerRight (Functor.associator _ _ _).symm S.functor ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerRight p source.fibreEquivalence.functor)
      S.functor ≪≫ Functor.associator _ _ _

end

set_option backward.isDefEq.respectTransparency false in
-- Transport the ring operations through the product/fibre comparison.
private def nerveSliceRingData {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J CommRingCat.{u}} {S : Sheaf K CommRingCat.{u}}
    (e : RingedToposMorphism (localCoefficientRings R) (localCoefficientRings S))
    (A : Sheaf K (Type u)) (Z : C)
    (H : Sheaf (elementTopology A) (Type u) ≌ Sheaf (J.over Z) (Type u))
    (q : e.inverse ⋙ J.overPullback (Type u) Z ≅
      elementSheafPullback A ⋙ H.functor) :
    RingedToposMorphism.RingData
      (localCoefficientRings (R.over Z))
      (localCoefficientRings (presentationElementRing S A)) where
  inverse := H.functor
  direct := H.inverse
  adj := H.toAdjunction
  leftExact := inferInstance
  ringMap := q.inv.app (ringSets (localCoefficientRings S)) ≫
    (J.overPullback (Type u) Z).map e.ringMap
  ring_zero := by
    intro T z hz U t
    have he : e.inverse.map (ringZero (localCoefficientRings S)) ≫ e.ringMap =
        RingedToposMorphism.RingData.zero _ := by
      ext V x
      exact e.ring_zero _ _ (fun _ _ ↦ rfl) V x
    have hz' : z = CartesianMonoidalCategory.toUnit T ≫
        (elementSheafPullback A).map (ringZero (localCoefficientRings S)) := by
      ext V x
      exact hz V x
    have hn := q.inv.naturality (ringZero (localCoefficientRings S))
    have hn' := congrArg (fun f ↦ f ≫
      (J.overPullback (Type u) Z).map e.ringMap) hn
    change H.functor.map ((elementSheafPullback A).map
        (ringZero (localCoefficientRings S))) ≫ q.inv.app _ ≫ _ = _ at hn'
    change _ = q.inv.app _ ≫
      (J.overPullback (Type u) Z).map (e.inverse.map _ ) ≫
        (J.overPullback (Type u) Z).map e.ringMap at hn'
    rw [← Functor.map_comp, he] at hn'
    have hz'' := congrArg (fun f ↦ H.functor.map f ≫
      (q.inv.app (ringSets (localCoefficientRings S)) ≫
        (J.overPullback (Type u) Z).map e.ringMap)) hz'
    simp only [Functor.map_comp, Category.assoc] at hz''
    rw [hn'] at hz''
    exact (congrArg (fun f ↦ f.hom.app U t) hz'').trans (by rfl)
  ring_one := by
    intro T z hz U t
    have he : e.inverse.map (ringOne (localCoefficientRings S)) ≫ e.ringMap =
        RingedToposMorphism.RingData.one _ := by
      ext V x
      exact e.ring_one _ _ (fun _ _ ↦ rfl) V x
    have hz' : z = CartesianMonoidalCategory.toUnit T ≫
        (elementSheafPullback A).map (ringOne (localCoefficientRings S)) := by
      ext V x
      exact hz V x
    have hn := q.inv.naturality (ringOne (localCoefficientRings S))
    have hn' := congrArg (fun f ↦ f ≫
      (J.overPullback (Type u) Z).map e.ringMap) hn
    change H.functor.map ((elementSheafPullback A).map
        (ringOne (localCoefficientRings S))) ≫ q.inv.app _ ≫ _ = _ at hn'
    change _ = q.inv.app _ ≫
      (J.overPullback (Type u) Z).map (e.inverse.map _ ) ≫
        (J.overPullback (Type u) Z).map e.ringMap at hn'
    rw [← Functor.map_comp, he] at hn'
    have hz'' := congrArg (fun f ↦ H.functor.map f ≫
      (q.inv.app (ringSets (localCoefficientRings S)) ≫
        (J.overPullback (Type u) Z).map e.ringMap)) hz'
    simp only [Functor.map_comp, Category.assoc] at hz''
    rw [hn'] at hz''
    exact (congrArg (fun f ↦ f.hom.app U t) hz'').trans (by rfl)
  ring_add := by
    intro T x y z hz U t
    change T ⟶ (elementSheafPullback A).obj (ringSets (localCoefficientRings S)) at x y z
    have h := congrArg (J.overPullback (Type u) Z).map (ringData_add e.ringData)
    simp only [Functor.map_comp] at h
    have h' := binary_conjugate q
      (CartesianMonoidalCategory.fst _ _) (CartesianMonoidalCategory.snd _ _)
      (ringAdd (localCoefficientRings S))
      ((J.overPullback (Type u) Z).map e.ringMap)
      ((J.overPullback (Type u) Z).map e.ringMap)
      ((J.overPullback (Type u) Z).map e.ringMap)
      (ringAdd (localCoefficientRings (R.over Z))) h
    have hz' := ringAdd_eq
      (localCoefficientRings (presentationElementRing S A)) x y z hz
    have h'' : H.functor.map z ≫ (q.inv.app (ringSets (localCoefficientRings S)) ≫
        (J.overPullback (Type u) Z).map e.ringMap) =
        CartesianMonoidalCategory.lift
          (H.functor.map x ≫ q.inv.app (ringSets (localCoefficientRings S)) ≫
            (J.overPullback (Type u) Z).map e.ringMap)
          (H.functor.map y ≫ q.inv.app (ringSets (localCoefficientRings S)) ≫
            (J.overPullback (Type u) Z).map e.ringMap) ≫
          ringAdd (localCoefficientRings (R.over Z)) := by
      rw [hz', Functor.map_comp, Category.assoc]
      change H.functor.map (CartesianMonoidalCategory.lift x y) ≫
        ((elementSheafPullback A ⋙ H.functor).map (ringAdd (localCoefficientRings S)) ≫
          q.inv.app (ringSets (localCoefficientRings S)) ≫ _) = _
      rw [h', CartesianMonoidalCategory.comp_lift_assoc]
      have hf : CartesianMonoidalCategory.lift x y ≫ (elementSheafPullback A).map
          (CartesianMonoidalCategory.fst (ringSets (localCoefficientRings S))
            (ringSets (localCoefficientRings S))) = x := by ext V v; rfl
      have hs : CartesianMonoidalCategory.lift x y ≫ (elementSheafPullback A).map
          (CartesianMonoidalCategory.snd (ringSets (localCoefficientRings S))
            (ringSets (localCoefficientRings S))) = y := by ext V v; rfl
      simp only [Functor.comp_map, ← Category.assoc, ← H.functor.map_comp, hf, hs]
    exact congrArg (fun f ↦ f.hom.app U t) h''
  ring_mul := by
    intro T x y z hz U t
    change T ⟶ (elementSheafPullback A).obj (ringSets (localCoefficientRings S)) at x y z
    have h := congrArg (J.overPullback (Type u) Z).map (ringData_mul e.ringData)
    simp only [Functor.map_comp] at h
    have h' := binary_conjugate q
      (CartesianMonoidalCategory.fst _ _) (CartesianMonoidalCategory.snd _ _)
      (ringMul (localCoefficientRings S))
      ((J.overPullback (Type u) Z).map e.ringMap)
      ((J.overPullback (Type u) Z).map e.ringMap)
      ((J.overPullback (Type u) Z).map e.ringMap)
      (ringMul (localCoefficientRings (R.over Z))) h
    have hz' := ringMul_eq
      (localCoefficientRings (presentationElementRing S A)) x y z hz
    have h'' : H.functor.map z ≫ (q.inv.app (ringSets (localCoefficientRings S)) ≫
        (J.overPullback (Type u) Z).map e.ringMap) =
        CartesianMonoidalCategory.lift
          (H.functor.map x ≫ q.inv.app (ringSets (localCoefficientRings S)) ≫
            (J.overPullback (Type u) Z).map e.ringMap)
          (H.functor.map y ≫ q.inv.app (ringSets (localCoefficientRings S)) ≫
            (J.overPullback (Type u) Z).map e.ringMap) ≫
          ringMul (localCoefficientRings (R.over Z)) := by
      rw [hz', Functor.map_comp, Category.assoc]
      change H.functor.map (CartesianMonoidalCategory.lift x y) ≫
        ((elementSheafPullback A ⋙ H.functor).map (ringMul (localCoefficientRings S)) ≫
          q.inv.app (ringSets (localCoefficientRings S)) ≫ _) = _
      rw [h', CartesianMonoidalCategory.comp_lift_assoc]
      have hf : CartesianMonoidalCategory.lift x y ≫ (elementSheafPullback A).map
          (CartesianMonoidalCategory.fst (ringSets (localCoefficientRings S))
            (ringSets (localCoefficientRings S))) = x := by ext V v; rfl
      have hs : CartesianMonoidalCategory.lift x y ≫ (elementSheafPullback A).map
          (CartesianMonoidalCategory.snd (ringSets (localCoefficientRings S))
            (ringSets (localCoefficientRings S))) = y := by ext V v; rfl
      simp only [Functor.comp_map, ← Category.assoc, ← H.functor.map_comp, hf, hs]
    exact congrArg (fun f ↦ f.hom.app U t) h''
private theorem sliceModulesExist
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J CommRingCat.{u}} {S : Sheaf K CommRingCat.{u}}
    (g : RingedToposMorphism (localCoefficientRings S) (localCoefficientRings R))
    [g.inverse.IsEquivalence] [IsIso g.ringMap] :
    Nonempty (BinaryPresentationModules g) := by
  obtain ⟨T, ⟨p⟩, a, ha⟩ := ringed_equivalence_module_hom g
  let h := Functor.additive_of_preserves_binary_products T.modules.functor
  let k := Functor.additive_of_preserves_binary_products T.modules.inverse
  let := HasDerivedCategory.standard (PresentationModules R)
  let := HasDerivedCategory.standard (PresentationModules S)
  let := h
  let := k
  exact ⟨{
    modules := T.modules
    additive := h
    inverseAdditive := k
    finiteLimits := inferInstance
    finiteColimits := inferInstance
    inverseFiniteLimits := inferInstance
    inverseFiniteColimits := inferInstance
    underlying := a
    unit := T.forwardUnit
    structural := ha
    pushforward := p
    derived := T.modules.mapDerivedCategory
    derivedFunctor := rfl
    derivedInverse := rfl }⟩

private def restrictionSquare
    {C E : Type u} [SmallCategory C] [SmallCategory E]
    {J : GrothendieckTopology C} {K : GrothendieckTopology E}
    {R : Sheaf J CommRingCat.{u}} {ring : Sheaf K CommRingCat.{u}}
    (F : E ⥤ Sheaf J (Type u)) (Z : E)
    (g : RingedToposMorphism (localCoefficientRings ring) (localCoefficientRings R))
    [g.inverse.IsEquivalence] [IsIso g.ringMap]
    (e : RingedToposMorphism (localCoefficientRings (ring.over Z))
      (localCoefficientRings (presentationElementRing R (F.obj Z))))
    [e.inverse.IsEquivalence] [IsIso e.ringMap]
    (q : g.inverse ⋙ K.overPullback (Type u) Z ≅
      elementSheafPullback (F.obj Z) ⋙ e.inverse)
    (hq : q.hom.app (ringSets (localCoefficientRings R)) ≫ e.ringMap =
      (K.overPullback (Type u) Z).map g.ringMap)
    (whole : BinaryPresentationModules g) (loc : BinaryPresentationModules e) :
    elementModulePullback (localCoefficientRings R) (F.obj Z) ⋙ loc.modules.functor ≅
      whole.modules.functor ⋙ SheafOfModules.overFunctor (localCoefficientRings ring) Z := by
  exact ((Functor.isoWhiskerLeft whole.modules.functor
    (restrictModulesIso (Over.forget Z) (localCoefficientRings ring))).symm ≪≫
    moduleSquare (Over.forget Z) (elementProjection (F.obj Z)) g e q hq
      whole.modules whole.pushforward loc.modules loc.pushforward ≪≫
    Functor.isoWhiskerRight
      (restrictModulesIso (elementProjection (F.obj Z)) (localCoefficientRings R))
      loc.modules.functor).symm

/-- The fibre nerve carries the restricted coefficient ring to the fixed localized ring.
Source: Stacks Sites 00Y1, 04GZ; Modules on Sites 03CR.
(blueprint: lem-sp-nerve-ringed-localization).

Proof: a morphism C → M uniquely lifts over F(Z) to F(Z) × M, with first
component the structural map of C. The slice nerve formula therefore identifies
N(M)|Z with the fibre-equivalence image of M|F(Z). This isomorphism is natural
in M. Conjugate the whole structural ring map by it. Its naturality for zero,
one, addition and multiplication proves the ring identities, and its
invertibility proves that the new structural map is invertible. The ring-data
module construction gives the induced direct image. The ringed module
Hom-equivalence gives the inverse equivalence, its underlying-set and rank-one
identifications. An additive equivalence is exact in both directions; its
termwise action descends to the stated derived equivalence. -/
theorem exists_binaryPresentationRingedSlice
    {C E : Type u} [SmallCategory C] [SmallCategory E]
    {J : GrothendieckTopology C} {K : GrothendieckTopology E}
    (R : Sheaf J CommRingCat.{u}) (ring : Sheaf K CommRingCat.{u})
    (F : E ⥤ Sheaf J (Type u)) (N : Sheaf J (Type u) ≌ Sheaf K (Type u))
    (hN : N.functor ⋙ sheafToPresheaf K (Type u) ≅ sheafSubcategoryNerve F)
    (g : RingedToposMorphism (localCoefficientRings ring) (localCoefficientRings R))
    (hi : g.inverse = N.functor) (hr : IsIso g.ringMap)
    (whole : BinaryPresentationModules g)
    (Z : E) (source : RingedSheafSliceAdjunctionData (localCoefficientRings R) (F.obj Z))
    (S : Over (F.obj Z) ≌ Sheaf (K.over Z) (Type u))
    (hS : S.functor ⋙ sheafToPresheaf (K.over Z) (Type u) ≅
      yoneda ⋙ (Functor.whiskeringLeft (Over Z)ᵒᵖ
        (Over (F.obj Z))ᵒᵖ (Type u)).obj (Over.post F).op) :
    ∃ e : RingedToposMorphism (localCoefficientRings (ring.over Z))
        (localCoefficientRings (presentationElementRing R (F.obj Z))),
      e.inverse = source.fibreEquivalence.functor ⋙ S.functor ∧
      IsIso e.ringMap ∧
      ∃ loc : BinaryPresentationModules e,
      Nonempty (elementModulePullback (localCoefficientRings R) (F.obj Z) ⋙
          loc.modules.functor ≅
          whole.modules.functor ⋙ SheafOfModules.overFunctor (localCoefficientRings ring) Z) := by
  classical
  let := hr
  let H := source.fibreEquivalence.trans S
  let q : g.inverse ⋙ K.overPullback (Type u) Z ≅
      elementSheafPullback (F.obj Z) ⋙ H.functor :=
    Functor.isoWhiskerRight (eqToIso hi) (K.overPullback (Type u) Z) ≪≫
      sliceSetComparison F N hN Z S hS (localCoefficientRings R) source
  let d := nerveSliceRingData g (F.obj Z) Z H q
  let e := d.withModules
    (Classical.choice (SheafOfModules.ringData_inducedModules _ _ d))
  have he : IsIso e.ringMap := by
    change IsIso (q.inv.app _ ≫ (K.overPullback (Type u) Z).map g.ringMap)
    infer_instance
  let := he
  have : e.inverse.IsEquivalence := inferInstanceAs H.functor.IsEquivalence
  have : g.inverse.IsEquivalence := hi ▸ inferInstance
  have hq : q.hom.app _ ≫ e.ringMap = (K.overPullback (Type u) Z).map g.ringMap := by
    change q.hom.app _ ≫ (q.inv.app _ ≫ _) = _
    rw [Iso.hom_inv_id_app_assoc]
  obtain ⟨loc⟩ := sliceModulesExist e
  exact ⟨e, rfl, he, loc, ⟨restrictionSquare F Z g e q hq whole loc⟩⟩

end CategoryTheory
