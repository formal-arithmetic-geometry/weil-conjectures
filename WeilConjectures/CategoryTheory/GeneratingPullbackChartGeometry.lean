/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
public import Mathlib.CategoryTheory.Sites.Over
import all WeilConjectures.CategoryTheory.ProperBaseChange.ElementSiteDescent
import all WeilConjectures.CategoryTheory.Ringed.RingedEquivalenceSlices
import WeilConjectures.CategoryTheory.Localized.LocalizedSheavesOverRepresentable
import WeilConjectures.ProperBaseChange.GeometricModuleConstruction
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over

/-! Object-slice geometric data for a ringed inverse image.

Source: Stacks Project, Sites, Tags 00WL and 04H1; Modules on Sites, Tags 04IF and 04J4.
(blueprint: lem-weil-pbc-object-slice-ringed-chart).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.MonoidalCategory
namespace CategoryTheory

/-- A geometric restriction square, with its structural ring map specified.
Source: Stacks Project, Modules on Sites, Tags 04IF and 04J4.
(blueprint: lem-weil-pbc-object-slice-ringed-chart). -/
structure ObjectSliceRingedChart
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (RY : Sheaf J CommRingCat.{u}) (RX : Sheaf K CommRingCat.{u})
    (f : RingedToposMorphism
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX)
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY))
    (U : D) (V : C)
    where
  morphism : RingedToposMorphism
    ((sheafCompose (K.over U) (forget₂ CommRingCat RingCat)).obj (RX.over U))
    ((sheafCompose (J.over V) (forget₂ CommRingCat RingCat)).obj (RY.over V))
  comparison : J.overPullback (Type u) V ⋙ morphism.inverse ≅
    f.inverse ⋙ K.overPullback (Type u) U
  structural : morphism.ringMap =
    comparison.hom.app
      ((sheafCompose J (forget RingCat)).obj
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY)) ≫
      (K.overPullback (Type u) U).map f.ringMap

private theorem element_cover_iff'
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (A : Sheaf J (Type u)) {X : A.obj.Elementsᵒᵖ} (S : Sieve X) :
    S ∈ elementTopology A X ↔
      S.functorPushforward (elementProjection A) ∈ J ((elementProjection A).obj X) := by
  constructor
  · exact (CoverPreserving.of_isContinuous (elementProjection A) _ _).cover_preserve
  · intro h
    rw [(element_site_descent A).1]
    exact (elementProjection A).mem_restrictedTopology_of_functorPushforward_mem h

private theorem elementMap_cocontinuous
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {A B : Sheaf J (Type u)} (b : B ⟶ A) :
    Functor.IsCocontinuous (elementMap b) (elementTopology B) (elementTopology A) where
  cover_lift {X S} hS := by
    apply (element_cover_iff' B _).mpr
    apply J.superset_covering ?_ ((element_cover_iff' A S).mp hS)
    intro W f hf
    refine ⟨liftElement B X f, liftElementHom B X f, 𝟙 W, ?_, ?_⟩
    · change S ((elementMap b).map (liftElementHom B X f))
      rw [← projection_pull_push A ((elementMap b).obj X) S]
      exact hf
    · simp [elementProjection, liftElementHom]
      rfl

private theorem exists_ordinarySliceEquiv
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) (U : C) :
    ∃ E : Sheaf (J.over U) (Type u) ≌
        Over ((presheafToSheaf J (Type u)).obj (yoneda.obj U)),
      Nonempty (productOver ((presheafToSheaf J (Type u)).obj (yoneda.obj U)) ⋙
        E.inverse ≅ J.overPullback (Type u) U) := by
  obtain ⟨_, _, _, _, _, E, _, r, hr, hn⟩ :=
    exists_localizedSheavesOverRepresentable_general J U
  refine ⟨E, ⟨?_⟩⟩
  apply Functor.fullyFaithfulCancelRight (sheafToPresheaf (J.over U) (Type u))
  let A := (presheafToSheaf J (Type u)).obj (yoneda.obj U)
  refine NatIso.ofComponents (fun X ↦ NatIso.ofComponents (fun W ↦
    (r ((productOver A).obj X) W.unop).toIso ≪≫ Equiv.toIso
      { toFun := fun x ↦ x.val.2
        invFun := fun x ↦ ⟨((toSheafify J (yoneda.obj U)).app
          (op W.unop.left) W.unop.hom, x), rfl⟩
        left_inv := fun x ↦ Subtype.ext (Prod.ext x.property.symm rfl)
        right_inv := fun x ↦ rfl }) ?_) ?_
  · intro W W' a
    apply ConcreteCategory.hom_ext
    intro x
    change (r ((productOver A).obj X) W'.unop
      ((E.inverse.obj ((productOver A).obj X)).obj.map a x)).val.2 = _
    exact congrArg (fun z ↦ z.2)
      (hr ((productOver A).obj X) W'.unop W.unop a.unop x)
  · intro X Y a
    ext W x
    change (r ((productOver A).obj Y) W.unop
      ((E.inverse.map ((productOver A).map a)).hom.app W x)).val.2 = _
    exact congrArg (fun z ↦ z.2)
      (hn ((productOver A).obj X) ((productOver A).obj Y) ((productOver A).map a) W.unop x)

private theorem over_pullback_isLeftAdjoint
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) {A B : Sheaf J (Type u)} (b : B ⟶ A) :
    (Over.pullback b).IsLeftAdjoint := by
  obtain ⟨s⟩ := ringed_sheaf_slice_adjunction R A
  obtain ⟨t⟩ := ringed_sheaf_slice_adjunction R B
  let hc := elementMap_continuous b
  let _ := hc
  let _ := elementMap_cocontinuous b
  let L := (elementMap b).sheafPushforwardContinuous (Type u)
    (elementTopology B) (elementTopology A)
  let _ : L.IsLeftAdjoint :=
    ((elementMap b).sheafAdjunctionCocontinuous (Type u)
      (elementTopology B) (elementTopology A)).isLeftAdjoint
  have q : (s.fibreEquivalence.inverse ⋙ L) ⋙ t.fibreEquivalence.functor ≅
      Over.pullback b :=
    Iso.compInverseIso (H := t.fibreEquivalence.symm) (fibreRestrictionIso b hc s t)
  exact Functor.isLeftAdjoint_of_iso q

private theorem exists_object_slice_inverse
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (RY : Sheaf J CommRingCat.{u}) (RX : Sheaf K CommRingCat.{u})
    (f : RingedToposMorphism
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX)
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY))
    (U : D) (V : C)
    (s : (f.inverse.obj
      ((presheafToSheaf J (Type u)).obj (yoneda.obj V))).obj.obj (op U)) :
    ∃ (L : Sheaf (J.over V) (Type u) ⥤ Sheaf (K.over U) (Type u))
      (P : Sheaf (K.over U) (Type u) ⥤ Sheaf (J.over V) (Type u)),
      Nonempty (L ⊣ P) ∧ PreservesFiniteLimits L ∧
      Nonempty (J.overPullback (Type u) V ⋙ L ≅
        f.inverse ⋙ K.overPullback (Type u) U) := by
  classical
  let _ : PreservesFiniteLimits f.inverse := f.leftExact
  let A := (presheafToSheaf J (Type u)).obj (yoneda.obj V)
  let B := (presheafToSheaf K (Type u)).obj (yoneda.obj U)
  let sigma : B ⟶ f.inverse.obj A :=
    ((sheafificationAdjunction K (Type u)).homEquiv _ _).symm (yonedaEquiv.symm s)
  obtain ⟨EY, ⟨pY⟩⟩ := exists_ordinarySliceEquiv J V
  obtain ⟨EX, ⟨pX⟩⟩ := exists_ordinarySliceEquiv K U
  let _ : (Over.post (X := A) f.inverse).IsLeftAdjoint :=
    (Over.postAdjunctionLeft f.adj).isLeftAdjoint
  let _ : (Over.pullback sigma).IsLeftAdjoint :=
    over_pullback_isLeftAdjoint
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX) sigma
  let _ : PreservesFiniteLimits (Over.post (X := A) f.inverse) := inferInstance
  let _ : PreservesFiniteLimits (Over.pullback sigma) := inferInstance
  let H := Over.post (X := A) f.inverse ⋙ Over.pullback sigma ⋙ EX.inverse
  let L := EY.functor ⋙ H
  let _ : PreservesFiniteLimits (Over.pullback sigma ⋙ EX.inverse) :=
    comp_preservesFiniteLimits _ _
  let _ : PreservesFiniteLimits H := comp_preservesFiniteLimits _ _
  let _ : PreservesFiniteLimits L := comp_preservesFiniteLimits _ _
  let cY : J.overPullback (Type u) V ⋙ EY.functor ≅ productOver A :=
    Iso.compInverseIso (H := EY.symm) pY.symm
  let q : J.overPullback (Type u) V ⋙ L ≅ f.inverse ⋙ K.overPullback (Type u) U :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight cY H ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (productPostIso f.inverse A)
        (Over.pullback sigma ⋙ EX.inverse) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft f.inverse ((Functor.associator _ _ _).symm) ≪≫
      Functor.isoWhiskerLeft f.inverse
        (Functor.isoWhiskerRight (productPullbackIso sigma) EX.inverse) ≪≫
      Functor.isoWhiskerLeft f.inverse pX
  exact ⟨L, L.rightAdjoint, ⟨Adjunction.ofIsLeftAdjoint L⟩, inferInstance, ⟨q⟩⟩

private def ordinarySliceRingData {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J CommRingCat.{u}} {S : Sheaf K CommRingCat.{u}}
    (e : RingedToposMorphism (localCoefficientRings R) (localCoefficientRings S))
    (U₀ : C) (V₀ : D)
    (L : Sheaf (K.over V₀) (Type u) ⥤ Sheaf (J.over U₀) (Type u))
    (P : Sheaf (J.over U₀) (Type u) ⥤ Sheaf (K.over V₀) (Type u))
    (adj : L ⊣ P) [PreservesFiniteLimits L]
    (q : e.inverse ⋙ J.overPullback (Type u) U₀ ≅
      K.overPullback (Type u) V₀ ⋙ L) :
    RingedToposMorphism.RingData
      (localCoefficientRings (R.over U₀))
      (localCoefficientRings (S.over V₀)) where
  inverse := L
  direct := P
  adj := adj
  leftExact := inferInstance
  ringMap := q.inv.app (ringSets (localCoefficientRings S)) ≫
    (J.overPullback (Type u) U₀).map e.ringMap
  ring_zero := by
    intro T z hz U t
    have he : e.inverse.map (ringZero (localCoefficientRings S)) ≫ e.ringMap =
        RingedToposMorphism.RingData.zero _ := by
      ext V x
      exact e.ring_zero _ _ (fun _ _ ↦ rfl) V x
    have hz' : z = CartesianMonoidalCategory.toUnit T ≫
        (K.overPullback (Type u) V₀).map (ringZero (localCoefficientRings S)) := by
      ext V x
      exact hz V x
    have hn := q.inv.naturality (ringZero (localCoefficientRings S))
    have hn' := congrArg (fun f ↦ f ≫
      (J.overPullback (Type u) U₀).map e.ringMap) hn
    change L.map ((K.overPullback (Type u) V₀).map
        (ringZero (localCoefficientRings S))) ≫ q.inv.app _ ≫ _ = _ at hn'
    change _ = q.inv.app _ ≫
      (J.overPullback (Type u) U₀).map (e.inverse.map _ ) ≫
        (J.overPullback (Type u) U₀).map e.ringMap at hn'
    rw [← Functor.map_comp, he] at hn'
    have hz'' := congrArg (fun f ↦ L.map f ≫
      (q.inv.app (ringSets (localCoefficientRings S)) ≫
        (J.overPullback (Type u) U₀).map e.ringMap)) hz'
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
        (K.overPullback (Type u) V₀).map (ringOne (localCoefficientRings S)) := by
      ext V x
      exact hz V x
    have hn := q.inv.naturality (ringOne (localCoefficientRings S))
    have hn' := congrArg (fun f ↦ f ≫
      (J.overPullback (Type u) U₀).map e.ringMap) hn
    change L.map ((K.overPullback (Type u) V₀).map
        (ringOne (localCoefficientRings S))) ≫ q.inv.app _ ≫ _ = _ at hn'
    change _ = q.inv.app _ ≫
      (J.overPullback (Type u) U₀).map (e.inverse.map _ ) ≫
        (J.overPullback (Type u) U₀).map e.ringMap at hn'
    rw [← Functor.map_comp, he] at hn'
    have hz'' := congrArg (fun f ↦ L.map f ≫
      (q.inv.app (ringSets (localCoefficientRings S)) ≫
        (J.overPullback (Type u) U₀).map e.ringMap)) hz'
    simp only [Functor.map_comp, Category.assoc] at hz''
    rw [hn'] at hz''
    exact (congrArg (fun f ↦ f.hom.app U t) hz'').trans (by rfl)
  ring_add := by
    intro T x y z hz U t
    change T ⟶ (K.overPullback (Type u) V₀).obj (ringSets (localCoefficientRings S)) at x y z
    have h := congrArg (J.overPullback (Type u) U₀).map (ringData_add e.ringData)
    simp only [Functor.map_comp] at h
    have h' := binary_conjugate q
      (CartesianMonoidalCategory.fst _ _) (CartesianMonoidalCategory.snd _ _)
      (ringAdd (localCoefficientRings S))
      ((J.overPullback (Type u) U₀).map e.ringMap)
      ((J.overPullback (Type u) U₀).map e.ringMap)
      ((J.overPullback (Type u) U₀).map e.ringMap)
      (ringAdd (localCoefficientRings (R.over U₀))) h
    have hz' := ringAdd_eq
      (localCoefficientRings (S.over V₀)) x y z hz
    have h'' : L.map z ≫ (q.inv.app (ringSets (localCoefficientRings S)) ≫
        (J.overPullback (Type u) U₀).map e.ringMap) =
        CartesianMonoidalCategory.lift
          (L.map x ≫ q.inv.app (ringSets (localCoefficientRings S)) ≫
            (J.overPullback (Type u) U₀).map e.ringMap)
          (L.map y ≫ q.inv.app (ringSets (localCoefficientRings S)) ≫
            (J.overPullback (Type u) U₀).map e.ringMap) ≫
          ringAdd (localCoefficientRings (R.over U₀)) := by
      rw [hz', Functor.map_comp, Category.assoc]
      change L.map (CartesianMonoidalCategory.lift x y) ≫
        ((K.overPullback (Type u) V₀ ⋙ L).map (ringAdd (localCoefficientRings S)) ≫
          q.inv.app (ringSets (localCoefficientRings S)) ≫ _) = _
      rw [h', CartesianMonoidalCategory.comp_lift_assoc]
      have hf : CartesianMonoidalCategory.lift x y ≫ (K.overPullback (Type u) V₀).map
          (CartesianMonoidalCategory.fst (ringSets (localCoefficientRings S))
            (ringSets (localCoefficientRings S))) = x := by ext V v; rfl
      have hs : CartesianMonoidalCategory.lift x y ≫ (K.overPullback (Type u) V₀).map
          (CartesianMonoidalCategory.snd (ringSets (localCoefficientRings S))
            (ringSets (localCoefficientRings S))) = y := by ext V v; rfl
      simp only [Functor.comp_map, ← Category.assoc, ← L.map_comp, hf, hs]
    exact congrArg (fun f ↦ f.hom.app U t) h''
  ring_mul := by
    intro T x y z hz U t
    change T ⟶ (K.overPullback (Type u) V₀).obj (ringSets (localCoefficientRings S)) at x y z
    have h := congrArg (J.overPullback (Type u) U₀).map (ringData_mul e.ringData)
    simp only [Functor.map_comp] at h
    have h' := binary_conjugate q
      (CartesianMonoidalCategory.fst _ _) (CartesianMonoidalCategory.snd _ _)
      (ringMul (localCoefficientRings S))
      ((J.overPullback (Type u) U₀).map e.ringMap)
      ((J.overPullback (Type u) U₀).map e.ringMap)
      ((J.overPullback (Type u) U₀).map e.ringMap)
      (ringMul (localCoefficientRings (R.over U₀))) h
    have hz' := ringMul_eq
      (localCoefficientRings (S.over V₀)) x y z hz
    have h'' : L.map z ≫ (q.inv.app (ringSets (localCoefficientRings S)) ≫
        (J.overPullback (Type u) U₀).map e.ringMap) =
        CartesianMonoidalCategory.lift
          (L.map x ≫ q.inv.app (ringSets (localCoefficientRings S)) ≫
            (J.overPullback (Type u) U₀).map e.ringMap)
          (L.map y ≫ q.inv.app (ringSets (localCoefficientRings S)) ≫
            (J.overPullback (Type u) U₀).map e.ringMap) ≫
          ringMul (localCoefficientRings (R.over U₀)) := by
      rw [hz', Functor.map_comp, Category.assoc]
      change L.map (CartesianMonoidalCategory.lift x y) ≫
        ((K.overPullback (Type u) V₀ ⋙ L).map (ringMul (localCoefficientRings S)) ≫
          q.inv.app (ringSets (localCoefficientRings S)) ≫ _) = _
      rw [h', CartesianMonoidalCategory.comp_lift_assoc]
      have hf : CartesianMonoidalCategory.lift x y ≫ (K.overPullback (Type u) V₀).map
          (CartesianMonoidalCategory.fst (ringSets (localCoefficientRings S))
            (ringSets (localCoefficientRings S))) = x := by ext V v; rfl
      have hs : CartesianMonoidalCategory.lift x y ≫ (K.overPullback (Type u) V₀).map
          (CartesianMonoidalCategory.snd (ringSets (localCoefficientRings S))
            (ringSets (localCoefficientRings S))) = y := by ext V v; rfl
      simp only [Functor.comp_map, ← Category.assoc, ← L.map_comp, hf, hs]
    exact congrArg (fun f ↦ f.hom.app U t) h''

/-- A section of an inverse-image representable defines the ringed object-slice square.
Source: Stacks Project, Sites, Tags 00WL, 04H1 and 0791;
Modules on Sites, Tags 04IF, 04IE and 04J4.
(blueprint: lem-weil-pbc-object-slice-ringed-chart).

Proof: Yoneda followed by the sheafification adjunction turns s into a map
sigma from the associated representable of U to f-inverse of the associated
representable of V. On sheaf slices take Over.post of f.inverse, then pullback
along sigma. Its right adjoint is the composite of the dependent-product
right adjoint to pullback along sigma and the right adjoint to Over.post.
Equivalences between object-slice sheaves and sheaves over the associated
representables transport this adjunction to the two given object-slice sites.
Each factor preserves finite limits. Products with the associated representable
compute object restriction; finite-product preservation and pullback of products
therefore give the displayed inverse-image comparison. At the ring object compose
that comparison with restriction of f.ringMap. Naturality at zero, one, addition
and multiplication shows it is a ring map. Construct the induced module direct
image from this geometric ring data. The displayed structural identity holds by
construction. The representable-slice equivalence uses sheafification, so neither
subcanonicity nor points nor a functor between the original sites is needed. -/
theorem exists_object_slice_ringed_chart
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (RY : Sheaf J CommRingCat.{u}) (RX : Sheaf K CommRingCat.{u})
    (f : RingedToposMorphism
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX)
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY))
    (U : D) (V : C)
    (s : (f.inverse.obj
      ((presheafToSheaf J (Type u)).obj (yoneda.obj V))).obj.obj (op U)) :
    Nonempty (ObjectSliceRingedChart RY RX f U V) := by
  obtain ⟨L, P, ⟨adj⟩, hlim, ⟨q⟩⟩ := exists_object_slice_inverse RY RX f U V s
  let _ := hlim
  let d := ordinarySliceRingData f U V L P adj q.symm
  obtain ⟨m⟩ := SheafOfModules.ringData_inducedModules (RX.over U) (RY.over V) d
  exact ⟨{
    morphism := d.withModules m
    comparison := q
    structural := rfl
  }⟩

end CategoryTheory
