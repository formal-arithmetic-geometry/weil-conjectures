/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.Ringed.RingedPresentationData
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import Mathlib.Algebra.Category.Ring.Limits
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.RingedToposRingData
import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod

/-! # Auxiliary ringed presentation comparisons -/

@[expose] public noncomputable section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.MonoidalCategory
namespace CategoryTheory
-- Cache the sheaf limit instances used repeatedly by the slice comparisons.
private instance (priority := 2000) sheafPullbacks
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) :
    HasPullbacks (Sheaf J (Type u)) := inferInstance

private instance (priority := 2000) sheafPullback
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {X Y Z : Sheaf J (Type u)} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasPullback f g := inferInstance

-- Products over a sheaf, and their images under the supplied fibre equivalences.
private def productOver {E : Type*} [Category E] [CartesianMonoidalCategory E]
    (A : E) : E ⥤ Over A where
  obj X := Over.mk (CartesianMonoidalCategory.fst A X)
  map f := Over.homMk (𝟙 A ⊗ₘ f) (by simp)
  map_id X := by apply Over.OverMorphism.ext; simp
  map_comp f g := by
    apply Over.OverMorphism.ext
    simp

private def productFibreIso {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} (A : Sheaf J (Type u))
    (s : RingedSheafSliceAdjunctionData R A) :
    productOver A ⋙ s.fibreEquivalence.inverse ≅ elementSheafPullback A := by
  apply Functor.fullyFaithfulCancelRight (sheafToPresheaf (elementTopology A) (Type u))
  refine Functor.isoWhiskerLeft (productOver A) s.fibre_iso ≪≫ ?_
  refine NatIso.ofComponents (fun X ↦ NatIso.ofComponents (fun U ↦ ?_) ?_) ?_
  · exact Equiv.toIso
      { toFun := fun x ↦ x.val.2
        invFun := fun x ↦ ⟨(U.unop.unop.2, x), rfl⟩
        left_inv := fun x ↦ Subtype.ext (Prod.ext x.property.symm rfl)
        right_inv := fun x ↦ rfl }
  · intro U V f
    ext x
    rfl
  · intro X Y f
    ext U x
    rfl
private def productPostIso {E E' : Type*} [Category E] [Category E']
    [CartesianMonoidalCategory E] [CartesianMonoidalCategory E']
    (F : E ⥤ E') [PreservesFiniteLimits F] (A : E) :
    productOver A ⋙ Over.post F ≅ F ⋙ productOver (F.obj A) := by
  refine NatIso.ofComponents (fun X ↦ Over.isoMk
    (CartesianMonoidalCategory.prodComparisonIso F A X) ?_) ?_
  · exact CartesianMonoidalCategory.prodComparison_fst F A X
  · intro X Y f
    apply Over.OverMorphism.ext
    change F.map (𝟙 A ⊗ₘ f) ≫
      (CartesianMonoidalCategory.prodComparisonIso F A Y).hom =
      (CartesianMonoidalCategory.prodComparisonIso F A X).hom ≫ (𝟙 (F.obj A) ⊗ₘ F.map f)
    simpa only [Functor.map_id, CartesianMonoidalCategory.prodComparisonIso_hom] using
      CartesianMonoidalCategory.prodComparison_natural F (𝟙 A) f
private def sliceEquivalence {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    (F : Sheaf K (Type u) ⥤ Sheaf J (Type u)) [F.IsEquivalence]
    (A : Sheaf K (Type u)) (s : RingedSheafSliceAdjunctionData S A)
    (t : RingedSheafSliceAdjunctionData R (F.obj A)) :
    Sheaf (elementTopology A) (Type u) ≌ Sheaf (elementTopology (F.obj A)) (Type u) :=
  s.fibreEquivalence.trans ((Over.post F).asEquivalence.trans t.fibreEquivalence.symm)

private def sliceComparison {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    (F : Sheaf K (Type u) ⥤ Sheaf J (Type u)) [F.IsEquivalence]
    (A : Sheaf K (Type u)) (s : RingedSheafSliceAdjunctionData S A)
    (t : RingedSheafSliceAdjunctionData R (F.obj A)) :
    F ⋙ elementSheafPullback (F.obj A) ≅
      elementSheafPullback A ⋙ (sliceEquivalence F A s t).functor := by
  let p := productFibreIso A s
  let q := productFibreIso (F.obj A) t
  let h : F ⋙ elementSheafPullback (F.obj A) ≅
      (productOver A ⋙ Over.post F) ⋙ t.fibreEquivalence.inverse :=
    Functor.isoWhiskerLeft F q.symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (productPostIso F A).symm t.fibreEquivalence.inverse
  let r : productOver A ≅ elementSheafPullback A ⋙ s.fibreEquivalence.functor :=
    (Functor.rightUnitor _).symm ≪≫
      Functor.isoWhiskerLeft _ s.fibreEquivalence.counitIso.symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight p s.fibreEquivalence.functor
  exact h ≪≫ Functor.isoWhiskerRight
    (Functor.isoWhiskerRight r (Over.post F)) t.fibreEquivalence.inverse
private theorem binary_conjugate
    {E E' : Type*} [Category E] [Category E'] [CartesianMonoidalCategory E']
    {F G : E ⥤ E'} (α : F ≅ G)
    {X₁ X₂ X₃ X₁₂ : E} (p₁ : X₁₂ ⟶ X₁) (p₂ : X₁₂ ⟶ X₂)
    (a : X₁₂ ⟶ X₃) {Y₁ Y₂ Y₃ : E'}
    (r₁ : F.obj X₁ ⟶ Y₁) (r₂ : F.obj X₂ ⟶ Y₂) (r₃ : F.obj X₃ ⟶ Y₃)
    (b : Y₁ ⊗ Y₂ ⟶ Y₃)
    (h : F.map a ≫ r₃ = CartesianMonoidalCategory.lift
      (F.map p₁ ≫ r₁) (F.map p₂ ≫ r₂) ≫ b) :
    G.map a ≫ α.inv.app X₃ ≫ r₃ = CartesianMonoidalCategory.lift
      (G.map p₁ ≫ α.inv.app X₁ ≫ r₁)
      (G.map p₂ ≫ α.inv.app X₂ ≫ r₂) ≫ b := by
  rw [α.inv.naturality_assoc, h, CartesianMonoidalCategory.comp_lift_assoc]
  rw [← α.inv.naturality_assoc, ← α.inv.naturality_assoc]

private abbrev ringSets {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) := (sheafCompose J (forget RingCat)).obj R

private abbrev ringSections {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u}) (U : Cᵒᵖ) :
    Ring ((ringSets R).obj.obj U) := inferInstanceAs (Ring (R.obj.obj U))
attribute [local instance] ringSections

private def ringBinary {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) (op : ∀ U : Cᵒᵖ, R.obj.obj U → R.obj.obj U → R.obj.obj U)
    (hn : ∀ {U V : Cᵒᵖ} (f : U ⟶ V) x y,
      R.obj.map f (op U x y) = op V (R.obj.map f x) (R.obj.map f y)) :
    ringSets R ⊗ ringSets R ⟶ ringSets R :=
  ⟨{ app := fun U ↦ TypeCat.ofHom (fun x ↦ op U x.1 x.2)
     naturality := by intro U V f; ext x; exact (hn f x.1 x.2).symm }⟩

private def ringAdd {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) : ringSets R ⊗ ringSets R ⟶ ringSets R :=
  ringBinary R (fun _ x y ↦ x + y) (fun f x y ↦ (R.obj.map f).hom.map_add x y)

private def ringMul {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) : ringSets R ⊗ ringSets R ⟶ ringSets R :=
  ringBinary R (fun _ x y ↦ x * y) (fun f x y ↦ (R.obj.map f).hom.map_mul x y)

private theorem ringAdd_eq {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) {T : Sheaf J (Type u)}
    (x y z : T ⟶ ringSets R) (h : ∀ U t,
      z.hom.app U t = @Add.add (R.obj.obj U) inferInstance (x.hom.app U t) (y.hom.app U t)) :
    z = CartesianMonoidalCategory.lift x y ≫ ringAdd R := by
  ext U t
  exact h U t

private theorem ringMul_eq {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) {T : Sheaf J (Type u)}
    (x y z : T ⟶ ringSets R) (h : ∀ U t,
      z.hom.app U t = @Mul.mul (R.obj.obj U) inferInstance (x.hom.app U t) (y.hom.app U t)) :
    z = CartesianMonoidalCategory.lift x y ≫ ringMul R := by
  ext U t
  exact h U t
private def ringZero {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) : 𝟙_ (Sheaf J (Type u)) ⟶ ringSets R :=
  RingedToposMorphism.RingData.zero _

private def ringOne {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) : 𝟙_ (Sheaf J (Type u)) ⟶ ringSets R :=
  RingedToposMorphism.RingData.one _

private theorem ringData_add {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    (e : RingedToposMorphism.RingData R S) :
    e.inverse.map (ringAdd S) ≫ e.ringMap = CartesianMonoidalCategory.lift
      (e.inverse.map (CartesianMonoidalCategory.fst _ _) ≫ e.ringMap)
      (e.inverse.map (CartesianMonoidalCategory.snd _ _) ≫ e.ringMap) ≫ ringAdd R := by
  ext U t
  exact e.ring_add _ _ _ _ (fun _ _ ↦ rfl) U t

private theorem ringData_mul {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    (e : RingedToposMorphism.RingData R S) :
    e.inverse.map (ringMul S) ≫ e.ringMap = CartesianMonoidalCategory.lift
      (e.inverse.map (CartesianMonoidalCategory.fst _ _) ≫ e.ringMap)
      (e.inverse.map (CartesianMonoidalCategory.snd _ _) ≫ e.ringMap) ≫ ringMul R := by
  ext U t
  exact e.ring_mul _ _ _ _ (fun _ _ ↦ rfl) U t

set_option backward.isDefEq.respectTransparency false in
-- Transport the ring operations through the product/fibre comparison.
private def sliceRingData {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J CommRingCat.{u}} {S : Sheaf K CommRingCat.{u}}
    (e : RingedToposMorphism (localCoefficientRings R) (localCoefficientRings S))
    (A : Sheaf K (Type u))
    (H : Sheaf (elementTopology A) (Type u) ≌
      Sheaf (elementTopology (e.inverse.obj A)) (Type u))
    (q : e.inverse ⋙ elementSheafPullback (e.inverse.obj A) ≅
      elementSheafPullback A ⋙ H.functor) :
    RingedToposMorphism.RingData
      (localCoefficientRings (presentationElementRing R (e.inverse.obj A)))
      (localCoefficientRings (presentationElementRing S A)) where
  inverse := H.functor
  direct := H.inverse
  adj := H.toAdjunction
  leftExact := inferInstance
  ringMap := q.inv.app (ringSets (localCoefficientRings S)) ≫
    (elementSheafPullback (e.inverse.obj A)).map e.ringMap
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
      (elementSheafPullback (e.inverse.obj A)).map e.ringMap) hn
    change H.functor.map ((elementSheafPullback A).map
        (ringZero (localCoefficientRings S))) ≫ q.inv.app _ ≫ _ = _ at hn'
    change _ = q.inv.app _ ≫
      (elementSheafPullback (e.inverse.obj A)).map (e.inverse.map _ ) ≫
        (elementSheafPullback (e.inverse.obj A)).map e.ringMap at hn'
    rw [← Functor.map_comp, he] at hn'
    have hz'' := congrArg (fun f ↦ H.functor.map f ≫
      (q.inv.app (ringSets (localCoefficientRings S)) ≫
        (elementSheafPullback (e.inverse.obj A)).map e.ringMap)) hz'
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
      (elementSheafPullback (e.inverse.obj A)).map e.ringMap) hn
    change H.functor.map ((elementSheafPullback A).map
        (ringOne (localCoefficientRings S))) ≫ q.inv.app _ ≫ _ = _ at hn'
    change _ = q.inv.app _ ≫
      (elementSheafPullback (e.inverse.obj A)).map (e.inverse.map _ ) ≫
        (elementSheafPullback (e.inverse.obj A)).map e.ringMap at hn'
    rw [← Functor.map_comp, he] at hn'
    have hz'' := congrArg (fun f ↦ H.functor.map f ≫
      (q.inv.app (ringSets (localCoefficientRings S)) ≫
        (elementSheafPullback (e.inverse.obj A)).map e.ringMap)) hz'
    simp only [Functor.map_comp, Category.assoc] at hz''
    rw [hn'] at hz''
    exact (congrArg (fun f ↦ f.hom.app U t) hz'').trans (by rfl)
  ring_add := by
    intro T x y z hz U t
    change T ⟶ (elementSheafPullback A).obj (ringSets (localCoefficientRings S)) at x y z
    have h := congrArg (elementSheafPullback (e.inverse.obj A)).map (ringData_add e.ringData)
    simp only [Functor.map_comp] at h
    have h' := binary_conjugate q
      (CartesianMonoidalCategory.fst _ _) (CartesianMonoidalCategory.snd _ _)
      (ringAdd (localCoefficientRings S))
      ((elementSheafPullback (e.inverse.obj A)).map e.ringMap)
      ((elementSheafPullback (e.inverse.obj A)).map e.ringMap)
      ((elementSheafPullback (e.inverse.obj A)).map e.ringMap)
      (ringAdd (localCoefficientRings (presentationElementRing R (e.inverse.obj A)))) h
    have hz' := ringAdd_eq
      (localCoefficientRings (presentationElementRing S A)) x y z hz
    have h'' : H.functor.map z ≫ (q.inv.app (ringSets (localCoefficientRings S)) ≫
        (elementSheafPullback (e.inverse.obj A)).map e.ringMap) =
        CartesianMonoidalCategory.lift
          (H.functor.map x ≫ q.inv.app (ringSets (localCoefficientRings S)) ≫
            (elementSheafPullback (e.inverse.obj A)).map e.ringMap)
          (H.functor.map y ≫ q.inv.app (ringSets (localCoefficientRings S)) ≫
            (elementSheafPullback (e.inverse.obj A)).map e.ringMap) ≫
          ringAdd (localCoefficientRings (presentationElementRing R (e.inverse.obj A))) := by
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
    have h := congrArg (elementSheafPullback (e.inverse.obj A)).map (ringData_mul e.ringData)
    simp only [Functor.map_comp] at h
    have h' := binary_conjugate q
      (CartesianMonoidalCategory.fst _ _) (CartesianMonoidalCategory.snd _ _)
      (ringMul (localCoefficientRings S))
      ((elementSheafPullback (e.inverse.obj A)).map e.ringMap)
      ((elementSheafPullback (e.inverse.obj A)).map e.ringMap)
      ((elementSheafPullback (e.inverse.obj A)).map e.ringMap)
      (ringMul (localCoefficientRings (presentationElementRing R (e.inverse.obj A)))) h
    have hz' := ringMul_eq
      (localCoefficientRings (presentationElementRing S A)) x y z hz
    have h'' : H.functor.map z ≫ (q.inv.app (ringSets (localCoefficientRings S)) ≫
        (elementSheafPullback (e.inverse.obj A)).map e.ringMap) =
        CartesianMonoidalCategory.lift
          (H.functor.map x ≫ q.inv.app (ringSets (localCoefficientRings S)) ≫
            (elementSheafPullback (e.inverse.obj A)).map e.ringMap)
          (H.functor.map y ≫ q.inv.app (ringSets (localCoefficientRings S)) ≫
            (elementSheafPullback (e.inverse.obj A)).map e.ringMap) ≫
          ringMul (localCoefficientRings (presentationElementRing R (e.inverse.obj A))) := by
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
private abbrev restrictSets {C C' : Type u} [SmallCategory C] [SmallCategory C']
    {J : GrothendieckTopology C} {J' : GrothendieckTopology C'}
    (F : C' ⥤ C) [Functor.IsContinuous F J' J] :=
  F.sheafPushforwardContinuous (Type u) J' J

-- Fibrewise pullbacks give the further-restriction comparison.
private def pullbackSections {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {X Y Z : Sheaf J (Type u)}
    (f : X ⟶ Z) (g : Y ⟶ Z) (U : Cᵒᵖ) :
    (pullback f g).obj.obj U ≃
      {p : X.obj.obj U × Y.obj.obj U // f.hom.app U p.1 = g.hom.app U p.2} :=
  PullbackCone.IsLimit.equivPullbackObj
    (isLimitPullbackConeMapOfIsLimit
      (sheafToPresheaf J (Type u) ⋙ (evaluation Cᵒᵖ (Type u)).obj U)
      (pullback.condition (f := f) (g := g)) (pullbackIsPullback f g))

private theorem pullbackSections_fst {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {X Y Z : Sheaf J (Type u)}
    (f : X ⟶ Z) (g : Y ⟶ Z) (U : Cᵒᵖ) (x : (pullback f g).obj.obj U) :
    (pullbackSections f g U x).val.1 = (pullback.fst f g).hom.app U x :=
  PullbackCone.IsLimit.equivPullbackObj_apply_fst _ _

private theorem pullbackSections_snd {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {X Y Z : Sheaf J (Type u)}
    (f : X ⟶ Z) (g : Y ⟶ Z) (U : Cᵒᵖ) (x : (pullback f g).obj.obj U) :
    (pullbackSections f g U x).val.2 = (pullback.snd f g).hom.app U x :=
  PullbackCone.IsLimit.equivPullbackObj_apply_snd _ _

private theorem pullbackSection_ext {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {X Y Z : Sheaf J (Type u)}
    (f : X ⟶ Z) (g : Y ⟶ Z) (U : Cᵒᵖ) {x y : (pullback f g).obj.obj U}
    (hf : (pullback.fst f g).hom.app U x = (pullback.fst f g).hom.app U y)
    (hg : (pullback.snd f g).hom.app U x = (pullback.snd f g).hom.app U y) : x = y := by
  apply (pullbackSections f g U).injective
  apply Subtype.ext
  exact Prod.ext ((pullbackSections_fst f g U x).trans
    (hf.trans (pullbackSections_fst f g U y).symm))
    ((pullbackSections_snd f g U x).trans (hg.trans (pullbackSections_snd f g U y).symm))

private def fibrePullbackEquiv {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {A B : Sheaf J (Type u)} (b : B ⟶ A)
    (X : Over A) (U : Cᵒᵖ) (s : B.obj.obj U) :
    {x : (pullback X.hom b).obj.obj U // (pullback.snd X.hom b).hom.app U x = s} ≃
      {x : X.left.obj.obj U // X.hom.hom.app U x = b.hom.app U s} where
  toFun x := ⟨(pullback.fst X.hom b).hom.app U x.val, by
    have h := congrArg (fun f ↦ f.hom.app U x.val) (pullback.condition (f := X.hom) (g := b))
    change X.hom.hom.app U ((pullback.fst X.hom b).hom.app U x.val) =
      b.hom.app U ((pullback.snd X.hom b).hom.app U x.val) at h
    exact h.trans (congrArg (b.hom.app U) x.property)⟩
  invFun x := ⟨(pullbackSections X.hom b U).symm ⟨(x.val, s), x.property⟩, by
    rw [← pullbackSections_snd]
    exact congrArg (fun p ↦ p.val.2) ((pullbackSections X.hom b U).apply_symm_apply _)⟩
  left_inv x := by
    apply Subtype.ext
    apply pullbackSection_ext X.hom b U
    · rw [← pullbackSections_fst]
      exact congrArg (fun p ↦ p.val.1) ((pullbackSections X.hom b U).apply_symm_apply _)
    · change (pullback.snd X.hom b).hom.app U
        ((pullbackSections X.hom b U).symm _) = _
      rw [← pullbackSections_snd]
      exact (congrArg (fun p ↦ p.val.2)
        ((pullbackSections X.hom b U).apply_symm_apply
          ⟨((pullback.fst X.hom b).hom.app U x.val, s), _⟩)).trans x.property.symm
  right_inv x := by
    apply Subtype.ext
    change (pullback.fst X.hom b).hom.app U ((pullbackSections X.hom b U).symm _) = _
    rw [← pullbackSections_fst]
    exact congrArg (fun p ↦ p.val.1) ((pullbackSections X.hom b U).apply_symm_apply _)


private def fibrePullbackIso {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {A B : Sheaf J (Type u)} (b : B ⟶ A)
    (_h : Functor.IsContinuous (elementMap b) (elementTopology B) (elementTopology A)) :
    Over.pullback b ⋙ elementFibrePresheafFunctor B ≅
      elementFibrePresheafFunctor A ⋙
        (Functor.whiskeringLeft _ _ (Type u)).obj (elementMap b).op := by
  refine NatIso.ofComponents (fun X ↦ NatIso.ofComponents
    (fun U ↦ (fibrePullbackEquiv b X U.unop.unop.1 U.unop.unop.2).toIso) ?_) ?_
  · intro U V f
    ext x
    apply Subtype.ext
    exact (NatTrans.naturality_apply (pullback.fst X.hom b).hom
      f.unop.unop.1 x.val)
  · intro X Y f
    ext U x
    apply Subtype.ext
    change (pullback.fst Y.hom b).hom.app U.unop.unop.1
      (((Over.pullback b).map f).left.hom.app U.unop.unop.1 x.val) = _
    exact congrArg (fun h : pullback X.hom b ⟶ Y.left ↦
      h.hom.app U.unop.unop.1 x.val) (pullback.lift_fst _ _ _)

private def fibreRestrictionIso {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    {A B : Sheaf J (Type u)} (b : B ⟶ A)
    (h : Functor.IsContinuous (elementMap b) (elementTopology B) (elementTopology A))
    (s : RingedSheafSliceAdjunctionData R A)
    (t : RingedSheafSliceAdjunctionData R B) :
    s.fibreEquivalence.inverse ⋙ restrictSets (elementMap b) ≅
      Over.pullback b ⋙ t.fibreEquivalence.inverse := by
  letI := h
  apply Functor.fullyFaithfulCancelRight (sheafToPresheaf (elementTopology B) (Type u))
  exact Functor.isoWhiskerRight s.fibre_iso
      ((Functor.whiskeringLeft _ _ (Type u)).obj (elementMap b).op) ≪≫
    (fibrePullbackIso b h).symm ≪≫
    Functor.isoWhiskerLeft (Over.pullback b) t.fibre_iso.symm

set_option backward.isDefEq.respectTransparency false in
private def postPullbackIso {E E' : Type*} [Category E] [Category E']
    [HasPullbacks E] [HasPullbacks E']
    (F : E ⥤ E') [PreservesFiniteLimits F] {A B : E} (b : B ⟶ A) :
    Over.post F ⋙ Over.pullback (F.map b) ≅ Over.pullback b ⋙ Over.post F := by
  refine NatIso.ofComponents (fun X ↦ Over.isoMk
    (PreservesPullback.iso F X.hom b).symm ?_) ?_
  · exact PreservesPullback.iso_inv_snd F X.hom b
  · intro X Y f
    apply Over.OverMorphism.ext
    change pullback.lift
        (pullback.fst (F.map X.hom) (F.map b) ≫ F.map f.left)
        (pullback.snd (F.map X.hom) (F.map b)) _ ≫
      (PreservesPullback.iso F Y.hom b).inv =
      (PreservesPullback.iso F X.hom b).inv ≫
        F.map (pullback.lift (pullback.fst X.hom b ≫ f.left) (pullback.snd X.hom b) _)
    apply (cancel_mono (PreservesPullback.iso F Y.hom b).hom).mp
    apply pullback.hom_ext
    · simp only [Category.assoc, PreservesPullback.iso_hom_fst]
      rw [PreservesPullback.iso_inv_fst, pullback.lift_fst,
        ← F.map_comp, pullback.lift_fst, F.map_comp,
        PreservesPullback.iso_inv_fst_assoc]
    · simp only [Category.assoc, PreservesPullback.iso_hom_snd]
      rw [PreservesPullback.iso_inv_snd, pullback.lift_snd, ← F.map_comp, pullback.lift_snd,
        PreservesPullback.iso_inv_snd]



private def sliceMorphism {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J CommRingCat.{u}} {S : Sheaf K CommRingCat.{u}}
    (e : RingedToposMorphism (localCoefficientRings R) (localCoefficientRings S))
    [e.inverse.IsEquivalence]
    (A : Sheaf K (Type u))
    (s : RingedSheafSliceAdjunctionData (localCoefficientRings S) A)
    (t : RingedSheafSliceAdjunctionData (localCoefficientRings R) (e.inverse.obj A)) :
    RingedToposMorphism
      (localCoefficientRings (presentationElementRing R (e.inverse.obj A)))
      (localCoefficientRings (presentationElementRing S A)) := by
  let H := sliceEquivalence e.inverse A s t
  let q := sliceComparison e.inverse A s t
  let d := sliceRingData e A H q
  exact d.withModules (Classical.choice (SheafOfModules.ringData_inducedModules _ _ d))

private instance sliceMorphism_equivalence
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J CommRingCat.{u}} {S : Sheaf K CommRingCat.{u}}
    (e : RingedToposMorphism (localCoefficientRings R) (localCoefficientRings S))
    [e.inverse.IsEquivalence]
    (A : Sheaf K (Type u))
    (s : RingedSheafSliceAdjunctionData (localCoefficientRings S) A)
    (t : RingedSheafSliceAdjunctionData (localCoefficientRings R) (e.inverse.obj A)) :
    (sliceMorphism e A s t).inverse.IsEquivalence := by
  change (sliceEquivalence e.inverse A s t).functor.IsEquivalence
  infer_instance

private theorem sliceMorphism_inverse
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J CommRingCat.{u}} {S : Sheaf K CommRingCat.{u}}
    (e : RingedToposMorphism (localCoefficientRings R) (localCoefficientRings S))
    [e.inverse.IsEquivalence]
    (A : Sheaf K (Type u))
    (s : RingedSheafSliceAdjunctionData (localCoefficientRings S) A)
    (t : RingedSheafSliceAdjunctionData (localCoefficientRings R) (e.inverse.obj A)) :
    (sliceMorphism e A s t).inverse = (sliceEquivalence e.inverse A s t).functor := rfl

private theorem sliceMorphism_ringMap
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J CommRingCat.{u}} {S : Sheaf K CommRingCat.{u}}
    (e : RingedToposMorphism (localCoefficientRings R) (localCoefficientRings S))
    [e.inverse.IsEquivalence]
    (A : Sheaf K (Type u))
    (s : RingedSheafSliceAdjunctionData (localCoefficientRings S) A)
    (t : RingedSheafSliceAdjunctionData (localCoefficientRings R) (e.inverse.obj A)) :
    (sliceMorphism e A s t).ringMap =
      (sliceComparison e.inverse A s t).inv.app (ringSets (localCoefficientRings S)) ≫
        (elementSheafPullback (e.inverse.obj A)).map e.ringMap := rfl

private theorem sliceMorphism_structural
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J CommRingCat.{u}} {S : Sheaf K CommRingCat.{u}}
    (e : RingedToposMorphism (localCoefficientRings R) (localCoefficientRings S))
    [e.inverse.IsEquivalence]
    (A : Sheaf K (Type u))
    (s : RingedSheafSliceAdjunctionData (localCoefficientRings S) A)
    (t : RingedSheafSliceAdjunctionData (localCoefficientRings R) (e.inverse.obj A)) :
    (sliceComparison e.inverse A s t).hom.app (ringSets (localCoefficientRings S)) ≫
      (sliceMorphism e A s t).ringMap =
      (elementSheafPullback (e.inverse.obj A)).map e.ringMap := by
  rw [sliceMorphism_ringMap, Iso.hom_inv_id_app_assoc]



private def fibreRestrictionForward {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    {A B : Sheaf J (Type u)} (b : B ⟶ A)
    (h : Functor.IsContinuous (elementMap b) (elementTopology B) (elementTopology A))
    (s : RingedSheafSliceAdjunctionData R A)
    (t : RingedSheafSliceAdjunctionData R B) :
    s.fibreEquivalence.functor ⋙ Over.pullback b ≅
      restrictSets (elementMap b) ⋙ t.fibreEquivalence.functor := by
  letI := h
  let q := fibreRestrictionIso b h s t
  calc
    s.fibreEquivalence.functor ⋙ Over.pullback b ≅
        (s.fibreEquivalence.functor ⋙ Over.pullback b) ⋙
          (t.fibreEquivalence.inverse ⋙ t.fibreEquivalence.functor) :=
      (Functor.rightUnitor _).symm ≪≫ Functor.isoWhiskerLeft _ t.fibreEquivalence.counitIso.symm
    _ ≅ ((s.fibreEquivalence.functor ⋙ Over.pullback b) ⋙
        t.fibreEquivalence.inverse) ⋙ t.fibreEquivalence.functor :=
      (Functor.associator _ _ _).symm
    _ ≅ ((s.fibreEquivalence.functor ⋙ s.fibreEquivalence.inverse) ⋙
        restrictSets (elementMap b)) ⋙ t.fibreEquivalence.functor :=
      Functor.isoWhiskerRight
        (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ q.symm ≪≫
          (Functor.associator _ _ _).symm) _
    _ ≅ restrictSets (elementMap b) ⋙ t.fibreEquivalence.functor :=
      Functor.isoWhiskerRight
        (Functor.isoWhiskerRight s.fibreEquivalence.unitIso.symm _ ≪≫
          Functor.leftUnitor _) _

private def sliceFurtherComparison
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    (F : Sheaf K (Type u) ⥤ Sheaf J (Type u)) [F.IsEquivalence]
    {A B : Sheaf K (Type u)} (b : B ⟶ A)
    (hb : Functor.IsContinuous (elementMap b) (elementTopology B) (elementTopology A))
    (hFb : Functor.IsContinuous (elementMap (F.map b))
      (elementTopology (F.obj B)) (elementTopology (F.obj A)))
    (sA : RingedSheafSliceAdjunctionData S A)
    (sB : RingedSheafSliceAdjunctionData S B)
    (tA : RingedSheafSliceAdjunctionData R (F.obj A))
    (tB : RingedSheafSliceAdjunctionData R (F.obj B)) :
    (sliceEquivalence F A sA tA).functor ⋙ restrictSets (elementMap (F.map b)) ≅
      restrictSets (elementMap b) ⋙ (sliceEquivalence F B sB tB).functor := by
  letI := hb
  letI := hFb
  let q := fibreRestrictionIso (F.map b) hFb tA tB
  let p := fibreRestrictionForward b hb sA sB
  calc
    (sliceEquivalence F A sA tA).functor ⋙ restrictSets (elementMap (F.map b)) ≅
        sA.fibreEquivalence.functor ⋙ Over.post F ⋙
          (tA.fibreEquivalence.inverse ⋙ restrictSets (elementMap (F.map b))) :=
      Functor.associator _ _ _
    _ ≅ sA.fibreEquivalence.functor ⋙ Over.post F ⋙
        (Over.pullback (F.map b) ⋙ tB.fibreEquivalence.inverse) :=
      Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _ q)
    _ ≅ (sA.fibreEquivalence.functor ⋙ (Over.post F ⋙
        Over.pullback (F.map b))) ⋙ tB.fibreEquivalence.inverse :=
      Functor.isoWhiskerLeft _ (Functor.associator _ _ _).symm ≪≫
        (Functor.associator _ _ _).symm
    _ ≅ ((sA.fibreEquivalence.functor ⋙ Over.pullback b) ⋙
        Over.post F) ⋙ tB.fibreEquivalence.inverse :=
      Functor.isoWhiskerRight
        (Functor.isoWhiskerLeft _ (postPullbackIso F b) ≪≫
          (Functor.associator _ _ _).symm) _
    _ ≅ (restrictSets (elementMap b) ⋙ sB.fibreEquivalence.functor ⋙
        Over.post F) ⋙ tB.fibreEquivalence.inverse :=
      Functor.isoWhiskerRight (Functor.isoWhiskerRight p _ ≪≫
        Functor.associator _ _ _) _
    _ ≅ restrictSets (elementMap b) ⋙ (sliceEquivalence F B sB tB).functor :=
      Functor.associator _ _ _

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

-- Compatibility of the product comparisons with further restriction.
private def productPullbackIso {E : Type*} [Category E] [CartesianMonoidalCategory E]
    [HasPullbacks E] {A B : E} (b : B ⟶ A) :
    productOver A ⋙ Over.pullback b ≅ productOver B := by
  refine NatIso.ofComponents (fun X ↦ ?_) ?_
  · change Over.mk (pullback.snd (CartesianMonoidalCategory.fst A X) b) ≅
      Over.mk (CartesianMonoidalCategory.fst B X)
    refine Over.isoMk ?_ ?_
    · refine ⟨CartesianMonoidalCategory.lift
          (pullback.snd (CartesianMonoidalCategory.fst A X) b)
          (pullback.fst (CartesianMonoidalCategory.fst A X) b ≫
            CartesianMonoidalCategory.snd A X),
        pullback.lift
          (CartesianMonoidalCategory.lift (CartesianMonoidalCategory.fst B X ≫ b)
            (CartesianMonoidalCategory.snd B X)) (CartesianMonoidalCategory.fst B X)
          (by simp), ?_, ?_⟩
      · apply pullback.hom_ext
        · apply CartesianMonoidalCategory.hom_ext
          · simpa only [Category.assoc, pullback.lift_fst,
              CartesianMonoidalCategory.lift_fst_assoc,
              CartesianMonoidalCategory.lift_fst, Category.id_comp] using
              (pullback.condition (f := CartesianMonoidalCategory.fst A X) (g := b)).symm
          · simp
        · simp
      · apply CartesianMonoidalCategory.hom_ext <;> simp
    · simp
  · intro X Y f
    apply Over.OverMorphism.ext
    change pullback.lift
        (pullback.fst (CartesianMonoidalCategory.fst A X) b ≫ (𝟙 A ⊗ₘ f))
        (pullback.snd (CartesianMonoidalCategory.fst A X) b) _ ≫
        CartesianMonoidalCategory.lift (pullback.snd (CartesianMonoidalCategory.fst A Y) b)
          (pullback.fst (CartesianMonoidalCategory.fst A Y) b ≫
            CartesianMonoidalCategory.snd A Y) =
      CartesianMonoidalCategory.lift (pullback.snd (CartesianMonoidalCategory.fst A X) b)
        (pullback.fst (CartesianMonoidalCategory.fst A X) b ≫
          CartesianMonoidalCategory.snd A X) ≫ (𝟙 B ⊗ₘ f)
    apply CartesianMonoidalCategory.hom_ext <;> simp

private theorem productFibreRestriction
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {A B : Sheaf J (Type u)} (b : B ⟶ A)
    (hb : Functor.IsContinuous (elementMap b) (elementTopology B) (elementTopology A))
    (s : RingedSheafSliceAdjunctionData R A)
    (t : RingedSheafSliceAdjunctionData R B) (X : Sheaf J (Type u)) :
    let := hb
    (restrictSets (elementMap b)).map ((productFibreIso A s).hom.app X) =
      (fibreRestrictionIso b hb s t).hom.app ((productOver A).obj X) ≫
        t.fibreEquivalence.inverse.map ((productPullbackIso b).hom.app X) ≫
          (productFibreIso B t).hom.app X := by
  let := hb
  apply (sheafToPresheaf (elementTopology B) (Type u)).map_injective
  change ((Functor.whiskeringLeft _ _ (Type u)).obj (elementMap b).op).map
      ((sheafToPresheaf (elementTopology A) (Type u)).map
        ((productFibreIso A s).hom.app X)) = _
  simp only [Functor.map_comp, productFibreIso, fibreRestrictionIso,
    Functor.fullyFaithfulCancelRight_hom_app, Functor.map_preimage,
    Iso.trans_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app,
    NatIso.ofComponents_hom_app, Iso.symm_hom, Category.assoc]
  erw [t.fibre_iso.hom.naturality_assoc]
  simp only [Iso.inv_hom_id_app_assoc]
  ext U x
  simp only [fibrePullbackIso, NatIso.ofComponents_inv_app,
    fibrePullbackEquiv, productPullbackIso,
    NatIso.ofComponents_hom_app]
  change _ = ((pullback.fst (CartesianMonoidalCategory.fst A X) b).hom.app
    U.unop.unop.1 ((pullbackSections _ _ _).symm _)).2
  rw [← pullbackSections_fst]
  let y := (s.fibre_iso.hom.app ((productOver A).obj X)).app
    ((elementMap b).op.obj U) x
  have hy : (CartesianMonoidalCategory.fst A X).hom.app U.unop.unop.1 y.val =
      b.hom.app U.unop.unop.1 U.unop.unop.2 := y.property
  have hh := (pullbackSections (CartesianMonoidalCategory.fst A X) b
    U.unop.unop.1).apply_symm_apply ⟨(y.val, U.unop.unop.2), hy⟩
  exact (congrArg (fun z ↦ z.val.1.2) hh).symm

private theorem forwardUnitFormula {E O : Type*} [Category E] [Category O]
    (e : E ≌ O) {X : O} {Y : E} (p : e.inverse.obj X ⟶ Y) :
    e.inverse.map (e.counitIso.inv.app X ≫ e.functor.map p) =
      p ≫ e.unitIso.hom.app Y := by
  rw [Functor.map_comp, ← e.unit_app_inverse]
  exact e.unit_naturality p

private theorem restrictionMateFormula
    {E E' O O' : Type*} [Category E] [Category E'] [Category O] [Category O']
    (a : E ≌ O) (b : E' ≌ O') (P : O ⥤ O') (R : E ⥤ E')
    (q : a.inverse ⋙ R ≅ P ⋙ b.inverse) (X : E) :
    b.inverse.map (b.counitIso.inv.app (P.obj (a.functor.obj X)) ≫
      b.functor.map (q.inv.app (a.functor.obj X)) ≫
      b.functor.map (R.map (a.unitIso.inv.app X))) =
      q.inv.app (a.functor.obj X) ≫ R.map (a.unitIso.inv.app X) ≫
        b.unitIso.hom.app (R.obj X) := by
  rw [← b.functor.map_comp]
  simpa only [Category.assoc, Functor.id_obj] using forwardUnitFormula b
    (q.inv.app (a.functor.obj X) ≫ R.map (a.unitIso.inv.app X))

private theorem productMateCoherence
    {E E' O O' : Type*} [Category E] [Category E'] [Category O] [Category O']
    (a : E ≌ O) (b : E' ≌ O') (P : O ⥤ O') (R : E ⥤ E')
    (q : a.inverse ⋙ R ≅ P ⋙ b.inverse)
    {X : O} {Y : O'} {L : E}
    (p : a.inverse.obj X ⟶ L) (p' : b.inverse.obj Y ⟶ R.obj L)
    (w : P.obj X ⟶ Y)
    (hw : R.map p = q.hom.app X ≫ b.inverse.map w ≫ p') :
    P.map (a.counitIso.inv.app X ≫ a.functor.map p) ≫
        (b.counitIso.inv.app (P.obj (a.functor.obj L)) ≫
          b.functor.map (q.inv.app (a.functor.obj L)) ≫
          b.functor.map (R.map (a.unitIso.inv.app L))) =
      w ≫ (b.counitIso.inv.app Y ≫ b.functor.map p') := by
  apply b.inverse.map_injective
  rw [Functor.map_comp, restrictionMateFormula]
  change (P ⋙ b.inverse).map _ ≫ _ = _
  erw [q.inv.naturality_assoc]
  dsimp only [Functor.comp_map, Functor.id_obj]
  rw [forwardUnitFormula]
  have hh : R.map (p ≫ a.unitIso.hom.app L) ≫ R.map (a.unitIso.inv.app L) =
      R.map p := by
    rw [← R.map_comp, Category.assoc, Iso.hom_inv_id_app]
    dsimp only [Functor.id_obj]
    rw [Category.comp_id]
  rw [← Category.assoc (R.map _) (R.map _) (b.unitIso.hom.app _), hh]
  rw [Functor.map_comp, forwardUnitFormula]
  rw [hw]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
private theorem productPostPullback
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : Sheaf K (Type u) ⥤ Sheaf J (Type u)) [F.IsEquivalence]
    {A B : Sheaf K (Type u)} (b : B ⟶ A) (X : Sheaf K (Type u)) :
    (postPullbackIso F b).hom.app ((productOver A).obj X) ≫
        (Over.post F).map ((productPullbackIso b).hom.app X) ≫
        (productPostIso F B).hom.app X =
      (Over.pullback (F.map b)).map ((productPostIso F A).hom.app X) ≫
        (productPullbackIso (F.map b)).hom.app (F.obj X) := by
  apply Over.OverMorphism.ext
  change (PreservesPullback.iso F (CartesianMonoidalCategory.fst A X) b).inv ≫
      F.map (CartesianMonoidalCategory.lift
        (pullback.snd (CartesianMonoidalCategory.fst A X) b)
        (pullback.fst (CartesianMonoidalCategory.fst A X) b ≫
          CartesianMonoidalCategory.snd A X)) ≫
        (CartesianMonoidalCategory.prodComparisonIso F B X).hom =
    pullback.lift
      (pullback.fst (F.map (CartesianMonoidalCategory.fst A X)) (F.map b) ≫
        (CartesianMonoidalCategory.prodComparisonIso F A X).hom)
      (pullback.snd (F.map (CartesianMonoidalCategory.fst A X)) (F.map b)) _ ≫
      CartesianMonoidalCategory.lift
        (pullback.snd (CartesianMonoidalCategory.fst (F.obj A) (F.obj X)) (F.map b))
        (pullback.fst (CartesianMonoidalCategory.fst (F.obj A) (F.obj X)) (F.map b) ≫
          CartesianMonoidalCategory.snd (F.obj A) (F.obj X))
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, CartesianMonoidalCategory.prodComparisonIso_hom,
      CartesianMonoidalCategory.prodComparison_fst,
      CartesianMonoidalCategory.lift_fst,
      pullback.lift_snd]
    erw [← F.map_comp, CartesianMonoidalCategory.lift_fst, PreservesPullback.iso_inv_snd]
  · simp only [Category.assoc, CartesianMonoidalCategory.prodComparisonIso_hom,
      CartesianMonoidalCategory.prodComparison_snd,
      CartesianMonoidalCategory.lift_snd,
      pullback.lift_fst_assoc]
    erw [← F.map_comp, CartesianMonoidalCategory.lift_snd, F.map_comp,
      PreservesPullback.iso_inv_fst_assoc]

private theorem sliceCoherenceAlgebra
    {O O' E E' : Type*} [Category O] [Category O'] [Category E] [Category E']
    (I : O ⥤ E) (I' : O' ⥤ E') (R : E ⥤ E') (P : O ⥤ O')
    (r : I ⋙ R ≅ P ⋙ I')
    {X Y Z : O} {X' Y' Z' : O'} {V : E}
    (p : I.obj X ≅ V) (p' : I'.obj X' ≅ R.obj V)
    (w : P.obj X ≅ X') (u : Y ≅ X) (u' : Y' ≅ X')
    (l : Y ⟶ Z) (l' : Y' ⟶ Z')
    (z : P.obj Y ⟶ Y') (z' : P.obj Z ⟶ Z')
    (hp : R.map p.hom = r.hom.app X ≫ I'.map w.hom ≫ p'.hom)
    (hz : P.map l ≫ z' = z ≫ l')
    (hu : z ≫ u'.hom = P.map u.hom ≫ w.hom) :
    R.map (p.inv ≫ I.map u.inv ≫ I.map l) ≫
        r.hom.app Z ≫ I'.map z' =
      p'.inv ≫ I'.map u'.inv ≫ I'.map l' := by
  have hp' : R.map p.inv ≫ r.hom.app X = p'.inv ≫ I'.map w.inv := by
    apply (cancel_epi (R.map p.hom)).mp
    simp only [← R.map_comp_assoc, p.hom_inv_id, R.map_id, Category.id_comp]
    rw [hp]
    simp only [Category.assoc, p'.hom_inv_id_assoc, ← I'.map_comp, w.hom_inv_id,
      I'.map_id]
    exact (Category.comp_id _).symm
  simp only [R.map_comp, Category.assoc]
  erw [r.hom.naturality_assoc]
  erw [r.hom.naturality_assoc]
  dsimp only [Functor.comp_map]
  simp only [← Category.assoc]
  rw [hp']
  simp only [Category.assoc]
  simp only [← I'.map_comp]
  have hu' : w.inv ≫ P.map u.inv ≫ z = u'.inv := by
    apply (cancel_mono u'.hom).mp
    simp only [Category.assoc, hu]
    rw [← P.map_comp_assoc, u.inv_hom_id, P.map_id, Category.id_comp,
      w.inv_hom_id, u'.inv_hom_id]
  rw [hz]
  rw [← Category.assoc w.inv (P.map u.inv) (z ≫ l'),
    ← Category.assoc (w.inv ≫ P.map u.inv) z l', Category.assoc w.inv (P.map u.inv) z, hu']

private theorem sliceComparison_hom
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    (F : Sheaf K (Type u) ⥤ Sheaf J (Type u)) [F.IsEquivalence]
    (A : Sheaf K (Type u)) (s : RingedSheafSliceAdjunctionData S A)
    (t : RingedSheafSliceAdjunctionData R (F.obj A)) (X : Sheaf K (Type u)) :
    (sliceComparison F A s t).hom.app X =
      (productFibreIso (F.obj A) t).inv.app (F.obj X) ≫
        t.fibreEquivalence.inverse.map ((productPostIso F A).inv.app X) ≫
        t.fibreEquivalence.inverse.map ((Over.post F).map
          (s.fibreEquivalence.counitIso.inv.app ((productOver A).obj X) ≫
            s.fibreEquivalence.functor.map ((productFibreIso A s).hom.app X))) := by
  simp only [sliceComparison, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app,
    Functor.associator_inv_app, Functor.rightUnitor_inv_app, Category.id_comp,
    Functor.map_comp, Category.assoc]

private theorem fibreRestrictionForward_hom
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {A B : Sheaf J (Type u)} (b : B ⟶ A)
    (hb : Functor.IsContinuous (elementMap b) (elementTopology B) (elementTopology A))
    (s : RingedSheafSliceAdjunctionData R A)
    (t : RingedSheafSliceAdjunctionData R B) (L : Sheaf (elementTopology A) (Type u)) :
    let := hb
    (fibreRestrictionForward b hb s t).hom.app L =
      t.fibreEquivalence.counitIso.inv.app
        ((Over.pullback b).obj (s.fibreEquivalence.functor.obj L)) ≫
        t.fibreEquivalence.functor.map
          ((fibreRestrictionIso b hb s t).inv.app (s.fibreEquivalence.functor.obj L)) ≫
        t.fibreEquivalence.functor.map
          ((restrictSets (elementMap b)).map (s.fibreEquivalence.unitIso.inv.app L)) := by
  let := hb
  dsimp only [fibreRestrictionForward, Trans.trans]
  simp only [Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app,
    Functor.associator_inv_app, Functor.associator_hom_app,
    Functor.rightUnitor_inv_app, Functor.leftUnitor_hom_app, Category.id_comp,
    Category.comp_id, Functor.map_comp, Category.assoc]
  dsimp only [Functor.comp_obj, Functor.id_obj]
  erw [t.fibreEquivalence.functor.map_id]
  simp only [Category.comp_id]

private theorem sliceFurtherComparison_hom
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    (F : Sheaf K (Type u) ⥤ Sheaf J (Type u)) [F.IsEquivalence]
    {A B : Sheaf K (Type u)} (b : B ⟶ A)
    (hb : Functor.IsContinuous (elementMap b) (elementTopology B) (elementTopology A))
    (hFb : Functor.IsContinuous (elementMap (F.map b))
      (elementTopology (F.obj B)) (elementTopology (F.obj A)))
    (sA : RingedSheafSliceAdjunctionData S A)
    (sB : RingedSheafSliceAdjunctionData S B)
    (tA : RingedSheafSliceAdjunctionData R (F.obj A))
    (tB : RingedSheafSliceAdjunctionData R (F.obj B))
    (L : Sheaf (elementTopology A) (Type u)) :
    let := hb
    let := hFb
    (sliceFurtherComparison F b hb hFb sA sB tA tB).hom.app L =
      (fibreRestrictionIso (F.map b) hFb tA tB).hom.app
        ((Over.post F).obj (sA.fibreEquivalence.functor.obj L)) ≫
      tB.fibreEquivalence.inverse.map
        ((postPullbackIso F b).hom.app (sA.fibreEquivalence.functor.obj L) ≫
          (Over.post F).map ((fibreRestrictionForward b hb sA sB).hom.app L)) := by
  let := hb
  let := hFb
  dsimp only [sliceFurtherComparison, Trans.trans]
  simp only [Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app,
    Functor.associator_inv_app, Functor.associator_hom_app,
    Functor.map_comp, Category.id_comp, Category.comp_id,
    Category.assoc]
  dsimp only [Functor.comp_obj, Functor.id_obj]
  simp only [Category.id_comp]
  change 𝟙 _ ≫ _ = _
  exact Category.id_comp _

private theorem sliceFurtherComparison_constant
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    (F : Sheaf K (Type u) ⥤ Sheaf J (Type u)) [F.IsEquivalence]
    {A B : Sheaf K (Type u)} (b : B ⟶ A)
    (hb : Functor.IsContinuous (elementMap b) (elementTopology B) (elementTopology A))
    (hFb : Functor.IsContinuous (elementMap (F.map b))
      (elementTopology (F.obj B)) (elementTopology (F.obj A)))
    (sA : RingedSheafSliceAdjunctionData S A)
    (sB : RingedSheafSliceAdjunctionData S B)
    (tA : RingedSheafSliceAdjunctionData R (F.obj A))
    (tB : RingedSheafSliceAdjunctionData R (F.obj B))
    (X : Sheaf K (Type u)) :
    let := hb
    let := hFb
    (restrictSets (elementMap (F.map b))).map ((sliceComparison F A sA tA).hom.app X) ≫
      (sliceFurtherComparison F b hb hFb sA sB tA tB).hom.app
        ((elementSheafPullback A).obj X) =
      (sliceComparison F B sB tB).hom.app X := by
  let := hb
  let := hFb
  let lA := sA.fibreEquivalence.counitIso.inv.app ((productOver A).obj X) ≫
    sA.fibreEquivalence.functor.map ((productFibreIso A sA).hom.app X)
  let lB := sB.fibreEquivalence.counitIso.inv.app ((productOver B).obj X) ≫
    sB.fibreEquivalence.functor.map ((productFibreIso B sB).hom.app X)
  have hm : (Over.pullback b).map lA ≫
      (fibreRestrictionForward b hb sA sB).hom.app ((elementSheafPullback A).obj X) =
        (productPullbackIso b).hom.app X ≫ lB := by
    rw [fibreRestrictionForward_hom]
    exact productMateCoherence sA.fibreEquivalence sB.fibreEquivalence
      (Over.pullback b) (restrictSets (elementMap b)) (fibreRestrictionIso b hb sA sB)
      ((productFibreIso A sA).hom.app X) ((productFibreIso B sB).hom.app X)
      ((productPullbackIso b).hom.app X) (productFibreRestriction b hb sA sB X)
  have hz :
      (Over.pullback (F.map b)).map ((Over.post F).map lA) ≫
        ((postPullbackIso F b).hom.app
          (sA.fibreEquivalence.functor.obj ((elementSheafPullback A).obj X)) ≫
          (Over.post F).map ((fibreRestrictionForward b hb sA sB).hom.app
            ((elementSheafPullback A).obj X))) =
      (postPullbackIso F b).hom.app ((productOver A).obj X) ≫
        (Over.post F).map ((productPullbackIso b).hom.app X) ≫
          (Over.post F).map lB := by
    change (Over.post F ⋙ Over.pullback (F.map b)).map lA ≫ _ = _
    rw [(postPullbackIso F b).hom.naturality_assoc]
    dsimp only [Functor.comp_map]
    rw [← Functor.map_comp, hm, Functor.map_comp]
    rfl
  have hh := sliceCoherenceAlgebra tA.fibreEquivalence.inverse tB.fibreEquivalence.inverse
    (restrictSets (elementMap (F.map b))) (Over.pullback (F.map b))
    (fibreRestrictionIso (F.map b) hFb tA tB)
    ((productFibreIso (F.obj A) tA).app (F.obj X))
    ((productFibreIso (F.obj B) tB).app (F.obj X))
    ((productPullbackIso (F.map b)).app (F.obj X))
    ((productPostIso F A).app X) ((productPostIso F B).app X)
    ((Over.post F).map lA) ((Over.post F).map lB)
    ((postPullbackIso F b).hom.app ((productOver A).obj X) ≫
      (Over.post F).map ((productPullbackIso b).hom.app X))
    ((postPullbackIso F b).hom.app
      (sA.fibreEquivalence.functor.obj ((elementSheafPullback A).obj X)) ≫
      (Over.post F).map ((fibreRestrictionForward b hb sA sB).hom.app
        ((elementSheafPullback A).obj X)))
    (productFibreRestriction (F.map b) hFb tA tB (F.obj X))
    (by simpa only [Category.assoc] using hz)
    (productPostPullback F b X)
  rw [sliceComparison_hom, sliceFurtherComparison_hom, sliceComparison_hom]
  ext U x
  exact congrArg (fun f ↦ f.hom.app U x) hh
attribute [irreducible] sliceComparison sliceFurtherComparison

private def sliceMorphismComparison
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J CommRingCat.{u}} {S : Sheaf K CommRingCat.{u}}
    (e : RingedToposMorphism (localCoefficientRings R) (localCoefficientRings S))
    [e.inverse.IsEquivalence] (A : Sheaf K (Type u))
    (s : RingedSheafSliceAdjunctionData (localCoefficientRings S) A)
    (t : RingedSheafSliceAdjunctionData (localCoefficientRings R) (e.inverse.obj A)) :
    e.inverse ⋙ elementSheafPullback (e.inverse.obj A) ≅
      elementSheafPullback A ⋙ (sliceMorphism e A s t).inverse :=
  sliceComparison e.inverse A s t

private theorem sliceMorphismComparison_structural
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J CommRingCat.{u}} {S : Sheaf K CommRingCat.{u}}
    (e : RingedToposMorphism (localCoefficientRings R) (localCoefficientRings S))
    [e.inverse.IsEquivalence] (A : Sheaf K (Type u))
    (s : RingedSheafSliceAdjunctionData (localCoefficientRings S) A)
    (t : RingedSheafSliceAdjunctionData (localCoefficientRings R) (e.inverse.obj A)) :
    (sliceMorphismComparison e A s t).hom.app (ringSets (localCoefficientRings S)) ≫
      (sliceMorphism e A s t).ringMap =
        (elementSheafPullback (e.inverse.obj A)).map e.ringMap :=
  sliceMorphism_structural e A s t

private theorem sliceMorphism_ringIso
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J CommRingCat.{u}} {S : Sheaf K CommRingCat.{u}}
    (e : RingedToposMorphism (localCoefficientRings R) (localCoefficientRings S))
    [e.inverse.IsEquivalence] [IsIso e.ringMap] (A : Sheaf K (Type u))
    (s : RingedSheafSliceAdjunctionData (localCoefficientRings S) A)
    (t : RingedSheafSliceAdjunctionData (localCoefficientRings R) (e.inverse.obj A)) :
    IsIso (sliceMorphism e A s t).ringMap := by
  rw [sliceMorphism_ringMap]
  exact IsIso.comp_isIso' ((sliceComparison e.inverse A s t).app _).isIso_inv
    (Functor.map_isIso (elementSheafPullback (e.inverse.obj A)) e.ringMap)

private def sliceMorphismFurtherComparison
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J CommRingCat.{u}} {S : Sheaf K CommRingCat.{u}}
    (e : RingedToposMorphism (localCoefficientRings R) (localCoefficientRings S))
    [e.inverse.IsEquivalence] {A B : Sheaf K (Type u)} (b : B ⟶ A)
    (hb : Functor.IsContinuous (elementMap b) (elementTopology B) (elementTopology A))
    (hFb : Functor.IsContinuous (elementMap (e.inverse.map b))
      (elementTopology (e.inverse.obj B)) (elementTopology (e.inverse.obj A)))
    (sA : RingedSheafSliceAdjunctionData (localCoefficientRings S) A)
    (sB : RingedSheafSliceAdjunctionData (localCoefficientRings S) B)
    (tA : RingedSheafSliceAdjunctionData (localCoefficientRings R) (e.inverse.obj A))
    (tB : RingedSheafSliceAdjunctionData (localCoefficientRings R) (e.inverse.obj B)) :
    let := hb
    let := hFb
    (sliceMorphism e A sA tA).inverse ⋙ restrictSets (elementMap (e.inverse.map b)) ≅
      restrictSets (elementMap b) ⋙ (sliceMorphism e B sB tB).inverse :=
  sliceFurtherComparison e.inverse b hb hFb sA sB tA tB

private theorem sliceMorphismFurther_structural
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J CommRingCat.{u}} {S : Sheaf K CommRingCat.{u}}
    (e : RingedToposMorphism (localCoefficientRings R) (localCoefficientRings S))
    [e.inverse.IsEquivalence] {A B : Sheaf K (Type u)} (b : B ⟶ A)
    (hb : Functor.IsContinuous (elementMap b) (elementTopology B) (elementTopology A))
    (hFb : Functor.IsContinuous (elementMap (e.inverse.map b))
      (elementTopology (e.inverse.obj B)) (elementTopology (e.inverse.obj A)))
    (sA : RingedSheafSliceAdjunctionData (localCoefficientRings S) A)
    (sB : RingedSheafSliceAdjunctionData (localCoefficientRings S) B)
    (tA : RingedSheafSliceAdjunctionData (localCoefficientRings R) (e.inverse.obj A))
    (tB : RingedSheafSliceAdjunctionData (localCoefficientRings R) (e.inverse.obj B)) :
    let := hb
    let := hFb
    (sliceMorphismFurtherComparison e b hb hFb sA sB tA tB).hom.app
        (ringSets (localCoefficientRings (presentationElementRing S A))) ≫
      (sliceMorphism e B sB tB).ringMap =
        (restrictSets (elementMap (e.inverse.map b))).map (sliceMorphism e A sA tA).ringMap := by
  let := hb
  let := hFb
  apply (cancel_epi ((restrictSets (elementMap (e.inverse.map b))).map
    ((sliceComparison e.inverse A sA tA).hom.app
      (ringSets (localCoefficientRings S))))).mp
  have hc := sliceFurtherComparison_constant e.inverse b hb hFb sA sB tA tB
    (ringSets (localCoefficientRings S))
  calc
    _ = (sliceComparison e.inverse B sB tB).hom.app
        (ringSets (localCoefficientRings S)) ≫ (sliceMorphism e B sB tB).ringMap := by
      ext U x
      exact congrArg (fun f ↦ (f ≫ (sliceMorphism e B sB tB).ringMap).hom.app U x) hc
    _ = _ := sliceMorphism_structural e B sB tB
    _ = _ := by
      rw [← Functor.map_comp]
      exact congrArg (restrictSets (elementMap (e.inverse.map b))).map
        (sliceMorphism_structural e A sA tA).symm

attribute [irreducible] sliceMorphism sliceMorphismComparison sliceMorphismFurtherComparison

-- Recover module inverse images from their specified adjunctions and linearity.
private abbrev moduleSet {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) :=
  SheafOfModules.toSheaf.{u} R ⋙ sheafCompose J (forget AddCommGrpCat.{u})

private def moduleAdd {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} (M : ringedSiteModules.{u} R) :
    (moduleSet R).obj M ⊗ (moduleSet R).obj M ⟶ (moduleSet R).obj M :=
  ⟨{ app := fun U ↦ TypeCat.ofHom (fun x ↦ @Add.add (M.val.obj U) inferInstance x.1 x.2)
     naturality := by intro U V f; ext x; exact (M.val.map f).hom.map_add _ _ |>.symm }⟩

private def moduleSMul {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} (M : ringedSiteModules.{u} R) :
    ringSets R ⊗ (moduleSet R).obj M ⟶ (moduleSet R).obj M :=
  ⟨{ app := fun U ↦ TypeCat.ofHom (fun x ↦
         @SMul.smul (R.obj.obj U) (M.val.obj U) inferInstance x.1 x.2)
     naturality := by intro U V f; ext x; exact (M.val.map_smul f _ _).symm }⟩

private def inverseModulesIso {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    (e : RingedToposMorphism R S) [e.inverse.IsEquivalence]
    (W : ringedSiteModules.{u} S ≌ ringedSiteModules.{u} R)
    (p : W.inverse ≅ e.modules) :
    moduleSet S ⋙ e.inverse ≅ W.functor ⋙ moduleSet R := by
  let a : W.functor ⊣ e.modules := W.toAdjunction.ofNatIsoRight p
  let v : moduleSet S ≅ W.functor ⋙ (moduleSet R ⋙ e.direct) :=
    Functor.isoWhiskerRight (asIso a.unit) (moduleSet S) ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft W.functor e.underlying
  exact Functor.isoWhiskerRight v e.inverse ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft W.functor (Functor.associator _ _ _) ≪≫
    Functor.isoWhiskerLeft (W.functor ⋙ moduleSet R) (asIso e.adj.counit) ≪≫
    Functor.rightUnitor _

attribute [irreducible] inverseModulesIso

private theorem inverseModulesIso_formula
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    (e : RingedToposMorphism R S) [e.inverse.IsEquivalence]
    (W : ringedSiteModules.{u} S ≌ ringedSiteModules.{u} R)
    (p : W.inverse ≅ e.modules) (M : ringedSiteModules.{u} S)
    {T : Sheaf K (Type u)} (x : T ⟶ (moduleSet S).obj M) :
    e.inverse.map x ≫ (inverseModulesIso e W p).hom.app M =
      (e.adj.homEquiv _ _).symm
        (x ≫ (moduleSet S).map ((W.toAdjunction.ofNatIsoRight p).unit.app M) ≫
          e.underlying.hom.app (W.functor.obj M)) := by
  simp only [Adjunction.homEquiv_symm_apply, inverseModulesIso, Iso.trans_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    NatTrans.comp_app, Functor.associator_hom_app, Functor.rightUnitor_hom_app,
    asIso_hom, Functor.map_comp, Functor.comp_obj, Functor.comp_map,
    Category.id_comp, Category.assoc]
  ext U t
  rfl

private theorem inverseModulesIso_linear
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    (e : RingedToposMorphism R S) [e.inverse.IsEquivalence]
    (W : ringedSiteModules.{u} S ≌ ringedSiteModules.{u} R)
    (p : W.inverse ≅ e.modules) (M : ringedSiteModules.{u} S)
    (T : Sheaf K (Type u)) (a : T ⟶ ringSets S)
    (x y z : T ⟶ (moduleSet S).obj M)
    (hz : ∀ U t, z.hom.app U t =
      @Add.add (M.val.obj U) inferInstance
        (@SMul.smul (S.obj.obj U) (M.val.obj U) inferInstance
          (a.hom.app U t) (x.hom.app U t)) (y.hom.app U t)) :
    ∀ U t, (e.inverse.map z ≫ (inverseModulesIso e W p).hom.app M).hom.app U t =
      @Add.add ((W.functor.obj M).val.obj U) inferInstance
        (@SMul.smul (R.obj.obj U) ((W.functor.obj M).val.obj U) inferInstance
          ((e.inverse.map a ≫ e.ringMap).hom.app U t)
          ((e.inverse.map x ≫ (inverseModulesIso e W p).hom.app M).hom.app U t))
        ((e.inverse.map y ≫ (inverseModulesIso e W p).hom.app M).hom.app U t) := by
  let f := (W.toAdjunction.ofNatIsoRight p).unit.app M
  intro U t
  rw [inverseModulesIso_formula, inverseModulesIso_formula, inverseModulesIso_formula]
  apply e.module_linear (W.functor.obj M) T a
    (x ≫ (moduleSet S).map f) (y ≫ (moduleSet S).map f)
    (z ≫ (moduleSet S).map f)
  intro V v
  change f.val.app V (z.hom.app V v) = _
  rw [hz]
  change f.val.app V ((_ : S.obj.obj V) • (_ : M.val.obj V) +
    (_ : M.val.obj V)) = _
  exact (f.val.app V).hom.map_add _ _ |>.trans
    (congrArg (fun z ↦ z + f.val.app V (y.hom.app V v))
      ((f.val.app V).hom.map_smul _ _))
private theorem inverseModulesIso_add
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    (e : RingedToposMorphism R S) [e.inverse.IsEquivalence]
    (W : ringedSiteModules.{u} S ≌ ringedSiteModules.{u} R)
    (p : W.inverse ≅ e.modules) (M : ringedSiteModules.{u} S) :
    e.inverse.map (moduleAdd M) ≫ (inverseModulesIso e W p).hom.app M =
      CartesianMonoidalCategory.lift
        (e.inverse.map (CartesianMonoidalCategory.fst _ _) ≫
          (inverseModulesIso e W p).hom.app M)
        (e.inverse.map (CartesianMonoidalCategory.snd _ _) ≫
          (inverseModulesIso e W p).hom.app M) ≫ moduleAdd (W.functor.obj M) := by
  ext U t
  have h := inverseModulesIso_linear e W p M _
    (RingedToposMorphism.RingData.one _)
    (CartesianMonoidalCategory.fst _ _) (CartesianMonoidalCategory.snd _ _)
    (moduleAdd M) (fun V x ↦ by
      change @Add.add (M.val.obj V) inferInstance x.1 x.2 =
        @Add.add (M.val.obj V) inferInstance
          (@SMul.smul (S.obj.obj V) (M.val.obj V) inferInstance 1 x.1) x.2
      exact congrArg (fun z : M.val.obj V ↦ z + (show M.val.obj V from x.2))
        (@one_smul (S.obj.obj V) (M.val.obj V) _ _ x.1).symm) U t
  rw [e.ring_one _ _ (fun _ _ ↦ rfl)] at h
  change _ = (1 : R.obj.obj U) • (_ : (W.functor.obj M).val.obj U) +
    (_ : (W.functor.obj M).val.obj U) at h
  rw [one_smul] at h
  exact h

private def moduleZero {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} (M : ringedSiteModules.{u} R) (T : Sheaf J (Type u)) :
    T ⟶ (moduleSet R).obj M :=
  ⟨{ app := fun U ↦ TypeCat.ofHom (fun _ ↦ (0 : M.val.obj U))
     naturality := by intro U V f; ext x; exact (map_zero (M.val.map f).hom).symm }⟩

private theorem inverseModulesIso_smul
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    (e : RingedToposMorphism R S) [e.inverse.IsEquivalence]
    (W : ringedSiteModules.{u} S ≌ ringedSiteModules.{u} R)
    (p : W.inverse ≅ e.modules) (M : ringedSiteModules.{u} S) :
    e.inverse.map (moduleSMul M) ≫ (inverseModulesIso e W p).hom.app M =
      CartesianMonoidalCategory.lift
        (e.inverse.map (CartesianMonoidalCategory.fst _ _) ≫ e.ringMap)
        (e.inverse.map (CartesianMonoidalCategory.snd _ _) ≫
          (inverseModulesIso e W p).hom.app M) ≫ moduleSMul (W.functor.obj M) := by
  have hz (T : Sheaf K (Type u)) (U : Cᵒᵖ) (t : (e.inverse.obj T).obj.obj U) :
      (e.inverse.map (moduleZero M T) ≫ (inverseModulesIso e W p).hom.app M).hom.app U t =
        (0 : (W.functor.obj M).val.obj U) := by
    have h := inverseModulesIso_linear e W p M T
      (RingedToposMorphism.RingData.one T) (moduleZero M T)
      (moduleZero M T) (moduleZero M T) (fun V x ↦ by
        change (0 : M.val.obj V) = (1 : S.obj.obj V) • (0 : M.val.obj V) + 0
        simp) U t
    rw [e.ring_one _ _ (fun _ _ ↦ rfl)] at h
    change _ = (1 : R.obj.obj U) • (_ : (W.functor.obj M).val.obj U) +
      (_ : (W.functor.obj M).val.obj U) at h
    rw [one_smul] at h
    have hh : (show (W.functor.obj M).val.obj U from
        (e.inverse.map (moduleZero M T) ≫
          (inverseModulesIso e W p).hom.app M).hom.app U t) =
        (show (W.functor.obj M).val.obj U from
        (e.inverse.map (moduleZero M T) ≫
          (inverseModulesIso e W p).hom.app M).hom.app U t) +
        (show (W.functor.obj M).val.obj U from
        (e.inverse.map (moduleZero M T) ≫
          (inverseModulesIso e W p).hom.app M).hom.app U t) := h
    exact @add_eq_left ((W.functor.obj M).val.obj U) _ _ _ _ |>.mp hh.symm
  ext U t
  have h := inverseModulesIso_linear e W p M _
    (CartesianMonoidalCategory.fst _ _) (CartesianMonoidalCategory.snd _ _)
    (moduleZero M _) (moduleSMul M) (fun V x ↦ by
      exact (@add_zero (M.val.obj V) _
        (@SMul.smul (S.obj.obj V) (M.val.obj V) inferInstance x.1 x.2)).symm) U t
  rw [hz] at h
  change _ = (_ : R.obj.obj U) • (_ : (W.functor.obj M).val.obj U) +
    (0 : (W.functor.obj M).val.obj U) at h
  rw [add_zero] at h
  exact h

private theorem compare_binary
    {E E' : Type*} [Category E] [Category E']
    [CartesianMonoidalCategory E] [CartesianMonoidalCategory E']
    (F G : E ⥤ E') [PreservesFiniteLimits F] (q : F ≅ G)
    {X₁ X₂ X₃ : E} {Y₁ Y₂ Y₃ Z₁ Z₂ Z₃ : E'}
    (d₁ : F.obj X₁ ≅ Y₁) (d₂ : F.obj X₂ ≅ Y₂) (d₃ : F.obj X₃ ≅ Y₃)
    (t₁ : G.obj X₁ ≅ Z₁) (t₂ : G.obj X₂ ≅ Z₂) (t₃ : G.obj X₃ ≅ Z₃)
    (a : X₁ ⊗ X₂ ⟶ X₃) (b : Y₁ ⊗ Y₂ ⟶ Y₃) (c : Z₁ ⊗ Z₂ ⟶ Z₃)
    (hd : F.map a ≫ d₃.hom = CartesianMonoidalCategory.lift
      (F.map (CartesianMonoidalCategory.fst _ _) ≫ d₁.hom)
      (F.map (CartesianMonoidalCategory.snd _ _) ≫ d₂.hom) ≫ b)
    (ht : G.map a ≫ t₃.hom = CartesianMonoidalCategory.lift
      (G.map (CartesianMonoidalCategory.fst _ _) ≫ t₁.hom)
      (G.map (CartesianMonoidalCategory.snd _ _) ≫ t₂.hom) ≫ c) :
    b ≫ (d₃.symm ≪≫ q.app X₃ ≪≫ t₃).hom =
      ((d₁.symm ≪≫ q.app X₁ ≪≫ t₁).hom ⊗ₘ
        (d₂.symm ≪≫ q.app X₂ ≪≫ t₂).hom) ≫ c := by
  let P := CartesianMonoidalCategory.prodComparisonIso F X₁ X₂ ≪≫ (d₁ ⊗ᵢ d₂)
  apply (cancel_epi P.hom).mp
  have hP : P.hom = CartesianMonoidalCategory.lift
      (F.map (CartesianMonoidalCategory.fst _ _) ≫ d₁.hom)
      (F.map (CartesianMonoidalCategory.snd _ _) ≫ d₂.hom) := by
    simp only [P, Iso.trans_hom, tensorIso_hom,
      CartesianMonoidalCategory.prodComparisonIso_hom,
      CartesianMonoidalCategory.prodComparison, CartesianMonoidalCategory.lift_map]
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom]
  rw [← Category.assoc, hP, ← hd]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [q.hom.naturality_assoc, ht, CartesianMonoidalCategory.comp_lift_assoc]
  simp only [← q.hom.naturality_assoc]
  rw [CartesianMonoidalCategory.lift_map_assoc]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

private def liftModuleMap {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {M N : ringedSiteModules.{u} R}
    (f : (moduleSet R).obj M ⟶ (moduleSet R).obj N)
    (ha : ∀ U (x y : M.val.obj U), f.hom.app U (x + y) =
      @Add.add (N.val.obj U) inferInstance (f.hom.app U x) (f.hom.app U y))
    (hs : ∀ U (r : R.obj.obj U) (x : M.val.obj U), f.hom.app U (r • x) =
      @SMul.smul (R.obj.obj U) (N.val.obj U) inferInstance r (f.hom.app U x)) : M ⟶ N where
  val :=
    { app U := ModuleCat.ofHom
        { toFun := f.hom.app U
          map_add' := ha U
          map_smul' := hs U }
      naturality := by
        intro U V g
        ext x
        exact congrArg (fun h ↦ h x) (f.hom.naturality g) }

private def liftModuleIso {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {M N : ringedSiteModules.{u} R}
    (f : (moduleSet R).obj M ≅ (moduleSet R).obj N)
    (ha : ∀ U (x y : M.val.obj U), f.hom.hom.app U (x + y) =
      @Add.add (N.val.obj U) inferInstance (f.hom.hom.app U x) (f.hom.hom.app U y))
    (hs : ∀ U (r : R.obj.obj U) (x : M.val.obj U), f.hom.hom.app U (r • x) =
      @SMul.smul (R.obj.obj U) (N.val.obj U) inferInstance r (f.hom.hom.app U x)) : M ≅ N := by
  let e (U : Cᵒᵖ) : M.val.obj U ≃ N.val.obj U :=
    ((sheafToPresheaf J (Type u)).mapIso f).app U |>.toEquiv
  have ei (U : Cᵒᵖ) (x : M.val.obj U) : e U x = f.hom.hom.app U x := rfl
  have he (U : Cᵒᵖ) (x : N.val.obj U) : (e U).symm x = f.inv.hom.app U x := rfl
  refine
    { hom := liftModuleMap f.hom ha hs
      inv := liftModuleMap f.inv ?_ ?_
      hom_inv_id := by ext U x; exact (e U).symm_apply_apply x
      inv_hom_id := by ext U x; exact (e U).apply_symm_apply x }
  · intro U x y
    apply (e U).injective
    change e U ((e U).symm (x + y)) =
      e U ((e U).symm x + (e U).symm y)
    rw [(e U).apply_symm_apply, ei, ha]
    change x + y = e U ((e U).symm x) + e U ((e U).symm y)
    rw [(e U).apply_symm_apply, (e U).apply_symm_apply]
  · intro U r x
    apply (e U).injective
    change e U ((e U).symm (r • x)) = e U (r • (e U).symm x)
    rw [(e U).apply_symm_apply, ei, hs]
    exact congrArg (fun y ↦ r • y) ((e U).apply_symm_apply x).symm


private abbrev restrictRing {C C' : Type u} [SmallCategory C] [SmallCategory C']
    {J : GrothendieckTopology C} {J' : GrothendieckTopology C'}
    (F : C' ⥤ C) [Functor.IsContinuous F J' J] (R : Sheaf J RingCat.{u}) :=
  (F.sheafPushforwardContinuous RingCat.{u} J' J).obj R

-- Use precomposition internally; compare explicitly with scalar restriction by identity.
private def restrictModules {C C' : Type u} [SmallCategory C] [SmallCategory C']
    {J : GrothendieckTopology C} {J' : GrothendieckTopology C'}
    (F : C' ⥤ C) [Functor.IsContinuous F J' J] (R : Sheaf J RingCat.{u}) :
    ringedSiteModules.{u} R ⥤ ringedSiteModules.{u} (restrictRing (J' := J') F R) where
  obj M :=
    { val := (PresheafOfModules.pushforward₀ F R.obj).obj M.val
      isSheaf := ((F.sheafPushforwardContinuous _ J' J).obj ⟨_, M.isSheaf⟩).property }
  map f := ⟨(PresheafOfModules.pushforward₀ F R.obj).map f.val⟩

private def restrictModulesIso {C C' : Type u} [SmallCategory C] [SmallCategory C']
    {J : GrothendieckTopology C} {J' : GrothendieckTopology C'}
    (F : C' ⥤ C) [Functor.IsContinuous F J' J] (R : Sheaf J RingCat.{u}) :
    restrictModules (J' := J') F R ≅
      SheafOfModules.pushforward (F := F) (𝟙 (restrictRing (J' := J') F R)) := by
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · exact (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun U ↦
        (ModuleCat.restrictScalarsId' (RingHom.id _) rfl).symm.app _)
        (by intros; ext x; rfl))
  · intros
    ext U x
    rfl

private theorem restrict_lift
    {C C' : Type u} [SmallCategory C] [SmallCategory C']
    {J : GrothendieckTopology C} {J' : GrothendieckTopology C'}
    (F : C' ⥤ C) [Functor.IsContinuous F J' J]
    {X Y Z : Sheaf J (Type u)} (f : X ⟶ Y) (g : X ⟶ Z) :
    (restrictSets (J' := J') F).map (CartesianMonoidalCategory.lift f g) =
      CartesianMonoidalCategory.lift ((restrictSets (J' := J') F).map f)
        ((restrictSets (J' := J') F).map g) := by
  ext U x
  rfl

private def restrictUnderlying
    {C C' : Type u} [SmallCategory C] [SmallCategory C']
    {J : GrothendieckTopology C} {J' : GrothendieckTopology C'}
    (F : C' ⥤ C) [Functor.IsContinuous F J' J] (R : Sheaf J RingCat.{u}) :
    restrictModules (J' := J') F R ⋙ moduleSet (restrictRing F R) ≅
      moduleSet R ⋙ restrictSets (J' := J') F := by
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · exact Iso.refl _
  · intro M N f
    ext U x
    rfl
private def moduleSquareSets
    {C D C' D' : Type u}
    [SmallCategory C] [SmallCategory D] [SmallCategory C'] [SmallCategory D']
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {J' : GrothendieckTopology C'} {K' : GrothendieckTopology D'}
    {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    (F : C' ⥤ C) (G : D' ⥤ D)
    [Functor.IsContinuous F J' J] [Functor.IsContinuous G K' K]
    (e : RingedToposMorphism R S) [e.inverse.IsEquivalence]
    (e' : RingedToposMorphism (restrictRing F R) (restrictRing G S))
    [e'.inverse.IsEquivalence]
    (q : e.inverse ⋙ restrictSets (J' := J') F ≅ restrictSets (J' := K') G ⋙ e'.inverse)
    (W : ringedSiteModules.{u} S ≌ ringedSiteModules.{u} R) (p : W.inverse ≅ e.modules)
    (W' : ringedSiteModules.{u} (restrictRing G S) ≌
      ringedSiteModules.{u} (restrictRing (J' := J') F R)) (p' : W'.inverse ≅ e'.modules) :
    (W.functor ⋙ restrictModules (J' := J') F R) ⋙ moduleSet (restrictRing F R) ≅
      (restrictModules (J' := K') G S ⋙ W'.functor) ⋙ moduleSet (restrictRing F R) := by
  let d := Functor.isoWhiskerLeft W.functor (restrictUnderlying F R) ≪≫
    Functor.isoWhiskerRight (inverseModulesIso e W p).symm (restrictSets (J' := J') F)
  let a := Functor.isoWhiskerLeft (moduleSet S) q
  let t := Functor.isoWhiskerRight (restrictUnderlying G S).symm e'.inverse ≪≫
    Functor.isoWhiskerLeft (restrictModules (J' := K') G S) (inverseModulesIso e' W' p')
  exact d ≪≫ a ≪≫ t



private theorem moduleSquareSets_hom
    {C D C' D' : Type u}
    [SmallCategory C] [SmallCategory D] [SmallCategory C'] [SmallCategory D']
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {J' : GrothendieckTopology C'} {K' : GrothendieckTopology D'}
    {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    (F : C' ⥤ C) (G : D' ⥤ D)
    [Functor.IsContinuous F J' J] [Functor.IsContinuous G K' K]
    (e : RingedToposMorphism R S) [e.inverse.IsEquivalence]
    (e' : RingedToposMorphism (restrictRing F R) (restrictRing G S))
    [e'.inverse.IsEquivalence]
    (q : e.inverse ⋙ restrictSets (J' := J') F ≅ restrictSets (J' := K') G ⋙ e'.inverse)
    (W : ringedSiteModules.{u} S ≌ ringedSiteModules.{u} R) (p : W.inverse ≅ e.modules)
    (W' : ringedSiteModules.{u} (restrictRing G S) ≌
      ringedSiteModules.{u} (restrictRing (J' := J') F R)) (p' : W'.inverse ≅ e'.modules)
    (M : ringedSiteModules.{u} S) :
    (moduleSquareSets F G e e' q W p W' p').hom.app M =
      (restrictSets (J' := J') F).map ((inverseModulesIso e W p).inv.app M) ≫
        q.hom.app ((moduleSet S).obj M) ≫
          (inverseModulesIso e' W' p').hom.app
            ((restrictModules (J' := K') G S).obj M) := by
  simp only [moduleSquareSets, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app,
    restrictUnderlying, NatIso.ofComponents_hom_app, NatIso.ofComponents_inv_app,
    Iso.refl_hom, Iso.refl_inv, Category.assoc]
  dsimp only [Functor.comp_obj]
  erw [e'.inverse.map_id]
  simp only [Category.id_comp]

attribute [irreducible] moduleSquareSets

-- A compatible square of set inverse images lifts to a square of module inverse images.
private def moduleSquare
    {C D C' D' : Type u}
    [SmallCategory C] [SmallCategory D] [SmallCategory C'] [SmallCategory D']
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {J' : GrothendieckTopology C'} {K' : GrothendieckTopology D'}
    {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    (F : C' ⥤ C) (G : D' ⥤ D)
    [Functor.IsContinuous F J' J] [Functor.IsContinuous G K' K]
    (e : RingedToposMorphism R S) [e.inverse.IsEquivalence] [IsIso e.ringMap]
    (e' : RingedToposMorphism (restrictRing F R) (restrictRing G S))
    [e'.inverse.IsEquivalence] [IsIso e'.ringMap]
    (q : e.inverse ⋙ restrictSets (J' := J') F ≅ restrictSets (J' := K') G ⋙ e'.inverse)
    (hr : q.hom.app (ringSets S) ≫ e'.ringMap = (restrictSets (J' := J') F).map e.ringMap)
    (W : ringedSiteModules.{u} S ≌ ringedSiteModules.{u} R) (p : W.inverse ≅ e.modules)
    (W' : ringedSiteModules.{u} (restrictRing G S) ≌
      ringedSiteModules.{u} (restrictRing (J' := J') F R)) (p' : W'.inverse ≅ e'.modules) :
    W.functor ⋙ restrictModules (J' := J') F R ≅ restrictModules (J' := K') G S ⋙ W'.functor := by
  let z := moduleSquareSets F G e e' q W p W' p'
  let d := inverseModulesIso e W p
  let t := inverseModulesIso e' W' p'
  have ha (M : ringedSiteModules.{u} S) :
      moduleAdd ((restrictModules (J' := J') F R).obj (W.functor.obj M)) ≫ z.hom.app M =
        (z.hom.app M ⊗ₘ z.hom.app M) ≫
          moduleAdd (W'.functor.obj ((restrictModules (J' := K') G S).obj M)) := by
    have hd := congrArg (restrictSets (J' := J') F).map (inverseModulesIso_add e W p M)
    simp only [Functor.map_comp, restrict_lift] at hd
    have hh := compare_binary (e.inverse ⋙ restrictSets (J' := J') F)
      (restrictSets (J' := K') G ⋙ e'.inverse) q
      ((restrictSets (J' := J') F).mapIso (d.app M)) ((restrictSets (J' := J') F).mapIso (d.app M))
      ((restrictSets (J' := J') F).mapIso (d.app M))
      (t.app ((restrictModules (J' := K') G S).obj M))
      (t.app ((restrictModules (J' := K') G S).obj M))
      (t.app ((restrictModules (J' := K') G S).obj M))
      (moduleAdd M)
      ((restrictSets (J' := J') F).map (moduleAdd (W.functor.obj M)))
      (moduleAdd (W'.functor.obj ((restrictModules (J' := K') G S).obj M)))
      hd (by
        ext U x
        exact congrArg (fun f ↦ f.hom.app U x)
          (inverseModulesIso_add e' W' p' ((restrictModules (J' := K') G S).obj M)))
    simp only [z, moduleSquareSets_hom]
    ext U x
    exact congrArg (fun f ↦ f.hom.app U x) hh
  have hs (M : ringedSiteModules.{u} S) :
      moduleSMul ((restrictModules (J' := J') F R).obj (W.functor.obj M)) ≫ z.hom.app M =
        (𝟙 _ ⊗ₘ z.hom.app M) ≫
          moduleSMul (W'.functor.obj ((restrictModules (J' := K') G S).obj M)) := by
    have hd := congrArg (restrictSets (J' := J') F).map (inverseModulesIso_smul e W p M)
    simp only [Functor.map_comp, restrict_lift] at hd
    have ht := inverseModulesIso_smul e' W' p'
      ((restrictModules (J' := K') G S).obj M)
    have h := compare_binary (e.inverse ⋙ restrictSets (J' := J') F)
      (restrictSets (J' := K') G ⋙ e'.inverse) q
      ((restrictSets (J' := J') F).mapIso (asIso e.ringMap))
      ((restrictSets (J' := J') F).mapIso (d.app M))
      ((restrictSets (J' := J') F).mapIso (d.app M))
      (asIso e'.ringMap) (t.app ((restrictModules (J' := K') G S).obj M))
      (t.app ((restrictModules (J' := K') G S).obj M))
      (moduleSMul M)
      ((restrictSets (J' := J') F).map (moduleSMul (W.functor.obj M)))
      (moduleSMul (W'.functor.obj ((restrictModules (J' := K') G S).obj M)))
      hd (by
        ext U x
        exact congrArg (fun f ↦ f.hom.app U x) ht)
    have hc : (((restrictSets (J' := J') F).mapIso (asIso e.ringMap)).symm ≪≫
        q.app (ringSets S) ≪≫ asIso e'.ringMap).hom = 𝟙 _ := by
      simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, asIso_hom,
        Functor.mapIso_inv, hr]
      rw [← Functor.map_comp]
      change (restrictSets (J' := J') F).map
        ((asIso e.ringMap).inv ≫ (asIso e.ringMap).hom) =
          𝟙 ((restrictSets (J' := J') F).obj (ringSets R))
      rw [Iso.inv_hom_id, Functor.map_id]
    rw [hc] at h
    simp only [z, moduleSquareSets_hom]
    ext U x
    exact congrArg (fun f ↦ f.hom.app U x) h
  refine NatIso.ofComponents (fun M ↦ liftModuleIso (z.app M) ?_ ?_) ?_
  · intro U x y
    exact congrArg (fun f ↦ f.hom.app U (x, y)) (ha M)
  · intro U r x
    exact congrArg (fun f ↦ f.hom.app U (r, x)) (hs M)
  · intro M N f
    ext U x
    exact congrArg (fun h ↦ h.hom.app U x) (z.hom.naturality f)



attribute [irreducible] moduleSquare

-- The original existential binders h and k are retained verbatim.
set_option linter.unusedVariables false in
/-- Slicing a ringed equivalence gives ringed equivalences, and the induced
module inverse images commute with restriction and further restriction.

Source: Stacks Project, sites-modules.tex, Tags 04IE and 04J4.
(blueprint: lem-weil-pbc-ringed-equivalence-slices).

Proof: over A send an arrow X → A to e.inverse X → e.inverse A.
Its inverse uses e.direct and the invertible adjunction unit. The unit and
counit are the original ones on the objects of the arrows. Conjugate with the
two element-site fibre equivalences. Preservation of products identifies the
restricted source ring with the inverse image of the restricted target ring;
use the restricted structural isomorphism for its ring map. This gives q and
its structural equation. Construct the module direct image from this geometric
adjunction and ring map. Module inverse image is obtained by transporting the
module operations, since the ring map is invertible. Both ways around a
restriction square have the same underlying set inverse image and the same
scalar action; the product/fibre comparison is therefore linear. Its inverse
is linear by the inverse structural isomorphism. Naturality follows by
applying the underlying functors to each module arrow. For a map B → A the
same computation uses the product over A, giving the further restriction
square. Any of the specified module equivalences has inverse naturally
isomorphic to the specified induced direct image. Uniqueness of left adjoints
therefore transports these squares to any choices of whole and slice module
transport. This argument imposes no boundedness or representability on A. -/
theorem ringed_equivalence_slices
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J CommRingCat.{u}} {S : Sheaf K CommRingCat.{u}}
    (e : RingedToposMorphism (localCoefficientRings R) (localCoefficientRings S))
    [e.inverse.IsEquivalence] [IsIso e.ringMap]
    (sourceSlices : ∀ A : Sheaf K (Type u),
      RingedSheafSliceAdjunctionData (localCoefficientRings S) A)
    (targetSlices : ∀ A : Sheaf J (Type u),
      RingedSheafSliceAdjunctionData (localCoefficientRings R) A) :
    ∃ (s : ∀ A : Sheaf K (Type u),
        RingedToposMorphism
          (localCoefficientRings (presentationElementRing R (e.inverse.obj A)))
          (localCoefficientRings (presentationElementRing S A)))
      (h : ∀ A : Sheaf K (Type u), (s A).inverse.IsEquivalence)
      (k : ∀ A : Sheaf K (Type u), IsIso (s A).ringMap)
      (q : ∀ A : Sheaf K (Type u),
        e.inverse ⋙ elementSheafPullback (e.inverse.obj A) ≅
          elementSheafPullback A ⋙ (s A).inverse),
      (∀ A : Sheaf K (Type u), Nonempty ((s A).inverse ≅
        (sourceSlices A).fibreEquivalence.functor ⋙ Over.post e.inverse ⋙
          (targetSlices (e.inverse.obj A)).fibreEquivalence.inverse)) ∧
      (∀ A : Sheaf K (Type u),
        (q A).hom.app ((sheafCompose K (forget RingCat)).obj (localCoefficientRings S)) ≫
          (s A).ringMap = (elementSheafPullback (e.inverse.obj A)).map e.ringMap) ∧
      ∀ (whole : RingedPresentationAt e)
        (T : ∀ A : Sheaf K (Type u), RingedPresentationAt (s A))
        (rs : RingedPresentationRestrictions S) (rt : RingedPresentationRestrictions R),
        (∀ A : Sheaf K (Type u),
          Nonempty (whole.transport.modules.functor ⋙
            elementModulePullback.{u, u} (localCoefficientRings R) (e.inverse.obj A) ≅
              elementModulePullback.{u, u} (localCoefficientRings S) A ⋙
                (T A).transport.modules.functor)) ∧
        ∀ {A B : Sheaf K (Type u)} (b : B ⟶ A),
          Nonempty ((T A).transport.modules.functor ⋙
            elementModulePullbackOver.{u, u} (localCoefficientRings R) (e.inverse.map b)
              (rt.overContinuous (e.inverse.map b)) ≅
            elementModulePullbackOver.{u, u} (localCoefficientRings S) b
              (rs.overContinuous b) ⋙ (T B).transport.modules.functor) := by
  classical
  let s := fun A ↦ sliceMorphism e A (sourceSlices A) (targetSlices (e.inverse.obj A))
  have h (A) : (s A).inverse.IsEquivalence := sliceMorphism_equivalence _ _ _ _
  have k (A) : IsIso (s A).ringMap := sliceMorphism_ringIso e A _ _
  let q (A : Sheaf K (Type u)) :=
    sliceMorphismComparison e A (sourceSlices A) (targetSlices (e.inverse.obj A))
  refine ⟨s, h, k, q, ?_, ?_, ?_⟩
  · intro A
    dsimp only [s]
    rw [sliceMorphism_inverse]
    exact ⟨Iso.refl _⟩
  · intro A
    exact sliceMorphismComparison_structural e A _ _
  · intro whole T rs rt
    constructor
    · intro A
      let := h A
      let := k A
      exact ⟨(Functor.isoWhiskerLeft whole.transport.modules.functor
        (restrictModulesIso (elementProjection (e.inverse.obj A))
          (localCoefficientRings R))).symm ≪≫
        moduleSquare (elementProjection (e.inverse.obj A)) (elementProjection A)
        e (s A) (q A) (sliceMorphismComparison_structural e A _ _)
        whole.transport.modules whole.pushforward (T A).transport.modules (T A).pushforward ≪≫
        Functor.isoWhiskerRight
          (restrictModulesIso (elementProjection A) (localCoefficientRings S))
          (T A).transport.modules.functor⟩
    · intro A B b
      let := h A
      let := k A
      let := h B
      let := k B
      let := rs.overContinuous b
      let := rt.overContinuous (e.inverse.map b)
      let c := sliceMorphismFurtherComparison e b (rs.overContinuous b)
        (rt.overContinuous (e.inverse.map b)) (sourceSlices A) (sourceSlices B)
        (targetSlices (e.inverse.obj A)) (targetSlices (e.inverse.obj B))
      have hr := sliceMorphismFurther_structural e b (rs.overContinuous b)
        (rt.overContinuous (e.inverse.map b)) (sourceSlices A) (sourceSlices B)
        (targetSlices (e.inverse.obj A)) (targetSlices (e.inverse.obj B))
      exact ⟨(Functor.isoWhiskerLeft (T A).transport.modules.functor
        (restrictModulesIso (elementMap (e.inverse.map b))
          (localCoefficientRings (presentationElementRing R (e.inverse.obj A))))).symm ≪≫
        moduleSquare (elementMap (e.inverse.map b)) (elementMap b)
        (s A) (s B) c hr (T A).transport.modules (T A).pushforward
        (T B).transport.modules (T B).pushforward ≪≫
        Functor.isoWhiskerRight
          (restrictModulesIso (elementMap b)
            (localCoefficientRings (presentationElementRing S A)))
          (T B).transport.modules.functor⟩

end CategoryTheory
