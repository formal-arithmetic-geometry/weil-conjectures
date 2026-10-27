/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V6
-/
module

public import Sheaf.Paper.PurAdicLineSystemData
import Mathlib.CategoryTheory.ShrinkYoneda
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Sites.Limits
import Sheaf.CategoryTheory.Sites.InverseImageLocalFamilies
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Limits

/-! # Semilinear comparison of locally based integral towers

Source: the integral twist paragraph of
`sk-prop-sfb-cartesian-coefficients-twists.proof.md`.
(blueprint: lem-pur-adic-integral-comparison).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

universe w uC vC uD vD

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

attribute [local instance 2000] purAdicHasSheafComposeRingSets
  purAdicHasSheafComposeModuleSets purAdicHasSheafComposeCoefficients

-- Realize local slice bases as products with sheafified representables.
private theorem sigma_ext {C : Type uC} [Category.{vC} C] {V X : C}
    (H : (Over V)ᵒᵖ ⥤ Type w) {a b : X ⟶ V}
    {s : H.obj (op (Over.mk a))} {t : H.obj (op (Over.mk b))}
    (h : a = b) (hs : H.map (eqToHom (by rw [h])).op t = s) :
    (⟨a, s⟩ : Σ a : X ⟶ V, H.obj (op (Over.mk a))) = ⟨b, t⟩ := by
  subst b
  simpa using congrArg
    (fun t : H.obj (op (Over.mk a)) ↦
      (⟨a, t⟩ : Σ a : X ⟶ V, H.obj (op (Over.mk a)))) hs.symm

private def sigmaRestriction {C : Type uC} [Category.{vC} C] {V X Y : C}
    (H : (Over V)ᵒᵖ ⥤ Type w) (b : Y ⟶ X)
    (z : Σ a : X ⟶ V, H.obj (op (Over.mk a))) :
    Σ a : Y ⟶ V, H.obj (op (Over.mk a)) :=
  ⟨b ≫ z.1, H.map (Over.homMk b rfl).op z.2⟩

private def sigmaPresheaf {C : Type uC} [Category.{vC} C] {V : C}
    (H : (Over V)ᵒᵖ ⥤ Type w) : Cᵒᵖ ⥤ Type (max vC w) where
  obj X := Σ a : X.unop ⟶ V, H.obj (op (Over.mk a))
  map b := ↾(sigmaRestriction H b.unop)
  map_id X := by
    apply ConcreteCategory.hom_ext
    rintro ⟨a, s⟩
    dsimp [sigmaRestriction]
    apply sigma_ext H (Category.id_comp _)
    congr 2
    congr 1
    apply Quiver.Hom.unop_inj
    ext
    simp
  map_comp b c := by
    apply ConcreteCategory.hom_ext
    rintro ⟨a, s⟩
    dsimp [sigmaRestriction]
    apply sigma_ext H (Category.assoc _ _ _)
    simp only [← Functor.map_comp_apply]
    congr 2
    congr 1
    apply Quiver.Hom.unop_inj
    ext
    simp

private def sigmaMap {C : Type uC} [Category.{vC} C] {V : C}
    {H H' : (Over V)ᵒᵖ ⥤ Type w} (f : H ⟶ H') :
    sigmaPresheaf H ⟶ sigmaPresheaf H' where
  app _ := ↾fun z ↦ ⟨z.1, f.app _ z.2⟩
  naturality X Y b := by
    apply ConcreteCategory.hom_ext
    rintro ⟨a, s⟩
    dsimp [sigmaPresheaf, sigmaRestriction]
    congr 1
    exact f.naturality_apply
      (Over.homMk b.unop rfl : Over.mk (b.unop ≫ a) ⟶ Over.mk a).op s

private instance sigmaSmall {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    {V : C} (H : (Over V)ᵒᵖ ⥤ Type w) :
    FunctorToTypes.Small.{w} (sigmaPresheaf H) := fun X ↦ by
  dsimp [sigmaPresheaf]
  infer_instance

private def sigmaFunctor {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    (J : GrothendieckTopology C) (V : C) :
    Sheaf (J.over V) (Type w) ⥤ (Cᵒᵖ ⥤ Type w) where
  obj H := FunctorToTypes.shrink (sigmaPresheaf H.obj)
  map f := FunctorToTypes.shrinkMap (sigmaMap f.hom)
  map_id H := by ext X x; simp [FunctorToTypes.shrinkMap, sigmaMap]
  map_comp {H H' H''} f g := by
    ext X x
    change equivShrink _ ((sigmaMap (f ≫ g).hom).app X ((equivShrink _).symm x)) =
      equivShrink _ ((sigmaMap g.hom).app X
        ((equivShrink ((sigmaPresheaf H'.obj).obj X)).symm
          (equivShrink _ ((sigmaMap f.hom).app X ((equivShrink _).symm x)))))
    rw [Equiv.symm_apply_apply]
    rfl

private def sigmaFst {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    (J : GrothendieckTopology C) (V : C) (F : Sheaf J (Type w)) :
    (sigmaFunctor J V).obj (F.over V) ⟶ shrinkYoneda.obj V where
  app X := ↾fun z ↦ equivShrink _ ((equivShrink _).symm z).1
  naturality X Y f := by
    ext x
    dsimp [sigmaFunctor, FunctorToTypes.shrink, sigmaPresheaf, sigmaRestriction,
      shrinkYoneda]
    simp only [Equiv.symm_apply_apply]

private def sigmaSnd {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    (J : GrothendieckTopology C) (V : C) (F : Sheaf J (Type w)) :
    (sigmaFunctor J V).obj (F.over V) ⟶ F.obj where
  app X := ↾fun z ↦ ((equivShrink _).symm z).2
  naturality X Y f := by
    ext x
    dsimp [sigmaFunctor, FunctorToTypes.shrink, sigmaPresheaf, sigmaRestriction]
    simp only [Equiv.symm_apply_apply]

private def sigmaFanIsLimit {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    (J : GrothendieckTopology C) (V : C) (F : Sheaf J (Type w)) :
    IsLimit (BinaryFan.mk (sigmaFst J V F) (sigmaSnd J V F)) := by
  refine BinaryFan.isLimitMk (fun s ↦ ?_) ?_ ?_ ?_
  · exact {
      app X := ↾fun z ↦ equivShrink _
        ⟨(equivShrink _).symm (s.fst.app X z), s.snd.app X z⟩
      naturality X Y f := by
        apply ConcreteCategory.hom_ext
        intro z
        change equivShrink ((sigmaPresheaf (F.over V).obj).obj Y)
            ⟨(equivShrink _).symm (s.fst.app Y (s.pt.map f z)), s.snd.app Y (s.pt.map f z)⟩ =
          equivShrink ((sigmaPresheaf (F.over V).obj).obj Y)
            (sigmaRestriction (F.over V).obj f.unop
              ((equivShrink ((sigmaPresheaf (F.over V).obj).obj X)).symm
                (equivShrink ((sigmaPresheaf (F.over V).obj).obj X) ⟨_, _⟩)))
        rw [Equiv.symm_apply_apply]
        apply congrArg (equivShrink.{w} ((sigmaPresheaf (F.over V).obj).obj Y))
        dsimp [sigmaRestriction]
        have h := congrArg (equivShrink _).symm (s.fst.naturality_apply f z)
        change (equivShrink _).symm (s.fst.app Y (s.pt.map f z)) =
          (equivShrink _).symm
            (equivShrink _ (f.unop ≫ (equivShrink _).symm (s.fst.app X z))) at h
        rw [Equiv.symm_apply_apply] at h
        apply Sigma.ext h
        exact heq_of_eq (show s.snd.app Y (s.pt.map f z) =
          F.obj.map f (s.snd.app X z) from s.snd.naturality_apply f z) }
  · intro s; ext X z; simp [sigmaFst]
  · intro s; ext X z; simp [sigmaSnd]
  · intro s m h₁ h₂
    apply NatTrans.ext
    funext X
    apply ConcreteCategory.hom_ext
    intro z
    apply (equivShrink _).symm.injective
    change (equivShrink _).symm (m.app X z) =
      (equivShrink _).symm (equivShrink _ ⟨_, _⟩)
    rw [Equiv.symm_apply_apply]
    have h₁' := congrArg (equivShrink _).symm
      (ConcreteCategory.congr_hom (congr_app h₁ X) z)
    change (equivShrink _).symm (equivShrink _
      ((equivShrink _).symm (m.app X z)).1) = _ at h₁'
    rw [Equiv.symm_apply_apply] at h₁'
    apply Sigma.ext h₁'
    have h₂' := ConcreteCategory.congr_hom (congr_app h₂ X) z
    change ((equivShrink ((sigmaPresheaf (F.over V).obj).obj X)).symm
      (m.app X z)).2 = s.snd.app X z at h₂'
    exact heq_of_eq h₂' 

private theorem prodTowerLimits {E : Type uC} [Category.{vC} E] [HasBinaryProducts E]
    (X : E) : PreservesLimitsOfShape ℕᵒᵖ (prod.functor.obj X) := by
  let snd : prod.functor.obj X ⟶ 𝟭 E := { app Y := prod.snd }
  refine ⟨fun {F} ↦ ⟨fun {c} hc ↦ ⟨?_⟩⟩⟩
  let forgetCone (s : Cone (F ⋙ prod.functor.obj X)) : Cone F :=
    ⟨s.pt, s.π ≫ Functor.whiskerLeft F snd⟩
  refine {
    lift := fun s ↦ prod.lift (s.π.app (op 0) ≫ prod.fst) (hc.lift (forgetCone s))
    fac := ?_
    uniq := ?_ }
  · intro s n
    change prod.lift _ _ ≫ prod.map (𝟙 X) (c.π.app n) = s.π.app n
    apply prod.hom_ext
    · simp only [Category.assoc, prod.map_fst, Category.comp_id, prod.lift_fst]
      have h := congrArg (fun f ↦ f ≫ prod.fst)
        (s.w (homOfLE (Nat.zero_le n.unop)).op)
      change (s.π.app n ≫ prod.map (𝟙 X) (F.map _)) ≫ prod.fst =
        s.π.app (op 0) ≫ prod.fst at h
      simpa only [Category.assoc, prod.map_fst, Category.comp_id] using h.symm
    · simp only [Category.assoc, prod.map_snd, prod.lift_snd_assoc, hc.fac]
      rfl
  · intro s m hm
    have hm' (n : ℕᵒᵖ) : m ≫ prod.map (𝟙 X) (c.π.app n) = s.π.app n := hm n
    apply prod.hom_ext
    · rw [prod.lift_fst]
      have h := congrArg (fun f ↦ f ≫ prod.fst) (hm' (op 0))
      simpa only [Category.assoc, prod.map_fst, Category.comp_id] using h
    · rw [prod.lift_snd]
      apply hc.uniq (forgetCone s)
      intro n
      have h := congrArg (fun f ↦ f ≫ prod.snd) (hm' n)
      change (m ≫ prod.snd) ≫ c.π.app n = s.π.app n ≫ prod.snd
      simpa only [Category.assoc, prod.map_snd] using h

private def sigmaSheaf {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    (J : GrothendieckTopology C) [HasSheafify J (Type w)] (V : C) :
    Sheaf (J.over V) (Type w) ⥤ Sheaf J (Type w) :=
  sigmaFunctor J V ⋙ presheafToSheaf J (Type w)

private def sigmaSheafFst {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    (J : GrothendieckTopology C) [HasSheafify J (Type w)] (V : C)
    (F : Sheaf J (Type w)) :
    (sigmaSheaf J V).obj (F.over V) ⟶
      (presheafToSheaf J (Type w)).obj (shrinkYoneda.obj V) :=
  (presheafToSheaf J (Type w)).map (sigmaFst J V F)

private def sigmaSheafSnd {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    (J : GrothendieckTopology C) [HasSheafify J (Type w)] (V : C)
    (F : Sheaf J (Type w)) : (sigmaSheaf J V).obj (F.over V) ⟶ F :=
  (presheafToSheaf J (Type w)).map (sigmaSnd J V F) ≫
    (sheafificationAdjunction J (Type w)).counit.app F

private def sigmaSheafFanIsLimit
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    (J : GrothendieckTopology C) [HasSheafify J (Type w)] (V : C)
    (F : Sheaf J (Type w)) :
    IsLimit (BinaryFan.mk (sigmaSheafFst J V F) (sigmaSheafSnd J V F)) := by
  exact BinaryFan.isLimitCompRightIso _
    ((sheafificationAdjunction J (Type w)).counit.app F)
    (mapIsLimitOfPreservesOfIsLimit (presheafToSheaf J (Type w)) _ _
      (sigmaFanIsLimit J V F))

private def sigmaSheafProductObj
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    (J : GrothendieckTopology C) [HasSheafify J (Type w)] (V : C)
    (F : Sheaf J (Type w)) :
    (sigmaSheaf J V).obj (F.over V) ≅
      (presheafToSheaf J (Type w)).obj (shrinkYoneda.obj V) ⨯ F where
  hom := prod.lift (sigmaSheafFst J V F) (sigmaSheafSnd J V F)
  inv := BinaryFan.IsLimit.lift (sigmaSheafFanIsLimit J V F) prod.fst prod.snd
  hom_inv_id := by
    apply BinaryFan.IsLimit.hom_ext (sigmaSheafFanIsLimit J V F)
    · rw [Category.assoc, BinaryFan.IsLimit.lift_fst, Category.id_comp]
      exact prod.lift_fst _ _
    · rw [Category.assoc, BinaryFan.IsLimit.lift_snd, Category.id_comp]
      exact prod.lift_snd _ _
  inv_hom_id := by
    apply prod.hom_ext
    · rw [Category.assoc, prod.lift_fst, Category.id_comp]
      exact BinaryFan.IsLimit.lift_fst (sigmaSheafFanIsLimit J V F) _ _
    · rw [Category.assoc, prod.lift_snd, Category.id_comp]
      exact BinaryFan.IsLimit.lift_snd (sigmaSheafFanIsLimit J V F) _ _

private def sigmaSheafProduct
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    (J : GrothendieckTopology C) [HasSheafify J (Type w)] (V : C) :
    J.overPullback (Type w) V ⋙ sigmaSheaf J V ≅
      prod.functor.obj ((presheafToSheaf J (Type w)).obj (shrinkYoneda.obj V)) := by
  refine NatIso.ofComponents (sigmaSheafProductObj J V) ?_
  intro F G f
  change _ ≫ prod.lift _ _ = prod.lift _ _ ≫ prod.map (𝟙 _) f
  apply prod.hom_ext
  · simp only [Category.assoc, prod.lift_fst, prod.map_fst, Category.comp_id]
    change (presheafToSheaf J (Type w)).map
      ((sigmaFunctor J V).map ((J.overPullback (Type w) V).map f)) ≫
        (presheafToSheaf J (Type w)).map (sigmaFst J V G) = _
    rw [← Functor.map_comp]
    have h : (sigmaFunctor J V).map ((J.overPullback (Type w) V).map f) ≫
        sigmaFst J V G = sigmaFst J V F := by
      ext X x
      dsimp [sigmaFunctor, FunctorToTypes.shrinkMap, sigmaMap, sigmaFst]
      simp only [Equiv.symm_apply_apply]
    exact congrArg (presheafToSheaf J (Type w)).map h
  · simp only [Category.assoc, prod.lift_snd, prod.map_snd]
    change (presheafToSheaf J (Type w)).map
      ((sigmaFunctor J V).map ((J.overPullback (Type w) V).map f)) ≫
        (presheafToSheaf J (Type w)).map (sigmaSnd J V G) ≫ _ = _
    rw [← Functor.map_comp_assoc]
    have h : (sigmaFunctor J V).map ((J.overPullback (Type w) V).map f) ≫
        sigmaSnd J V G = sigmaSnd J V F ≫ f.hom := by
      ext X x
      dsimp [sigmaFunctor, FunctorToTypes.shrinkMap, sigmaMap, sigmaSnd]
      simp only [Equiv.symm_apply_apply]
    rw [h, Functor.map_comp, Category.assoc]
    rw [prod.lift_snd_assoc]
    exact congrArg (fun t ↦ (presheafToSheaf J (Type w)).map (sigmaSnd J V F) ≫ t)
      ((sheafificationAdjunction J (Type w)).counit.naturality f)

private theorem preservesProductTower
    {E : Type uC} {F : Type uD} [Category.{vC} E] [Category.{vD} F]
    [HasBinaryProducts E] [HasBinaryProducts F]
    (L : E ⥤ F) [PreservesFiniteLimits L]
    (R : ℕᵒᵖ ⥤ E) [HasLimit R] [PreservesLimit R L] (X : E) :
    PreservesLimit (R ⋙ prod.functor.obj X) L := by
  have : PreservesLimitsOfShape ℕᵒᵖ (prod.functor.obj X) := prodTowerLimits X
  have : PreservesLimitsOfShape ℕᵒᵖ (prod.functor.obj (L.obj X)) := prodTowerLimits _
  have : PreservesLimit R (prod.functor.obj X ⋙ L) :=
    preservesLimit_of_natIso R (prodComparisonNatIso L X).symm
  exact preservesLimit_of_preserves_limit_cone
    (isLimitOfPreserves (prod.functor.obj X) (limit.isLimit R))
    (isLimitOfPreserves (prod.functor.obj X ⋙ L) (limit.isLimit R))

private theorem preservesLocalProductTower
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{w} C]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [HasSheafify J (Type w)]
    (L : Sheaf J (Type w) ⥤ Sheaf K (Type w)) [PreservesFiniteLimits L]
    (R M : ℕᵒᵖ ⥤ Sheaf J (Type w)) [HasLimit R] [HasLimit M]
    [PreservesLimit R L] (V : C)
    (b : R ⋙ J.overPullback (Type w) V ≅ M ⋙ J.overPullback (Type w) V) :
    PreservesLimit M (L ⋙ prod.functor.obj
      (L.obj ((presheafToSheaf J (Type w)).obj (shrinkYoneda.obj V)))) := by
  let X := (presheafToSheaf J (Type w)).obj (shrinkYoneda.obj V)
  have : PreservesLimitsOfShape ℕᵒᵖ (prod.functor.obj X) := prodTowerLimits X
  have : PreservesLimit (R ⋙ prod.functor.obj X) L := preservesProductTower L R X
  let q : R ⋙ prod.functor.obj X ≅ M ⋙ prod.functor.obj X :=
    (Functor.isoWhiskerLeft R (sigmaSheafProduct J V)).symm ≪≫
      Functor.isoWhiskerRight b (sigmaSheaf J V) ≪≫
        Functor.isoWhiskerLeft M (sigmaSheafProduct J V)
  have : PreservesLimit (M ⋙ prod.functor.obj X) L := preservesLimit_of_iso_diagram L q
  have : PreservesLimit M (prod.functor.obj X ⋙ L) := inferInstance
  exact preservesLimit_of_natIso M (prodComparisonNatIso L X)

private theorem productSection
    {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
    (X Y : Sheaf J (Type w)) (V : Cᵒᵖ) (x : X.obj.obj V) (y : Y.obj.obj V) :
    ∃ z : (X ⨯ Y).obj.obj V,
      (prod.fst : X ⨯ Y ⟶ X).hom.app V z = x ∧
        (prod.snd : X ⨯ Y ⟶ Y).hom.app V z = y := by
  let E := sheafToPresheaf J (Type w) ⋙ (evaluation Cᵒᵖ (Type w)).obj V
  let h := mapIsLimitOfPreservesOfIsLimit E _ _ (prodIsProd X Y)
  let f : PUnit ⟶ E.obj X := ↾fun _ ↦ x
  let g : PUnit ⟶ E.obj Y := ↾fun _ ↦ y
  refine ⟨BinaryFan.IsLimit.lift h f g PUnit.unit, ?_, ?_⟩
  · exact ConcreteCategory.congr_hom (BinaryFan.IsLimit.lift_fst h f g) PUnit.unit
  · exact ConcreteCategory.congr_hom (BinaryFan.IsLimit.lift_snd h f g) PUnit.unit

private theorem productSection_ext
    {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
    (X Y : Sheaf J (Type w)) (V : Cᵒᵖ) {x y : (X ⨯ Y).obj.obj V}
    (h₁ : (prod.fst : X ⨯ Y ⟶ X).hom.app V x = (prod.fst : X ⨯ Y ⟶ X).hom.app V y)
    (h₂ : (prod.snd : X ⨯ Y ⟶ Y).hom.app V x = (prod.snd : X ⨯ Y ⟶ Y).hom.app V y) : x = y := by
  let E := sheafToPresheaf J (Type w) ⋙ (evaluation Cᵒᵖ (Type w)).obj V
  let h := mapIsLimitOfPreservesOfIsLimit E _ _ (prodIsProd X Y)
  have he := BinaryFan.IsLimit.hom_ext h
    (show (↾fun _ : PUnit ↦ x) ≫ E.map prod.fst =
      (↾fun _ : PUnit ↦ y) ≫ E.map prod.fst by ext; exact h₁)
    (show (↾fun _ : PUnit ↦ x) ≫ E.map prod.snd =
      (↾fun _ : PUnit ↦ y) ≫ E.map prod.snd by ext; exact h₂)
  exact ConcreteCategory.congr_hom he PUnit.unit

-- A locally inhabited family detects isomorphisms after taking products.
private theorem productDetectsIso
    {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
    {ι : Type w} (E : ι → Sheaf J (Type w))
    (hE : ∀ (V : Cᵒᵖ), ∃ S : Sieve V.unop, S ∈ J V.unop ∧
      ∀ (W : C) (a : W ⟶ V.unop), S a → ∃ i : ι, Nonempty ((E i).obj.obj (op W)))
    {X Y : Sheaf J (Type w)} (f : X ⟶ Y)
    (hi : ∀ i, IsIso (prod.map (𝟙 (E i)) f)) : IsIso f := by
  have hb (i : ι) (V : Cᵒᵖ) (e : (E i).obj.obj V) :
      Function.Bijective (f.hom.app V) := by
    have := hi i
    have : IsIso ((prod.map (𝟙 (E i)) f).hom.app V) := inferInstance
    have bij := (isIso_iff_bijective _).1 this
    constructor
    · intro x y h
      obtain ⟨zx, hx₁, hx₂⟩ := productSection (E i) X V e x
      obtain ⟨zy, hy₁, hy₂⟩ := productSection (E i) X V e y
      have hz : (prod.map (𝟙 (E i)) f).hom.app V zx =
          (prod.map (𝟙 (E i)) f).hom.app V zy := by
        apply productSection_ext (E i) Y V
        · have ex := congrArg (fun k : E i ⨯ X ⟶ E i ↦ k.hom.app V zx)
            (prod.map_fst (𝟙 (E i)) f)
          have ey := congrArg (fun k : E i ⨯ X ⟶ E i ↦ k.hom.app V zy)
            (prod.map_fst (𝟙 (E i)) f)
          change (prod.fst : E i ⨯ Y ⟶ E i).hom.app V _ =
            (prod.fst : E i ⨯ X ⟶ E i).hom.app V zx at ex
          change (prod.fst : E i ⨯ Y ⟶ E i).hom.app V _ =
            (prod.fst : E i ⨯ X ⟶ E i).hom.app V zy at ey
          exact ex.trans (hx₁.trans (hy₁.symm.trans ey.symm))
        · have ex := congrArg (fun k : E i ⨯ X ⟶ Y ↦ k.hom.app V zx)
            (prod.map_snd (𝟙 (E i)) f)
          have ey := congrArg (fun k : E i ⨯ X ⟶ Y ↦ k.hom.app V zy)
            (prod.map_snd (𝟙 (E i)) f)
          change (prod.snd : E i ⨯ Y ⟶ Y).hom.app V _ =
            f.hom.app V ((prod.snd : E i ⨯ X ⟶ X).hom.app V zx) at ex
          change (prod.snd : E i ⨯ Y ⟶ Y).hom.app V _ =
            f.hom.app V ((prod.snd : E i ⨯ X ⟶ X).hom.app V zy) at ey
          exact ex.trans ((congrArg (f.hom.app V) hx₂).trans
            (h.trans ((congrArg (f.hom.app V) hy₂).symm.trans ey.symm)))
      have he := congrArg (fun z ↦ (prod.snd : E i ⨯ X ⟶ X).hom.app V z)
        (bij.injective hz)
      simpa only [hx₂, hy₂] using he
    · intro y
      obtain ⟨z, _, hz⟩ := productSection (E i) Y V e y
      obtain ⟨x, hx⟩ := bij.surjective z
      refine ⟨(prod.snd : E i ⨯ X ⟶ X).hom.app V x, ?_⟩
      have he := congrArg (fun k : E i ⨯ X ⟶ Y ↦ k.hom.app V x)
        (prod.map_snd (𝟙 (E i)) f)
      change (prod.snd : E i ⨯ Y ⟶ Y).hom.app V _ =
        f.hom.app V ((prod.snd : E i ⨯ X ⟶ X).hom.app V x) at he
      exact he.symm.trans ((congrArg
        (fun z ↦ (prod.snd : E i ⨯ Y ⟶ Y).hom.app V z) hx).trans hz)
  apply (Sheaf.isLocallyBijective_iff_isIso f).1
  constructor
  · constructor
    intro V x y h
    obtain ⟨S, hS, hs⟩ := hE V
    apply J.superset_covering _ hS
    intro W a ha
    obtain ⟨i, ⟨e⟩⟩ := hs W a ha
    apply (hb i (op W) e).injective
    rw [NatTrans.naturality_apply, NatTrans.naturality_apply, h]
  · constructor
    intro V y
    obtain ⟨S, hS, hs⟩ := hE (op V)
    apply J.superset_covering _ hS
    intro W a ha
    obtain ⟨i, ⟨e⟩⟩ := hs W a ha
    exact (hb i (op W) e).surjective (Y.obj.map a.op y)

private theorem preservesTowerOfLocalBases
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{w} C]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [HasSheafify J (Type w)]
    (L : Sheaf J (Type w) ⥤ Sheaf K (Type w))
    (G : Sheaf K (Type w) ⥤ Sheaf J (Type w)) (adj : L ⊣ G)
    [PreservesFiniteLimits L]
    (R M : ℕᵒᵖ ⥤ Sheaf J (Type w)) [HasLimit R] [HasLimit M]
    [PreservesLimit R L]
    (ι : Type w) (V : ι → C)
    (hV : ∀ (W : C), ∃ S : Sieve W, S ∈ J W ∧
      ∀ (Z : C) (f : Z ⟶ W), S f → ∃ i : ι, Nonempty (Z ⟶ V i))
    (b : ∀ i, R ⋙ J.overPullback (Type w) (V i) ≅
      M ⋙ J.overPullback (Type w) (V i)) : PreservesLimit M L := by
  let E (i : ι) := (presheafToSheaf J (Type w)).obj (shrinkYoneda.obj (V i))
  let T := ⊤_ (Sheaf J (Type w))
  let t (i : ι) : E i ⟶ T := terminal.from _
  have hv : ∀ (W : Cᵒᵖ) (x : T.obj.obj W),
      ∃ S : Sieve W.unop, S ∈ J W.unop ∧
        ∀ (Z : C) (f : Z ⟶ W.unop), S f →
          ∃ (i : ι) (y : (E i).obj.obj (op Z)),
            (t i).hom.app (op Z) y = T.obj.map f.op x := by
    intro W x
    obtain ⟨S, hS, hs⟩ := hV W.unop
    refine ⟨S, hS, ?_⟩
    intro Z f hf
    obtain ⟨i, ⟨g⟩⟩ := hs Z f hf
    let y : (E i).obj.obj (op Z) :=
      (toSheafify J (shrinkYoneda.{w}.obj (V i))).app (op Z)
        (shrinkYonedaObjObjEquiv.{w}.symm g)
    refine ⟨i, y, ?_⟩
    let ev := sheafToPresheaf J (Type w) ⋙ (evaluation Cᵒᵖ (Type w)).obj (op Z)
    have hu := Types.isTerminalEquivUnique (ev.obj T)
      (IsTerminal.isTerminalObj ev T terminalIsTerminal)
    exact hu.uniq _ |>.trans (hu.uniq _).symm
  have hv' := Sheaf.map_jointly_locally_surjective L G adj t hv
  have hE : ∀ W : Dᵒᵖ, ∃ S : Sieve W.unop, S ∈ K W.unop ∧
      ∀ (Z : D) (f : Z ⟶ W.unop), S f →
        ∃ i : ι, Nonempty ((L.obj (E i)).obj.obj (op Z)) := by
    intro W
    let ev := sheafToPresheaf K (Type w) ⋙ (evaluation Dᵒᵖ (Type w)).obj W
    have hT := IsTerminal.isTerminalObj L T terminalIsTerminal
    have hu := Types.isTerminalEquivUnique (ev.obj (L.obj T))
      (IsTerminal.isTerminalObj ev _ hT)
    obtain ⟨S, hS, hs⟩ := hv' W hu.default
    exact ⟨S, hS, fun Z f hf ↦ by
      obtain ⟨i, y, _⟩ := hs Z f hf
      exact ⟨i, ⟨y⟩⟩⟩
  have hi (i : ι) : IsIso (prod.map (𝟙 (L.obj (E i))) (limit.post M L)) := by
    let P := prod.functor.obj (L.obj (E i))
    have : PreservesLimitsOfShape ℕᵒᵖ P := prodTowerLimits _
    have : PreservesLimit M (L ⋙ P) := preservesLocalProductTower J K L R M (V i) (b i)
    have he : P.map (limit.post M L) =
        limit.post M (L ⋙ P) ≫ inv (limit.post (M ⋙ L) P) := by
      rw [IsIso.eq_comp_inv, limit.post_post]
    change IsIso (P.map (limit.post M L))
    rw [he]
    infer_instance
  have : IsIso (limit.post M L) := productDetectsIso (fun i ↦ L.obj (E i)) hE _ hi
  exact preservesLimit_of_isIso_post L M

private theorem sheafForgetTowerLimits
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    (J : GrothendieckTopology C) {E : Type*} [Category E]
    (F : E ⥤ Type w) [J.HasSheafCompose F]
    [PreservesLimitsOfShape ℕᵒᵖ F] [HasLimitsOfShape ℕᵒᵖ E] :
    PreservesLimitsOfShape ℕᵒᵖ (sheafCompose J F) := by
  have : PreservesLimitsOfShape ℕᵒᵖ
      (sheafCompose J F ⋙ sheafToPresheaf J (Type w)) :=
    inferInstanceAs (PreservesLimitsOfShape ℕᵒᵖ
      (sheafToPresheaf J E ⋙ (Functor.whiskeringRight Cᵒᵖ E (Type w)).obj F))
  exact preservesLimitsOfShape_of_reflects_of_preserves _ (sheafToPresheaf J (Type w))

-- The supplied cofinal restriction fixes the coefficient limit and its projections.
private def ringCone
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    {J : GrothendieckTopology C} {I : Type w} [PartialOrder I] {e : I → ℕ}
    (A : PurAdicLineLimits.{w} J I e) (i : I) :
    Cone (Prod.sectR i ℕᵒᵖ ⋙ A.levels.R) :=
  (Cone.postcompose (A.subsequence i).inv).obj
    ((Cone.mk (A.integral.R.obj i) (A.rπ i)).whisker (purAdicStride (e i)))

private def ringConeIsLimit
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    {J : GrothendieckTopology C} {I : Type w} [PartialOrder I] {e : I → ℕ}
    (A : PurAdicLineLimits.{w} J I e) (hA : PurAdicCofinalRestriction A) (i : I) :
    IsLimit (ringCone A i) := by
  let F := purAdicStride (e i) ⋙ A.full i
  have : HasLimit F := (hA i).1
  let q := Classical.choose ((hA i).2 (limit.cone F) (limit.isLimit F))
  have hq := (Classical.choose_spec ((hA i).2 (limit.cone F) (limit.isLimit F))).1
  let S := (Cone.mk (A.integral.R.obj i) (A.rπ i)).whisker (purAdicStride (e i))
  have hs : IsLimit S := (limit.isLimit F).ofIsoLimit
    (Cone.ext q.symm (fun n ↦ by
      symm
      change q.inv ≫ (A.rπ i).app (op (e i * (n.unop + 1) - 1)) = limit.π F n
      rw [← hq n.unop, Iso.inv_hom_id_assoc]
      rfl))
  exact (IsLimit.postcomposeInvEquiv (A.subsequence i) S).symm hs

private theorem preservesOfConeIso
    {E F : Type*} [Category E] [Category F]
    {R : ℕᵒᵖ ⥤ E} (L : E ⥤ F) (T : Cone R) (hT : IsLimit T)
    {S' : ℕᵒᵖ ⥤ F} (T' : Cone S') (hT' : IsLimit T')
    (c : R ⋙ L ≅ S') (q : L.obj T.pt ≅ T'.pt)
    (hq : ∀ n, q.hom ≫ T'.π.app n = L.map (T.π.app n) ≫ c.hom.app n) :
    PreservesLimit R L := by
  apply preservesLimit_of_preserves_limit_cone hT
  apply (IsLimit.postcomposeHomEquiv c (L.mapCone T)).toFun
  exact hT'.ofIsoLimit (Cone.ext q.symm (fun n ↦ by
    symm
    change q.inv ≫ (L.map (T.π.app n) ≫ c.hom.app n) = T'.π.app n
    rw [← hq, Iso.inv_hom_id_assoc]))

private def ringLevelIso
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {I : Type w} [PartialOrder I] {L : Sheaf J (Type w) ⥤ Sheaf K (Type w)}
    {A : PurAdicPairDiagram.{w} J (I × ℕᵒᵖ)}
    {B : PurAdicPairDiagram.{w} K (I × ℕᵒᵖ)}
    (c : PurAdicPairComparison L A B) (i : I) :
    (Prod.sectR i ℕᵒᵖ ⋙ A.rings) ⋙ L ≅ Prod.sectR i ℕᵒᵖ ⋙ B.rings :=
  NatIso.ofComponents (fun n ↦ (c.a (i, n)).ringUnderlying)
    (fun f ↦ c.ring_natural (Prod.mkHom (𝟙 i) f))

private theorem ringProjectionComparison
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {I : Type w} [PartialOrder I] {e : I → ℕ}
    {L : Sheaf J (Type w) ⥤ Sheaf K (Type w)}
    (A : PurAdicLineLimits.{w} J I e) (B : PurAdicLineLimits.{w} K I e)
    (c : PurAdicPairComparison L A.levels B.levels)
    (a : PurAdicCoefficientComparison L A B c) (i : I) (n : ℕᵒᵖ) :
    (a.integral i).ringUnderlying.hom ≫
        (sheafCompose K (forget CommRingCat.{w})).map ((ringCone B i).π.app n) =
      L.map ((sheafCompose J (forget CommRingCat.{w})).map
        ((ringCone A i).π.app n)) ≫ (c.a (i, n)).ringUnderlying.hom := by
  let FA := sheafCompose J (forget CommRingCat.{w})
  let FB := sheafCompose K (forget CommRingCat.{w})
  have hs : L.map (FA.map ((A.subsequence i).inv.app n)) ≫
        (c.a (i, n)).ringUnderlying.hom =
      (a.full i (e i * (n.unop + 1) - 1)).ringUnderlying.hom ≫
        FB.map ((B.subsequence i).inv.app n) := by
    apply (cancel_mono (FB.map ((B.subsequence i).hom.app n))).mp
    simp only [Category.assoc, ← FB.map_comp, Iso.inv_hom_id_app]
    rw [← a.subsequence i n.unop, ← Category.assoc, ← L.map_comp, ← FA.map_comp]
    change L.map (FA.map ((A.subsequence i).inv.app n ≫
        (A.subsequence i).hom.app n)) ≫ _ = _ ≫ FB.map (𝟙 _)
    rw [Iso.inv_hom_id_app, FA.map_id, L.map_id, Category.id_comp,
      FB.map_id, Category.comp_id]
  change _ ≫ FB.map (_ ≫ _) = L.map (FA.map (_ ≫ _)) ≫ _
  rw [FB.map_comp, FA.map_comp, L.map_comp, Category.assoc, hs, ← Category.assoc]
  exact (congrArg (fun f ↦ f ≫ FB.map ((B.subsequence i).inv.app n))
    (a.projection i (e i * (n.unop + 1) - 1))).symm.trans (Category.assoc _ _ _)

private def moduleLevelIso
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {I : Type w} [PartialOrder I] {L : Sheaf J (Type w) ⥤ Sheaf K (Type w)}
    {A : PurAdicPairDiagram.{w} J (I × ℕᵒᵖ)}
    {B : PurAdicPairDiagram.{w} K (I × ℕᵒᵖ)}
    (c : PurAdicPairComparison L A B) (i : I) :
    (Prod.sectR i ℕᵒᵖ ⋙ A.modules) ⋙ L ≅ Prod.sectR i ℕᵒᵖ ⋙ B.modules :=
  NatIso.ofComponents (fun n ↦ purAdicModuleIso L A B (i, n) (c.a _) (c.c _))
    (fun f ↦ c.module_natural (Prod.mkHom (𝟙 i) f))

private theorem localBasisDiagrams
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C] [HasFiniteLimits C]
    (J : Precoverage C) {I : Type w} [PartialOrder I] {e : I → ℕ}
    (A : PurAdicLineLimits.{w} J.toGrothendieck I e)
    (bases : PurAdicLineLocallyBased J A) (i : I) :
    ∃ (Q : Type w) (V : Q → C),
      (∀ (W : C), ∃ S : Sieve W, S ∈ J.toGrothendieck W ∧
        ∀ (Z : C) (f : Z ⟶ W), S f → ∃ j : Q, Nonempty (Z ⟶ V j)) ∧
      Nonempty (∀ j, (Prod.sectR i ℕᵒᵖ ⋙ A.levels.rings) ⋙
          J.toGrothendieck.overPullback (Type w) (V j) ≅
        (Prod.sectR i ℕᵒᵖ ⋙ A.levels.modules) ⋙
          J.toGrothendieck.overPullback (Type w) (V j)) := by
  obtain ⟨Q, V, v, hv, b, hb⟩ := bases i
  refine ⟨Q, V, ?_, ?_⟩
  · intro W
    refine ⟨(Sieve.generate (Presieve.ofArrows V v)).pullback (terminal.from W),
      J.toGrothendieck.pullback_stable _
        (Precoverage.Saturate.of _ _ hv), ?_⟩
    intro Z f hf
    obtain ⟨Y, g, t, ⟨j⟩, ht⟩ := hf
    exact ⟨j, ⟨g⟩⟩
  · let B (j : Q) (n : ℕ) :
        (A.levels.rings.obj (i, op n)).over (V j) ≅
          (A.levels.modules.obj (i, op n)).over (V j) :=
      (sheafCompose (J.toGrothendieck.over (V j))
        (forget AddCommGrpCat.{w})).mapIso
          ((SheafOfModules.toSheaf _).mapIso (b j n)) ≪≫
      (J.toGrothendieck.overPullback (Type w) (V j)).mapIso
        ((sheafCompose J.toGrothendieck (forget AddCommGrpCat.{w})).mapIso
          (A.levels.identify (i, op n)))
    let β (j : Q) : (Prod.sectR i ℕᵒᵖ ⋙ A.levels.rings) ⋙
          J.toGrothendieck.overPullback (Type w) (V j) ⟶
        (Prod.sectR i ℕᵒᵖ ⋙ A.levels.modules) ⋙
          J.toGrothendieck.overPullback (Type w) (V j) :=
      NatTrans.ofOpSequence (fun n ↦ (B j n).hom) (fun n ↦ by
        ext W r
        exact (hb j n W.unop r).symm)
    have (j : Q) : IsIso (β j) := by
      have : ∀ n, IsIso ((β j).app n) := fun n ↦
        inferInstanceAs (IsIso (B j n.unop).hom)
      exact NatIso.isIso_of_isIso_app (β j)
    exact ⟨fun j ↦ asIso (β j)⟩

private theorem integralSetComparison
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
    [HasFiniteLimits C]
    (J : Precoverage C) (K : GrothendieckTopology D)
    (L : Sheaf J.toGrothendieck (Type w) ⥤ Sheaf K (Type w))
    (G : Sheaf K (Type w) ⥤ Sheaf J.toGrothendieck (Type w)) (adj : L ⊣ G)
    [PreservesFiniteLimits L]
    {I : Type w} [PartialOrder I] {e : I → ℕ}
    (A : PurAdicLineLimits.{w} J.toGrothendieck I e)
    (B : PurAdicLineLimits.{w} K I e)
    (c : PurAdicPairComparison L A.levels B.levels)
    (a : PurAdicCoefficientComparison L A B c)
    (bases : PurAdicLineLocallyBased J A)
    (hA : PurAdicCofinalRestriction A) (hB : PurAdicCofinalRestriction B) (i : I) :
    ∃ q : L.obj (A.integral.modules.obj i) ≅ B.integral.modules.obj i,
      ∀ n : ℕ, q.hom ≫ (sheafCompose K (forget AddCommGrpCat.{w})).map
          ((B.pπ i).app (op n)) =
        L.map ((sheafCompose J.toGrothendieck (forget AddCommGrpCat.{w})).map
          ((A.pπ i).app (op n))) ≫ (moduleLevelIso c i).hom.app (op n) := by
  let := hasSheafifyEssentiallySmallSite.{vC, w, uC, w + 1, w}
    J.toGrothendieck (Type w)
  let RA := sheafCompose J.toGrothendieck (forget CommRingCat.{w})
  let RB := sheafCompose K (forget CommRingCat.{w})
  let PA := sheafCompose J.toGrothendieck (forget AddCommGrpCat.{w})
  let PB := sheafCompose K (forget AddCommGrpCat.{w})
  have : PreservesLimitsOfShape ℕᵒᵖ RA := sheafForgetTowerLimits _ _
  have : PreservesLimitsOfShape ℕᵒᵖ RB := sheafForgetTowerLimits _ _
  have : PreservesLimitsOfShape ℕᵒᵖ PA := sheafForgetTowerLimits _ _
  have : PreservesLimitsOfShape ℕᵒᵖ PB := sheafForgetTowerLimits _ _
  let R := Prod.sectR i ℕᵒᵖ ⋙ A.levels.rings
  let M := Prod.sectR i ℕᵒᵖ ⋙ A.levels.modules
  let rA : Cone R := RA.mapCone (ringCone A i)
  let rB := RB.mapCone (ringCone B i)
  have hrA := isLimitOfPreserves RA (ringConeIsLimit A hA i)
  have hrB := isLimitOfPreserves RB (ringConeIsLimit B hB i)
  have : HasLimit R := ⟨⟨rA, hrA⟩⟩
  have : PreservesLimit R L := preservesOfConeIso L rA hrA rB hrB
    (ringLevelIso c i) (a.integral i).ringUnderlying (ringProjectionComparison A B c a i)
  let mA : Cone M := PA.mapCone (Cone.mk (A.integral.P.obj i) (A.pπ i))
  let mB := PB.mapCone (Cone.mk (B.integral.P.obj i) (B.pπ i))
  have hmA : IsLimit mA := isLimitOfPreserves PA (A.plimit i)
  have hmB : IsLimit mB := isLimitOfPreserves PB (B.plimit i)
  have : HasLimit M := ⟨⟨mA, hmA⟩⟩
  obtain ⟨Q, V, hV, ⟨b⟩⟩ := localBasisDiagrams J A bases i
  have : PreservesLimit M L := preservesTowerOfLocalBases _ _ L G adj R M Q V hV b
  let q := (isLimitOfPreserves L hmA).conePointsIsoOfNatIso hmB (moduleLevelIso c i)
  exact ⟨q, fun n ↦ IsLimit.conePointsIsoOfNatIso_hom_comp _ _ _ (op n)⟩

-- Recover the algebraic operations from their equations on every projection.
private theorem moduleSections_ext
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    {J : GrothendieckTopology C} {I : Type w} [PartialOrder I] {e : I → ℕ}
    (A : PurAdicLineLimits.{w} J I e) (i : I) (V : Cᵒᵖ)
    (x y : (A.integral.P.obj i).obj.obj V)
    (h : ∀ n : ℕ, ((A.pπ i).app (op n)).hom.app V x =
      ((A.pπ i).app (op n)).hom.app V y) : x = y := by
  let P := sheafCompose J (forget AddCommGrpCat.{w})
  have : PreservesLimitsOfShape ℕᵒᵖ P := sheafForgetTowerLimits _ _
  let E := sheafToPresheaf J (Type w) ⋙ (evaluation Cᵒᵖ (Type w)).obj V
  let hL := isLimitOfPreserves E (isLimitOfPreserves P (A.plimit i))
  have hh := hL.hom_ext (f := (↾fun _ : PUnit ↦ x))
    (f' := (↾fun _ : PUnit ↦ y)) (fun n ↦ by ext; exact h n.unop)
  exact ConcreteCategory.congr_hom hh PUnit.unit

private theorem mapPairSection
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (L : Sheaf J (Type w) ⥤ Sheaf K (Type w)) [PreservesFiniteLimits L]
    (X Y : Sheaf J (Type w)) (V : Dᵒᵖ)
    (x : (L.obj X).obj.obj V) (y : (L.obj Y).obj.obj V) :
    ∃ t : (L.obj (X ⨯ Y)).obj.obj V,
      (L.map (prod.fst : X ⨯ Y ⟶ X)).hom.app V t = x ∧
      (L.map (prod.snd : X ⨯ Y ⟶ Y)).hom.app V t = y := by
  let E := sheafToPresheaf K (Type w) ⋙ (evaluation Dᵒᵖ (Type w)).obj V
  let h := mapIsLimitOfPreservesOfIsLimit (L ⋙ E) _ _ (prodIsProd X Y)
  let f : PUnit ⟶ E.obj (L.obj X) := ↾fun _ ↦ x
  let g : PUnit ⟶ E.obj (L.obj Y) := ↾fun _ ↦ y
  refine ⟨BinaryFan.IsLimit.lift h f g PUnit.unit, ?_, ?_⟩
  · exact ConcreteCategory.congr_hom (BinaryFan.IsLimit.lift_fst h f g) PUnit.unit
  · exact ConcreteCategory.congr_hom (BinaryFan.IsLimit.lift_snd h f g) PUnit.unit

private def presentedAdd
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    {J : GrothendieckTopology C} {I : Type*} [Category I]
    (A : PurAdicPairDiagram.{w} J I) (i : I) :
    A.modules.obj i ⨯ A.modules.obj i ⟶ A.modules.obj i where
  hom := {
    app U := ↾fun t ↦ @Add.add ((A.P.obj i).obj.obj U) inferInstance
      ((prod.fst : A.modules.obj i ⨯ A.modules.obj i ⟶ _).hom.app U t)
      ((prod.snd : A.modules.obj i ⨯ A.modules.obj i ⟶ _).hom.app U t)
    naturality U V f := by
      ext t
      change @Add.add ((A.P.obj i).obj.obj V) inferInstance
        ((prod.fst : A.modules.obj i ⨯ A.modules.obj i ⟶ _).hom.app V
          ((A.modules.obj i ⨯ A.modules.obj i).obj.map f t))
        ((prod.snd : A.modules.obj i ⨯ A.modules.obj i ⟶ _).hom.app V
          ((A.modules.obj i ⨯ A.modules.obj i).obj.map f t)) =
        (A.P.obj i).obj.map f (_ + _)
      exact (congrArg₂ (fun x y : (A.P.obj i).obj.obj V ↦ x + y)
        (NatTrans.naturality_apply
          (prod.fst : A.modules.obj i ⨯ A.modules.obj i ⟶ _).hom f t)
        (NatTrans.naturality_apply
          (prod.snd : A.modules.obj i ⨯ A.modules.obj i ⟶ _).hom f t)).trans
        (((A.P.obj i).obj.map f).hom.map_add _ _).symm }

private def presentedSMul
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    {J : GrothendieckTopology C} {I : Type*} [Category I]
    (A : PurAdicPairDiagram.{w} J I) (i : I) :
    A.rings.obj i ⨯ A.modules.obj i ⟶ A.modules.obj i where
  hom := {
    app U := ↾fun t ↦ A.act i U
      ((prod.fst : A.rings.obj i ⨯ A.modules.obj i ⟶ _).hom.app U t)
      ((prod.snd : A.rings.obj i ⨯ A.modules.obj i ⟶ _).hom.app U t)
    naturality U V f := by
      ext t
      change A.act i V
        ((prod.fst : A.rings.obj i ⨯ A.modules.obj i ⟶ _).hom.app V
          ((A.rings.obj i ⨯ A.modules.obj i).obj.map f t))
        ((prod.snd : A.rings.obj i ⨯ A.modules.obj i ⟶ _).hom.app V
          ((A.rings.obj i ⨯ A.modules.obj i).obj.map f t)) =
        (A.P.obj i).obj.map f (A.act i U
          ((prod.fst : A.rings.obj i ⨯ A.modules.obj i ⟶ _).hom.app U t)
          ((prod.snd : A.rings.obj i ⨯ A.modules.obj i ⟶ _).hom.app U t))
      rw [NatTrans.naturality_apply
          (prod.fst : A.rings.obj i ⨯ A.modules.obj i ⟶ _).hom,
        NatTrans.naturality_apply
          (prod.snd : A.rings.obj i ⨯ A.modules.obj i ⟶ _).hom]
      dsimp [PurAdicPairDiagram.act]
      have h₁ := NatTrans.naturality_apply (A.identify i).hom.hom f
        (((prod.fst : A.rings.obj i ⨯ A.modules.obj i ⟶ _).hom.app U t) •
          @id ((A.M i).val.obj U) ((A.identify i).inv.hom.app U
            ((prod.snd : A.rings.obj i ⨯ A.modules.obj i ⟶ _).hom.app U t)))
      have h₂ := NatTrans.naturality_apply (A.identify i).inv.hom f
        ((prod.snd : A.rings.obj i ⨯ A.modules.obj i ⟶ _).hom.app U t)
      have h₃ := (A.M i).val.map_smul f
        ((prod.fst : A.rings.obj i ⨯ A.modules.obj i ⟶ _).hom.app U t)
        ((A.identify i).inv.hom.app U
          ((prod.snd : A.rings.obj i ⨯ A.modules.obj i ⟶ _).hom.app U t))
      exact (congrArg ((A.identify i).hom.hom.app V)
        ((congrArg (fun m : (A.M i).val.obj V ↦
          ((A.R.obj i).obj.map f _) • m) h₂).trans h₃.symm)).trans
        h₁ }

private theorem presentedAddGraph
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {I : Type*} [Category I] (L : Sheaf J (Type w) ⥤ Sheaf K (Type w))
    (A : PurAdicPairDiagram.{w} J I) (B : PurAdicPairDiagram.{w} K I) (i : I)
    (a : SheafOfModules.AlgebraicInverseImage L (A.R.obj i) (B.R.obj i))
    (ci : a.modules.obj (A.M i) ≅ B.M i)
    (T : Sheaf J (Type w)) (x y z : T ⟶ A.modules.obj i)
    (hz : ∀ U t, z.hom.app U t =
      @Add.add ((A.P.obj i).obj.obj U) inferInstance
        (x.hom.app U t) (y.hom.app U t))
    (V : Dᵒᵖ) (t : (L.obj T).obj.obj V) :
    (L.map z ≫ (purAdicModuleIso L A B i a ci).hom).hom.app V t =
      @Add.add ((B.P.obj i).obj.obj V) inferInstance
        ((L.map x ≫ (purAdicModuleIso L A B i a ci).hom).hom.app V t)
        ((L.map y ≫ (purAdicModuleIso L A B i a ci).hom).hom.app V t) := by
  let F := sheafCompose J (forget AddCommGrpCat.{w})
  let p := F.map (A.identify i).inv
  have h := a.moduleAdd (A.M i) T (x ≫ p) (y ≫ p) (z ≫ p) (by
    intro U t
    change (A.identify i).inv.hom.app U (z.hom.app U t) = _
    rw [hz]
    exact ((A.identify i).inv.hom.app U).hom.map_add _ _) V t
  have hh := congrArg (fun s : (a.modules.obj (A.M i)).val.obj V ↦
    (B.identify i).hom.hom.app V (ci.hom.val.app V s)) h
  simp only [purAdicModuleIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Functor.map_comp]
  simp only [Functor.map_comp] at h hh
  change (B.identify i).hom.hom.app V (ci.hom.val.app V
      ((a.moduleUnderlying.inv.app (A.M i)).hom.app V ((L.map z ≫ L.map p).hom.app V t))) =
    (B.identify i).hom.hom.app V (ci.hom.val.app V
      ((a.moduleUnderlying.inv.app (A.M i)).hom.app V ((L.map x ≫ L.map p).hom.app V t))) +
    (B.identify i).hom.hom.app V (ci.hom.val.app V
      ((a.moduleUnderlying.inv.app (A.M i)).hom.app V ((L.map y ≫ L.map p).hom.app V t)))
  simp only [map_add, id_eq] at hh
  exact hh

private theorem presentedSMulGraph
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {I : Type*} [Category I] (L : Sheaf J (Type w) ⥤ Sheaf K (Type w))
    (A : PurAdicPairDiagram.{w} J I) (B : PurAdicPairDiagram.{w} K I) (i : I)
    (a : SheafOfModules.AlgebraicInverseImage L (A.R.obj i) (B.R.obj i))
    (ci : a.modules.obj (A.M i) ≅ B.M i)
    (T : Sheaf J (Type w)) (r : T ⟶ A.rings.obj i)
    (x z : T ⟶ A.modules.obj i)
    (hz : ∀ U t, z.hom.app U t = A.act i U (r.hom.app U t) (x.hom.app U t))
    (V : Dᵒᵖ) (t : (L.obj T).obj.obj V) :
    (L.map z ≫ (purAdicModuleIso L A B i a ci).hom).hom.app V t =
      B.act i V ((L.map r ≫ a.ringUnderlying.hom).hom.app V t)
        ((L.map x ≫ (purAdicModuleIso L A B i a ci).hom).hom.app V t) := by
  let F := sheafCompose J (forget AddCommGrpCat.{w})
  let p := F.map (A.identify i).inv
  have h := a.moduleSMul (A.M i) T r (x ≫ p) (z ≫ p) (by
    intro U t
    change (A.identify i).inv.hom.app U (z.hom.app U t) = _
    rw [hz]
    change (A.identify i).inv.hom.app U
      ((A.identify i).hom.hom.app U _) = _
    exact ConcreteCategory.congr_hom
      (congrArg (fun f ↦ f.hom.app U) (A.identify i).hom_inv_id) _) V t
  have hh := congrArg (fun s : (a.modules.obj (A.M i)).val.obj V ↦
    (B.identify i).hom.hom.app V (ci.hom.val.app V s)) h
  simp only [purAdicModuleIso, PurAdicPairDiagram.act, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Functor.map_comp]
  simp only [Functor.map_comp] at h hh
  change (B.identify i).hom.hom.app V (ci.hom.val.app V
      ((a.moduleUnderlying.inv.app (A.M i)).hom.app V ((L.map z ≫ L.map p).hom.app V t))) =
    (B.identify i).hom.hom.app V
      ((a.ringUnderlying.hom.hom.app V ((L.map r).hom.app V t)) •
        @id ((B.M i).val.obj V) ((B.identify i).inv.hom.app V
          ((B.identify i).hom.hom.app V (ci.hom.val.app V
            ((a.moduleUnderlying.inv.app (A.M i)).hom.app V
              ((L.map x ≫ L.map p).hom.app V t))))))
  have hc (m : (B.M i).val.obj V) :
      (B.identify i).inv.hom.app V ((B.identify i).hom.hom.app V m) = m :=
    congrArg (fun f ↦ f.hom.app V m) (B.identify i).hom_inv_id
  rw [hc]
  simp only [map_smul, id_eq] at hh
  exact hh

private theorem integralGraphs
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {I : Type w} [PartialOrder I] {e : I → ℕ}
    (L : Sheaf J (Type w) ⥤ Sheaf K (Type w))
    (A : PurAdicLineLimits.{w} J I e) (B : PurAdicLineLimits.{w} K I e)
    (c : PurAdicPairComparison L A.levels B.levels)
    (a : PurAdicCoefficientComparison L A B c) (i : I)
    (q : L.obj (A.integral.modules.obj i) ≅ B.integral.modules.obj i)
    (hq : ∀ n : ℕ, q.hom ≫ (sheafCompose K (forget AddCommGrpCat.{w})).map
        ((B.pπ i).app (op n)) =
      L.map ((sheafCompose J (forget AddCommGrpCat.{w})).map
        ((A.pπ i).app (op n))) ≫ (moduleLevelIso c i).hom.app (op n)) :
    (∀ (T : Sheaf J (Type w)) (x y z : T ⟶ A.integral.modules.obj i),
      (∀ U t, z.hom.app U t = @Add.add ((A.integral.P.obj i).obj.obj U)
        inferInstance (x.hom.app U t) (y.hom.app U t)) →
      ∀ V t, (L.map z ≫ q.hom).hom.app V t =
        @Add.add ((B.integral.P.obj i).obj.obj V) inferInstance
          ((L.map x ≫ q.hom).hom.app V t) ((L.map y ≫ q.hom).hom.app V t)) ∧
    (∀ (T : Sheaf J (Type w)) (r : T ⟶ A.integral.rings.obj i)
      (x z : T ⟶ A.integral.modules.obj i),
      (∀ U t, z.hom.app U t =
        A.integral.act i U (r.hom.app U t) (x.hom.app U t)) →
      ∀ V t, (L.map z ≫ q.hom).hom.app V t =
        B.integral.act i V
          ((L.map r ≫ (a.integral i).ringUnderlying.hom).hom.app V t)
          ((L.map x ≫ q.hom).hom.app V t)) := by
  let PA := sheafCompose J (forget AddCommGrpCat.{w})
  let PB := sheafCompose K (forget AddCommGrpCat.{w})
  have hp (T : Sheaf J (Type w)) (z : T ⟶ A.integral.modules.obj i) (n : ℕ) :
      L.map z ≫ q.hom ≫ PB.map ((B.pπ i).app (op n)) =
        L.map (z ≫ PA.map ((A.pπ i).app (op n))) ≫
          (moduleLevelIso c i).hom.app (op n) := by
    rw [hq, L.map_comp, Category.assoc]
  constructor
  · intro T x y z hz V t
    apply moduleSections_ext B i V
    intro n
    have hn (z : T ⟶ A.integral.modules.obj i) :
        ((B.pπ i).app (op n)).hom.app V ((L.map z ≫ q.hom).hom.app V t) =
          (L.map (z ≫ PA.map ((A.pπ i).app (op n))) ≫
            (moduleLevelIso c i).hom.app (op n)).hom.app V t :=
      congrArg (fun f ↦ f.hom.app V t) (hp T z n)
    change ((B.pπ i).app (op n)).hom.app V _ =
      ((B.pπ i).app (op n)).hom.app V (_ + _)
    rw [map_add]
    rw [hn z, hn x, hn y]
    apply presentedAddGraph L A.levels B.levels (i, op n) (c.a _) (c.c _)
    intro U s
    change ((A.pπ i).app (op n)).hom.app U (z.hom.app U s) = _
    rw [hz]
    exact (((A.pπ i).app (op n)).hom.app U).hom.map_add _ _
  · intro T r x z hz V t
    apply moduleSections_ext B i V
    intro n
    have hn (z : T ⟶ A.integral.modules.obj i) :
        ((B.pπ i).app (op n)).hom.app V ((L.map z ≫ q.hom).hom.app V t) =
          (L.map (z ≫ PA.map ((A.pπ i).app (op n))) ≫
            (moduleLevelIso c i).hom.app (op n)).hom.app V t :=
      congrArg (fun f ↦ f.hom.app V t) (hp T z n)
    change ((B.pπ i).app (op n)).hom.app V _ =
      ((B.pπ i).app (op n)).hom.app V (B.integral.act i V _ _)
    rw [B.projection_smul, hn z, hn x]
    let r' := r ≫ (sheafCompose J (forget CommRingCat.{w})).map
      ((ringCone A i).π.app (op n))
    have hr : (L.map r' ≫ (c.a (i, op n)).ringUnderlying.hom).hom.app V t =
        ((B.subsequence i).inv.app (op n)).hom.app V
          (((B.rπ i).app (op (e i * (n + 1) - 1))).hom.app V
            ((L.map r ≫ (a.integral i).ringUnderlying.hom).hom.app V t)) := by
      have h := congrArg (fun f ↦ f.hom.app V t)
        (congrArg (fun f ↦ L.map r ≫ f) (ringProjectionComparison A B c a i (op n)))
      simp only [r', L.map_comp, Category.assoc] at h ⊢
      exact h.symm
    rw [← hr]
    apply presentedSMulGraph L A.levels B.levels (i, op n) (c.a _) (c.c _)
    intro U s
    change ((A.pπ i).app (op n)).hom.app U (z.hom.app U s) = _
    rw [hz]
    exact A.projection_smul i n U (r.hom.app U s) (x.hom.app U s)

private theorem isoSection_hom_inv
    {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
    {X Y : Sheaf J (Type w)} (s : X ≅ Y) (V : Cᵒᵖ) (x : X.obj.obj V) :
    s.inv.hom.app V (s.hom.hom.app V x) = x :=
  congrArg (fun f ↦ f.hom.app V x) s.hom_inv_id

private theorem isoSection_inv_hom
    {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
    {X Y : Sheaf J (Type w)} (s : X ≅ Y) (V : Cᵒᵖ) (y : Y.obj.obj V) :
    s.hom.hom.app V (s.inv.hom.app V y) = y :=
  congrArg (fun f ↦ f.hom.app V y) s.inv_hom_id

private theorem binaryCompare
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (L : Sheaf J (Type w) ⥤ Sheaf K (Type w)) [PreservesFiniteLimits L]
    {X Y Z : Sheaf J (Type w)} {X' Y' Z' X'' Y'' Z'' : Sheaf K (Type w)}
    (dX : L.obj X ≅ X') (dY : L.obj Y ≅ Y') (dZ : L.obj Z ≅ Z')
    (qX : L.obj X ⟶ X'') (qY : L.obj Y ⟶ Y'') (qZ : L.obj Z ⟶ Z'')
    (z : X ⨯ Y ⟶ Z)
    (μ : ∀ V, X'.obj.obj V → Y'.obj.obj V → Z'.obj.obj V)
    (ν : ∀ V, X''.obj.obj V → Y''.obj.obj V → Z''.obj.obj V)
    (hμ : ∀ V t, (L.map z ≫ dZ.hom).hom.app V t =
      μ V ((L.map prod.fst ≫ dX.hom).hom.app V t)
        ((L.map prod.snd ≫ dY.hom).hom.app V t))
    (hν : ∀ V t, (L.map z ≫ qZ).hom.app V t =
      ν V ((L.map prod.fst ≫ qX).hom.app V t)
        ((L.map prod.snd ≫ qY).hom.app V t))
    (V : Dᵒᵖ) (x : X'.obj.obj V) (y : Y'.obj.obj V) :
    qZ.hom.app V (dZ.inv.hom.app V (μ V x y)) =
      ν V (qX.hom.app V (dX.inv.hom.app V x))
        (qY.hom.app V (dY.inv.hom.app V y)) := by
  obtain ⟨t, hx, hy⟩ := mapPairSection L X Y V
    (dX.inv.hom.app V x) (dY.inv.hom.app V y)
  have hs := hμ V t
  change dZ.hom.hom.app V ((L.map z).hom.app V t) =
    μ V (dX.hom.hom.app V ((L.map prod.fst).hom.app V t))
      (dY.hom.hom.app V ((L.map prod.snd).hom.app V t)) at hs
  rw [hx, hy, isoSection_inv_hom, isoSection_inv_hom] at hs
  have he : dZ.inv.hom.app V (μ V x y) = (L.map z).hom.app V t := by
    rw [← hs, isoSection_hom_inv]
  rw [he]
  have ht := hν V t
  change qZ.hom.app V ((L.map z).hom.app V t) =
    ν V (qX.hom.app V ((L.map prod.fst).hom.app V t))
      (qY.hom.app V ((L.map prod.snd).hom.app V t)) at ht
  rw [hx, hy] at ht
  exact ht

private theorem integralLinearIso
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {I : Type w} [PartialOrder I] {e : I → ℕ}
    (L : Sheaf J (Type w) ⥤ Sheaf K (Type w)) [PreservesFiniteLimits L]
    (A : PurAdicLineLimits.{w} J I e) (B : PurAdicLineLimits.{w} K I e)
    (c : PurAdicPairComparison L A.levels B.levels)
    (a : PurAdicCoefficientComparison L A B c) (i : I)
    (q : L.obj (A.integral.modules.obj i) ≅ B.integral.modules.obj i)
    (hq : ∀ n : ℕ, q.hom ≫ (sheafCompose K (forget AddCommGrpCat.{w})).map
        ((B.pπ i).app (op n)) =
      L.map ((sheafCompose J (forget AddCommGrpCat.{w})).map
        ((A.pπ i).app (op n))) ≫ (moduleLevelIso c i).hom.app (op n)) :
    ∃ ci : (a.integral i).modules.obj (A.integral.M i) ≅ B.integral.M i,
      (purAdicModuleIso L A.integral B.integral i (a.integral i) ci).hom = q.hom := by
  let ai := a.integral i
  let M := ai.modules.obj (A.integral.M i)
  let N := B.integral.M i
  let F := sheafCompose J (forget AddCommGrpCat.{w})
  let H := sheafCompose K (forget AddCommGrpCat.{w})
  let p := F.mapIso (A.integral.identify i).symm
  let d : L.obj (A.integral.modules.obj i) ≅
      H.obj ((SheafOfModules.toSheaf _).obj M) :=
    L.mapIso p ≪≫ (ai.moduleUnderlying.app (A.integral.M i)).symm
  let s := d.symm ≪≫ q ≪≫ H.mapIso (B.integral.identify i).symm
  obtain ⟨hadd, hsmul⟩ := integralGraphs L A B c a i q hq
  have hdadd V t : (L.map (presentedAdd A.integral i) ≫ d.hom).hom.app V t =
      @Add.add (M.val.obj V) inferInstance
        ((L.map prod.fst ≫ d.hom).hom.app V t)
        ((L.map prod.snd ≫ d.hom).hom.app V t) := by
    have h := ai.moduleAdd (A.integral.M i) _
      (prod.fst ≫ p.hom) (prod.snd ≫ p.hom)
      (presentedAdd A.integral i ≫ p.hom) (by
        intro U t
        exact ((A.integral.identify i).inv.hom.app U).hom.map_add _ _) V t
    simp only [Functor.map_comp] at h
    exact h
  have hdsmul V t : (L.map (presentedSMul A.integral i) ≫ d.hom).hom.app V t =
      @SMul.smul ((B.integral.R.obj i).obj.obj V) (M.val.obj V) inferInstance
        ((L.map prod.fst ≫ ai.ringUnderlying.hom).hom.app V t)
        ((L.map prod.snd ≫ d.hom).hom.app V t) := by
    have h := ai.moduleSMul (A.integral.M i) _ prod.fst
      (prod.snd ≫ p.hom) (presentedSMul A.integral i ≫ p.hom) (by
        intro U t
        change (A.integral.identify i).inv.hom.app U
          ((A.integral.identify i).hom.hom.app U _) = _
        exact ConcreteCategory.congr_hom
          (congrArg (fun f ↦ f.hom.app U) (A.integral.identify i).hom_inv_id) _) V t
    simp only [Functor.map_comp] at h
    exact h
  have ha V (x y : M.val.obj V) : s.hom.hom.app V (x + y) =
      @Add.add (N.val.obj V) inferInstance (s.hom.hom.app V x) (s.hom.hom.app V y) := by
    have h := binaryCompare L d d d q.hom q.hom q.hom (presentedAdd A.integral i)
      (fun V x y ↦ @Add.add (M.val.obj V) inferInstance x y)
      (fun V x y ↦ @Add.add ((B.integral.P.obj i).obj.obj V) inferInstance x y)
      hdadd (hadd _ prod.fst prod.snd (presentedAdd A.integral i) (fun _ _ ↦ rfl))
      V x y
    exact (congrArg ((B.integral.identify i).inv.hom.app V) h).trans
      (((B.integral.identify i).inv.hom.app V).hom.map_add _ _)
  have hs V (r : (B.integral.R.obj i).obj.obj V) (x : M.val.obj V) :
      s.hom.hom.app V (r • x) =
        @SMul.smul ((B.integral.R.obj i).obj.obj V) (N.val.obj V) inferInstance
          r (s.hom.hom.app V x) := by
    have h := binaryCompare L ai.ringUnderlying d d ai.ringUnderlying.hom q.hom q.hom
      (presentedSMul A.integral i)
      (fun V r x ↦ @SMul.smul ((B.integral.R.obj i).obj.obj V)
        (M.val.obj V) inferInstance r x)
      (fun V r x ↦ B.integral.act i V r x)
      hdsmul (hsmul _ prod.fst prod.snd (presentedSMul A.integral i)
        (fun _ _ ↦ rfl)) V r x
    rw [isoSection_inv_hom] at h
    have hh := congrArg ((B.integral.identify i).inv.hom.app V) h
    change s.hom.hom.app V (r • x) =
      (B.integral.identify i).inv.hom.app V
        ((B.integral.identify i).hom.hom.app V _) at hh
    exact hh.trans (ConcreteCategory.congr_hom
      (congrArg (fun f ↦ f.hom.app V) (B.integral.identify i).hom_inv_id) _)
  let f : M ⟶ N := ⟨{
    app V := ModuleCat.ofHom
      { toFun := s.hom.hom.app V
        map_add' := ha V
        map_smul' := hs V }
    naturality {U V} g := by
      ext x
      exact congrArg (fun f ↦ f x) (s.hom.hom.naturality g) }⟩
  have happ (V : Dᵒᵖ) : IsIso (f.val.app V) :=
    (ConcreteCategory.isIso_iff_bijective _).2
      (ConcreteCategory.bijective_of_isIso (s.hom.hom.app V))
  let ep : M.val ≅ N.val := PresheafOfModules.isoMk
    (fun V ↦ asIso (f.val.app V)) (fun _ _ g ↦ f.val.naturality g)
  let ci : M ≅ N := {
    hom := f
    inv := ⟨ep.inv⟩
    hom_inv_id := by apply SheafOfModules.Hom.ext; exact ep.hom_inv_id
    inv_hom_id := by apply SheafOfModules.Hom.ext; exact ep.inv_hom_id }
  refine ⟨ci, ?_⟩
  change (L.mapIso p).hom ≫ (ai.moduleUnderlying.app (A.integral.M i)).inv ≫
    H.map ((SheafOfModules.toSheaf _).map ci.hom ≫ (B.integral.identify i).hom) = _
  change d.hom ≫ (s.hom ≫ (H.mapIso (B.integral.identify i)).hom) = _
  simp only [s, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]
  change q.hom ≫ H.map (B.integral.identify i).inv ≫
    H.map (B.integral.identify i).hom = q.hom
  rw [← H.map_comp, Iso.inv_hom_id, H.map_id]
  ext V x
  rfl

/-- The projection-normalized integral module comparison exists over the specified
coefficient comparison. No naturality in the coefficient index is assumed or concluded.
Source: the integral twist paragraph of the blueprint coefficient-twists proof;
Stacks, Sites, Tag 03CF, lemma-localize-morphism.
(blueprint: lem-pur-adic-integral-comparison).

Proof: Fix i. The supplied cofinal identifications make the full ring limit
also present the subsequence ring limit. The given projection equations
for a.integral and a.full show that the comparison from L of that ring limit to
the limit of its inverse image is invertible: compose it with the levelwise
ring isomorphisms and test on projections to obtain a.integral.
On each member of the one common cover, the compatible bases identify the module
tower with this ring tower. For a covering object V, sending a sheaf H on C/V to
the sheafification of the presheaf X ↦ Σ (f : X ⟶ V), H(X,f) identifies
this construction on restricted sheaves with h_V × (-), where h_V is the
sheafified representable. Thus the local bases identify h_V × the two towers.
Product with h_V preserves connected limits; finite-limit preservation of L
then gives preservation of the module tower after product with L(h_V).
The sheaves h_V form a locally surjective family over the terminal sheaf.
The adjunction carries that property to the family L(h_V). Hence the canonical
module-limit comparison is locally bijective, and therefore invertible.
Compose with the levelwise c comparisons and normalize by their projections.
On the product of the ring and module sheaves, test the scalar equation on every
projection; it follows from projection_smul and the graph equations for c and a.
The additive equation is proved in the same way. These equations lift the
underlying isomorphism to an isomorphism from the specified inverse image of A.integral.M i
to B.integral.M i. The inverse is linear by the same equations. This construction uses
only the comparison's projections, which are exactly the displayed formula. -/
theorem purAdicIntegralComparison_exists
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
    [HasFiniteLimits C] [HasFiniteLimits D]
    (J : Precoverage C) (K : Precoverage D)
    (hJ : J.IsSiteForCoverings) (hK : K.IsSiteForCoverings)
    (U : C ⥤ D) [PreservesFiniteLimits U]
    (hUcover : ∀ (X : C) (S : Presieve X), S ∈ J X → S.map U ∈ K (U.obj X))
    [U.IsContinuous J.toGrothendieck K.toGrothendieck]
    (L : Sheaf J.toGrothendieck (Type w) ⥤ Sheaf K.toGrothendieck (Type w))
    (adj : L ⊣ U.sheafPushforwardContinuous (Type w) J.toGrothendieck K.toGrothendieck)
    [PreservesFiniteLimits L]
    {I : Type w} [PartialOrder I] {e : I → ℕ}
    (A : PurAdicLineLimits.{w} J.toGrothendieck I e)
    (B : PurAdicLineLimits.{w} K.toGrothendieck I e)
    (c : PurAdicPairComparison L A.levels B.levels)
    (a : PurAdicCoefficientComparison L A B c)
    (bases : PurAdicLineLocallyBased J A)
    (hA : PurAdicCofinalRestriction A) (hB : PurAdicCofinalRestriction B) :
    ∀ i : I, ∃ ci : (a.integral i).modules.obj (A.integral.M i) ≅ B.integral.M i,
      ∀ n : ℕ,
        (purAdicModuleIso L A.integral B.integral i (a.integral i) ci).hom ≫
            (sheafCompose K.toGrothendieck (forget AddCommGrpCat.{w})).map
              ((B.pπ i).app (op n)) =
          L.map ((sheafCompose J.toGrothendieck (forget AddCommGrpCat.{w})).map
            ((A.pπ i).app (op n))) ≫
              (purAdicModuleIso L A.levels B.levels (i, op n) (c.a _) (c.c _)).hom := by
  -- The argument uses the adjunction directly; keep the specified site hypotheses.
  have _ := hJ
  have _ := hK
  have _ := hUcover
  intro i
  obtain ⟨q, hq⟩ := integralSetComparison J K.toGrothendieck L _ adj A B c a bases hA hB i
  obtain ⟨ci, hci⟩ := integralLinearIso L A B c a i q hq
  exact ⟨ci, fun n ↦ by rw [hci]; exact hq n⟩

end CategoryTheory
