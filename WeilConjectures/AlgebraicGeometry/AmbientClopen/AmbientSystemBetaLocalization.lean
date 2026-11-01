/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AmbientClopen.AmbientExactClopenData
import WeilConjectures.CategoryTheory.Exact.ExactLocalizationInverseMate
import all WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.SemilinearProperOpenMatePasting

/-! # Ambient SystemBetaLocalization

Source: Stacks Project, Tags 015F, 07A7 and 0F7B.
(blueprint: lem-sf-ambient-system-beta-localization)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v₁ v₂ w₁ w₂ h₁ h₂
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace AlgebraicGeometry.ProEtale.AmbientClopen

private theorem system_push_comp_heq
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n : ℕ, C (n + 1) ⟶ C n)
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    HEq (SemilinearProperOpen.pushComp C τ f g) (VaryingRing.modulePComp C τ f g) := by
  unfold SemilinearProperOpen.pushComp VaryingRing.modulePComp
  congr 1
  · simp only [SemilinearProperOpen.push_eq]
  · unfold SemilinearProperOpen.push
    rw [SemilinearProperOpen.coefficientMap_forget_eq,
      SemilinearProperOpen.coefficientMap_forget_eq,
      SemilinearProperOpen.coefficientMap_forget_eq]
    rfl
  · exact proof_irrel_heq _ _

private theorem chosen_adj_congr
    {A B : Type*} [Category A] [Category B]
    (P Q : B ⥤ A) [P.IsRightAdjoint] [Q.IsRightAdjoint] (h : P = Q) :
    HEq (Adjunction.ofIsRightAdjoint P) (Adjunction.ofIsRightAdjoint Q) := by
  subst Q
  rfl

private theorem left_comp_heq
    {A B D : Type*} [Category A] [Category B] [Category D]
    {L L₁ : A ⥤ B} {R R₁ : B ⥤ A}
    {M M₁ : B ⥤ D} {S S₁ : D ⥤ B}
    {N N₁ : A ⥤ D} {T T₁ : D ⥤ A}
    (a : L ⊣ R) (a₁ : L₁ ⊣ R₁) (b : M ⊣ S) (b₁ : M₁ ⊣ S₁)
    (c : N ⊣ T) (c₁ : N₁ ⊣ T₁) (d : S ⋙ R ≅ T) (d₁ : S₁ ⋙ R₁ ≅ T₁)
    (eL : L = L₁) (eR : R = R₁) (eM : M = M₁) (eS : S = S₁)
    (eN : N = N₁) (eT : T = T₁)
    (ha : HEq a a₁) (hb : HEq b b₁) (hc : HEq c c₁) (hd : HEq d d₁) :
    HEq (Adjunction.leftAdjointCompIso a b c d)
      (Adjunction.leftAdjointCompIso a₁ b₁ c₁ d₁) := by
  subst L₁
  subst R₁
  subst M₁
  subst S₁
  subst N₁
  subst T₁
  cases ha
  cases hb
  cases hc
  cases hd
  rfl

private theorem system_pull_comp_heq
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n : ℕ, C (n + 1) ⟶ C n)
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    HEq (SemilinearProperOpen.pullComp C τ f g) (VaryingRing.moduleGComp C τ f g) := by
  have := VaryingRing.push_isRightAdjoint C τ f
  have := VaryingRing.push_isRightAdjoint C τ g
  have := VaryingRing.push_isRightAdjoint C τ (f ≫ g)
  unfold SemilinearProperOpen.pullComp VaryingRing.moduleGComp
  have he := system_push_comp_heq C τ f g
  have haf : HEq (SemilinearProperOpen.ordinaryAdj C τ f) (VaryingRing.moduleAdj C τ f) :=
    chosen_adj_congr _ _ (SemilinearProperOpen.push_eq C τ f)
  have hag : HEq (SemilinearProperOpen.ordinaryAdj C τ g) (VaryingRing.moduleAdj C τ g) :=
    chosen_adj_congr _ _ (SemilinearProperOpen.push_eq C τ g)
  have hafg : HEq (SemilinearProperOpen.ordinaryAdj C τ (f ≫ g))
      (VaryingRing.moduleAdj C τ (f ≫ g)) :=
    chosen_adj_congr _ _ (SemilinearProperOpen.push_eq C τ (f ≫ g))
  have hcomp := left_comp_heq
    (SemilinearProperOpen.ordinaryAdj C τ g) (VaryingRing.moduleAdj C τ g)
    (SemilinearProperOpen.ordinaryAdj C τ f) (VaryingRing.moduleAdj C τ f)
    (SemilinearProperOpen.ordinaryAdj C τ (f ≫ g)) (VaryingRing.moduleAdj C τ (f ≫ g))
    (SemilinearProperOpen.pushComp C τ f g) (VaryingRing.modulePComp C τ f g)
    (SemilinearProperOpen.pull_eq C τ g) (SemilinearProperOpen.push_eq C τ g)
    (SemilinearProperOpen.pull_eq C τ f) (SemilinearProperOpen.push_eq C τ f)
    (SemilinearProperOpen.pull_eq C τ (f ≫ g))
    (SemilinearProperOpen.push_eq C τ (f ≫ g)) hag haf hafg he
  congr 1 <;> first
  | exact hcomp
  | rfl
  | simp only [SemilinearProperOpen.pull_eq]

private theorem derived_iso_heq
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (F F' G G' : A ⥤ B) [F.Additive] [F'.Additive] [G.Additive] [G'.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits G'] [PreservesFiniteColimits G']
    (a : F ≅ G) (a' : F' ≅ G') (hF : F = F') (hG : G = G') (ha : HEq a a') :
    HEq (Functor.mapDerivedCategoryNatIso a) (Functor.mapDerivedCategoryNatIso a') := by
  subst F'
  subst G'
  cases ha
  rfl

attribute [local instance] VaryingRing.pullAdditive VaryingRing.pullLimits
  VaryingRing.pullColimits VaryingRing.extensionAdditive VaryingRing.extensionLimits
  VaryingRing.extensionColimits

private theorem comp_iso_heq
    {A B D : Type*} [Category A] [Category B] [Category D]
    [Abelian A] [Abelian B] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory D]
    (F F' : A ⥤ B) (G G' : B ⥤ D)
    [F.Additive] [F'.Additive] [G.Additive] [G'.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits G'] [PreservesFiniteColimits G'] (hf : F = F') (hg : G = G') :
    HEq (Functor.mapDerivedCategoryCompIso F G) (Functor.mapDerivedCategoryCompIso F' G') := by
  subst F'
  subst G'
  rfl

private theorem trans_iso_heq
    {A : Type*} [Category A] {X X' Y Y' Z Z' : A}
    (a : X ≅ Y) (a' : X' ≅ Y') (b : Y ≅ Z) (b' : Y' ≅ Z')
    (hX : X = X') (hY : Y = Y') (hZ : Z = Z') (ha : HEq a a') (hb : HEq b b') :
    HEq (a ≪≫ b) (a' ≪≫ b') := by
  subst X'
  subst Y'
  subst Z'
  cases ha
  cases hb
  rfl

private theorem pcomp_heq
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n : ℕ, C (n + 1) ⟶ C n)
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    HEq (SemilinearProperOpen.pComp C τ f g) (VaryingRing.gComp C τ f g) := by
  have := VaryingRing.pullAdditive C τ f
  have := VaryingRing.pullAdditive C τ g
  have := VaryingRing.pullAdditive C τ (f ≫ g)
  have := VaryingRing.pullLimits C τ f
  have := VaryingRing.pullLimits C τ g
  have := VaryingRing.pullLimits C τ (f ≫ g)
  have := VaryingRing.pullColimits C τ f
  have := VaryingRing.pullColimits C τ g
  have := VaryingRing.pullColimits C τ (f ≫ g)
  unfold SemilinearProperOpen.pComp VaryingRing.gComp
  have hd := derived_iso_heq
    (SemilinearProperOpen.pull C τ (f ≫ g)) (VaryingRing.pull C τ (f ≫ g))
    (SemilinearProperOpen.pull C τ g ⋙ SemilinearProperOpen.pull C τ f)
    (VaryingRing.pull C τ g ⋙ VaryingRing.pull C τ f)
    (SemilinearProperOpen.pullComp C τ f g) (VaryingRing.moduleGComp C τ f g)
    (SemilinearProperOpen.pull_eq C τ (f ≫ g))
    (by simp only [SemilinearProperOpen.pull_eq]) (system_pull_comp_heq C τ f g)
  have hc := comp_iso_heq (SemilinearProperOpen.pull C τ g) (VaryingRing.pull C τ g)
    (SemilinearProperOpen.pull C τ f) (VaryingRing.pull C τ f)
    (SemilinearProperOpen.pull_eq C τ g) (SemilinearProperOpen.pull_eq C τ f)
  exact trans_iso_heq _ _ _ _ (SemilinearProperOpen.P_eq C τ (f ≫ g))
    (exact_derived_congr
      (by simp only [SemilinearProperOpen.pull_eq]))
    (by simp only [SemilinearProperOpen.P_eq]) hd hc

universe u₁ u₂ u₃ u₄ v₃ v₄ w₃ w₄

private theorem inverse_mate_localized
    {A : Type u₁} {B : Type u₂} {D : Type u₃} {F : Type u₄}
    [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} D] [Category.{v₄} F]
    [Abelian A] [Abelian B] [Abelian D] [Abelian F]
    [HasDerivedCategory.{w₁} A] [HasDerivedCategory.{w₂} B]
    [HasDerivedCategory.{w₃} D] [HasDerivedCategory.{w₄} F]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : D ⥤ F} {R₂ : F ⥤ D}
    {G : A ⥤ D} {H : B ⥤ F}
    [L₁.Additive] [R₁.Additive] [L₂.Additive] [R₂.Additive]
    [G.Additive] [H.Additive]
    [PreservesFiniteLimits L₁] [PreservesFiniteColimits L₁]
    [PreservesFiniteLimits R₁] [PreservesFiniteColimits R₁]
    [PreservesFiniteLimits L₂] [PreservesFiniteColimits L₂]
    [PreservesFiniteLimits R₂] [PreservesFiniteColimits R₂]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (d : R₁ ⋙ G ≅ H ⋙ R₂)
    (β : G ⋙ L₂ ≅ L₁ ⋙ H)
    (hβ : ∀ M, a₂.unit.app (G.obj M) ≫ R₂.map (β.hom.app M) =
      G.map (a₁.unit.app M) ≫ d.hom.app (L₁.obj M)) :
    ((mateEquiv (exactLocalizationDerivedAdjunction a₁)
      (exactLocalizationDerivedAdjunction a₂)).symm
      (TwoSquare.mk _ _ _ _ (Functor.mapDerivedCategorySquareIso d).hom)).natTrans =
      (Functor.mapDerivedCategorySquareIso β).hom := by
  have he : ((mateEquiv a₁ a₂).symm (TwoSquare.mk _ _ _ _ d.hom)).natTrans = β.hom := by
    apply NatTrans.ext
    funext M
    apply (a₂.homEquiv _ _).injective
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    exact (unit_mateEquiv_symm a₁ a₂ (TwoSquare.mk _ _ _ _ d.hom) M).symm.trans
      (hβ M).symm
  have : IsIso ((mateEquiv a₁ a₂).symm (TwoSquare.mk _ _ _ _ d.hom)).natTrans := by
    rw [he]
    infer_instance
  have hh := (exact_localization_inverse_mate a₁ a₂ d).2.1
  have hi : asIso ((mateEquiv a₁ a₂).symm (TwoSquare.mk _ _ _ _ d.hom)).natTrans = β :=
    Iso.ext he
  rw [hi] at hh
  exact hh

private theorem map_derived_transport
    {A B I : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (F : I → A ⥤ B) [∀ j, (F j).Additive]
    [∀ j, PreservesFiniteLimits (F j)] [∀ j, PreservesFiniteColimits (F j)]
    {j k : I} (h : j = k) :
    (Functor.mapDerivedCategoryNatIso (eqToIso (congrArg F h))).hom =
      (eqToIso (congrArg (fun j ↦ (F j).mapDerivedCategory) h)).hom := by
  cases h
  exact Functor.mapDerivedCategoryNatIso_refl

private theorem system_square_localization
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n : ℕ, C (n + 1) ⟶ C n)
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    (h : k ≫ p = r ≫ i) :
    Functor.mapDerivedCategorySquareIso (VaryingRing.moduleSquareG C τ k r p i h) =
      (VaryingRing.gComp C τ r i).symm ≪≫
        eqToIso (congrArg (VaryingRing.G C τ) h.symm) ≪≫ VaryingRing.gComp C τ k p := by
  rw [VaryingRing.moduleSquareG_eq]
  apply Iso.ext
  simp only [Functor.mapDerivedCategorySquareIso, VaryingRing.gComp,
    Functor.mapDerivedCategoryNatIso_trans, Functor.mapDerivedCategoryNatIso_symm,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Category.assoc]
  rw [map_derived_transport (fun f : U ⟶ Z ↦ VaryingRing.pull C τ f) h.symm]

private theorem iso_word_heq
    {A I : Type*} [Category A] (F F' : I → A) {j k : I} (h : j = k)
    {X X' Y Y' : A} (a : F j ≅ X) (a' : F' j ≅ X')
    (b : F k ≅ Y) (b' : F' k ≅ Y') (hF : F = F') (hX : X = X') (hY : Y = Y')
    (ha : HEq a a') (hb : HEq b b') :
    HEq (a.symm ≪≫ eqToIso (congrArg F h) ≪≫ b)
      (a'.symm ≪≫ eqToIso (congrArg F' h) ≪≫ b') := by
  subst F'
  subst X'
  subst Y'
  cases ha
  cases hb
  rfl

private theorem system_square_heq
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n : ℕ, C (n + 1) ⟶ C n)
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    (h : k ≫ p = r ≫ i) :
    HEq (SemilinearProperOpen.squareP C τ k r p i h)
      (Functor.mapDerivedCategorySquareIso (VaryingRing.moduleSquareG C τ k r p i h)) := by
  rw [system_square_localization]
  unfold SemilinearProperOpen.squareP
  exact iso_word_heq (SemilinearProperOpen.P C τ) (VaryingRing.G C τ) h.symm
    (SemilinearProperOpen.pComp C τ r i) (VaryingRing.gComp C τ r i)
    (SemilinearProperOpen.pComp C τ k p) (VaryingRing.gComp C τ k p)
    (funext fun f ↦ SemilinearProperOpen.P_eq C τ f)
    (by simp only [SemilinearProperOpen.P_eq])
    (by simp only [SemilinearProperOpen.P_eq]) (pcomp_heq C τ r i) (pcomp_heq C τ k p)

private theorem chosen_exact_adjunction_congr
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (P Q : A ⥤ B) [P.IsRightAdjoint] [Q.IsRightAdjoint]
    [P.Additive] [Q.Additive] [P.leftAdjoint.Additive] [Q.leftAdjoint.Additive]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    [PreservesFiniteLimits P.leftAdjoint] [PreservesFiniteColimits P.leftAdjoint]
    [PreservesFiniteLimits Q.leftAdjoint] [PreservesFiniteColimits Q.leftAdjoint]
    (h : P = Q) :
    HEq (Adjunction.ofIsRightAdjoint P).mapExactDerivedCategory
      (Adjunction.ofIsRightAdjoint Q).mapExactDerivedCategory := by
  subst Q
  rfl

private theorem system_open_adjunction_exact
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n : ℕ, C (n + 1) ⟶ C n)
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    HEq (exactLocalizationDerivedAdjunction
      (VaryingRing.moduleJAdj C τ j)) (SemilinearProperOpen.jAdj C τ j) := by
  have := SemilinearProperOpen.openPull_isRightAdjoint C τ j
  have := SemilinearProperOpen.pull_additive C τ j
  have := SemilinearProperOpen.pull_limits C τ j
  have := SemilinearProperOpen.pull_colimits C τ j
  have := SemilinearProperOpen.extension_additive C τ j
  have := SemilinearProperOpen.extension_limits C τ j
  have := SemilinearProperOpen.extension_colimits C τ j
  unfold SemilinearProperOpen.jAdj SemilinearProperOpen.J SemilinearProperOpen.P
    SemilinearProperOpen.ordinaryOpenAdj VaryingRing.moduleJAdj
    exactLocalizationDerivedAdjunction
  exact chosen_exact_adjunction_congr (VaryingRing.pull C τ j)
    (SemilinearProperOpen.pull C τ j) (SemilinearProperOpen.pull_eq C τ j).symm

private theorem inverse_mate_heq
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L₁ L₁' : A ⥤ B} {R₁ R₁' : B ⥤ A}
    {L₂ L₂' : C ⥤ D} {R₂ R₂' : D ⥤ C}
    {G G' : A ⥤ C} {H H' : B ⥤ D}
    (a : L₁ ⊣ R₁) (a' : L₁' ⊣ R₁') (b : L₂ ⊣ R₂) (b' : L₂' ⊣ R₂')
    (δ : R₁ ⋙ G ⟶ H ⋙ R₂) (δ' : R₁' ⋙ G' ⟶ H' ⋙ R₂')
    (e₁ : L₁ = L₁') (e₂ : R₁ = R₁') (e₃ : L₂ = L₂') (e₄ : R₂ = R₂')
    (e₅ : G = G') (e₆ : H = H') (ha : HEq a a') (hb : HEq b b') (hδ : HEq δ δ') :
    HEq ((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ δ)).natTrans
      ((mateEquiv a' b').symm (TwoSquare.mk _ _ _ _ δ')).natTrans := by
  subst L₁'
  subst R₁'
  subst L₂'
  subst R₂'
  subst G'
  subst H'
  cases ha
  cases hb
  cases hδ
  rfl

private theorem iso_inv_heq
    {A : Type*} [Category A] {X X' Y Y' : A}
    (e : X ≅ Y) (e' : X' ≅ Y') (hX : X = X') (hY : Y = Y') (he : HEq e e') :
    HEq e.inv e'.inv := by
  subst X'
  subst Y'
  cases he
  rfl

private theorem iso_hom_of_inv_heq
    {A : Type*} [Category A] {X X' Y Y' : A}
    (e : X ≅ Y) (e' : X' ≅ Y') (hX : X = X') (hY : Y = Y')
    (he : HEq e.inv e'.inv) : HEq e.hom e'.hom := by
  subst X'
  subst Y'
  exact congrArg Iso.hom (Iso.ext_inv (eq_of_heq he)) |>.heq

private theorem square_symm_hom
    {A B D F : Type*} [Category A] [Category B] [Category D] [Category F]
    [Abelian A] [Abelian B] [Abelian D] [Abelian F]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory D] [HasDerivedCategory F]
    {L₁ : A ⥤ B} {L₂ : B ⥤ F} {R₁ : A ⥤ D} {R₂ : D ⥤ F}
    [L₁.Additive] [L₂.Additive] [R₁.Additive] [R₂.Additive]
    [PreservesFiniteLimits L₁] [PreservesFiniteColimits L₁]
    [PreservesFiniteLimits L₂] [PreservesFiniteColimits L₂]
    [PreservesFiniteLimits R₁] [PreservesFiniteColimits R₁]
    [PreservesFiniteLimits R₂] [PreservesFiniteColimits R₂]
    (e : L₁ ⋙ L₂ ≅ R₁ ⋙ R₂) :
    (Functor.mapDerivedCategorySquareIso e.symm).hom =
      (Functor.mapDerivedCategorySquareIso e).inv := by
  simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    Iso.trans_inv, Functor.mapDerivedCategoryNatIso_symm, Category.assoc, Iso.symm_inv]

private theorem unit_homEquiv_symm
    {A B : Type*} [Category A] [Category B] {L : A ⥤ B} {R : B ⥤ A}
    (a : L ⊣ R) {M : A} {N : B} (f : M ⟶ R.obj N) :
    a.unit.app M ≫ R.map ((a.homEquiv M N).symm f) = f := by
  simpa only [Adjunction.homEquiv_unit] using (a.homEquiv M N).apply_symm_apply f

private theorem inverse_mate_app
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
    {G : A ⥤ C} {H : B ⥤ D} (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂)
    (δ : TwoSquare R₁ H G R₂) (M : A) :
    ((mateEquiv a b).symm δ).natTrans.app M = (b.homEquiv _ _).symm
      (G.map (a.unit.app M) ≫ δ.app (L₁.obj M)) := by
  apply (b.homEquiv (G.obj M) (H.obj (L₁.obj M))).injective
  calc
    _ = G.map (a.unit.app M) ≫ δ.app (L₁.obj M) := by
      rw [Adjunction.homEquiv_unit]
      exact (unit_mateEquiv_symm a b δ M).symm
    _ = _ := ((b.homEquiv _ _).apply_symm_apply _).symm

private theorem intrinsic_beta_inverse_mate
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n : ℕ, C (n + 1) ⟶ C n)
    {U' U X' X : Scheme.{u}} (a : U' ⟶ U) (b : U' ⟶ X')
    (i : U ⟶ X) (p : X' ⟶ X) [IsOpenImmersion i] [IsOpenImmersion b]
    (h : a ≫ i = b ≫ p) :
    ((mateEquiv (SemilinearProperOpen.jAdj C τ i) (SemilinearProperOpen.jAdj C τ b)).symm
      (TwoSquare.mk _ _ _ _ (SemilinearProperOpen.squareP C τ a b i p h).inv)).natTrans =
      SemilinearProperOpen.betaInv C τ a b i p h := by
  apply NatTrans.ext
  funext M
  exact inverse_mate_app (SemilinearProperOpen.jAdj C τ i)
    (SemilinearProperOpen.jAdj C τ b)
    (TwoSquare.mk _ _ _ _ (SemilinearProperOpen.squareP C τ a b i p h).inv) M

/-- Ambient SystemBetaLocalization. Source: Stacks Project, Tags 015F, 07A7 and 0F7B.
(blueprint: lem-sf-ambient-system-beta-localization)

Proof: The two ordinary pushforwards are equal because their coefficient ring maps
agree on every sequence-site object. Thus their chosen inverse images, open extensions
and adjunctions agree. The section-normalized direct-image compositors agree by their
uniqueness, so the pullback square compositor agrees after exact localization.
The inverse module beta is characterized by the open-unit equation. Exact localization
preserves that equation and the specified open adjunction; injectivity of its Hom
bijection identifies the localized inverse beta with the intrinsic inverse beta.
Taking inverses yields the displayed equality. -/
theorem system_beta_localized
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n : ℕ, C (n + 1) ⟶ C n)
    {U' U X' X : Scheme.{u}} (a : U' ⟶ U) (b : U' ⟶ X')
    (i : U ⟶ X) (p : X' ⟶ X) [IsOpenImmersion i] [IsOpenImmersion b]
    (h : a ≫ i = b ≫ p) (sq : IsPullback a b i p) :
    HEq (localizeSquare _ _ _ _ (VaryingRing.moduleBeta C τ a b i p h sq).hom)
      (SemilinearProperOpen.beta C τ a b i p h sq).hom := by
  have hl := inverse_mate_localized
    (VaryingRing.moduleJAdj C τ i) (VaryingRing.moduleJAdj C τ b)
    (VaryingRing.moduleSquareG C τ a b i p h).symm
    (VaryingRing.moduleBeta C τ a b i p h sq).symm (fun M ↦ by
      change (VaryingRing.moduleJAdj C τ b).unit.app _ ≫
        (VaryingRing.pull C τ b).map
          (((VaryingRing.moduleJAdj C τ b).homEquiv _ _).symm _) = _
      exact unit_homEquiv_symm (VaryingRing.moduleJAdj C τ b) _)
  have hs : HEq
      (Functor.mapDerivedCategorySquareIso
        (VaryingRing.moduleSquareG C τ a b i p h).symm).hom
      (SemilinearProperOpen.squareP C τ a b i p h).inv := by
    rw [square_symm_hom]
    exact iso_inv_heq _ _ (by simp only [SemilinearProperOpen.P_eq])
      (by simp only [SemilinearProperOpen.P_eq]) (system_square_heq C τ a b i p h).symm
  have hm := inverse_mate_heq
    (exactLocalizationDerivedAdjunction (VaryingRing.moduleJAdj C τ i))
    (SemilinearProperOpen.jAdj C τ i)
    (exactLocalizationDerivedAdjunction (VaryingRing.moduleJAdj C τ b))
    (SemilinearProperOpen.jAdj C τ b)
    (Functor.mapDerivedCategorySquareIso
      (VaryingRing.moduleSquareG C τ a b i p h).symm).hom
    (SemilinearProperOpen.squareP C τ a b i p h).inv
    (SemilinearProperOpen.J_eq C τ i).symm (SemilinearProperOpen.P_eq C τ i).symm
    (SemilinearProperOpen.J_eq C τ b).symm (SemilinearProperOpen.P_eq C τ b).symm
    (SemilinearProperOpen.P_eq C τ a).symm (SemilinearProperOpen.P_eq C τ p).symm
    (system_open_adjunction_exact C τ i) (system_open_adjunction_exact C τ b) hs
  rw [intrinsic_beta_inverse_mate] at hm
  have hi := HEq.trans hl.symm.heq hm
  rw [square_symm_hom] at hi
  change HEq (Functor.mapDerivedCategorySquareIso
    (VaryingRing.moduleBeta C τ a b i p h sq)).inv
    (SemilinearProperOpen.beta C τ a b i p h sq).inv at hi
  exact iso_hom_of_inv_heq _ _
    (by simp only [SemilinearProperOpen.J_eq, SemilinearProperOpen.P_eq])
    (by simp only [SemilinearProperOpen.J_eq, SemilinearProperOpen.P_eq]) hi

end AlgebraicGeometry.ProEtale.AmbientClopen
