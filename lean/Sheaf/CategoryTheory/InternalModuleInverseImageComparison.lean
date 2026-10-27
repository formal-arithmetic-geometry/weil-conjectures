/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Sheaf.CategoryTheory.Sites.GeometricMorphism
public import Sheaf.CategoryTheory.Sites.AbelianInverseImagePresentation
public import Sheaf.CategoryTheory.AlgebraicInverseImageOfUniverses
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.CategoryTheory.Sites.CartesianMonoidal

/-! # Internal and sectionwise module inverse images

Source: Stacks Project, Tags 03D2, 03EK, 03EL and 00YV; blueprint main-20261015,
`lem-sfb-module-mapmod-pullback-kflat`, opening inverse-image identification
(blueprint: lem-sfb-internal-module-inverse-image-comparison).

Normalization is expressed on all generalized sections, including the universal
pair of sections. Thus it specifies the inverse product comparison, without
assuming that sections of a sheafified tensor are globally pure tensors.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option synthInstance.maxSize 2048

universe u uC vC uD vD

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct CategoryTheory.Obj
attribute [instance] Sheaf.monoidalCategory Sheaf.braidedCategory

namespace CategoryTheory.InternalModuleInverseImage

private lemma right_unit_of_left_and_braiding
    {E : Type uC} {H : Type uD} [Category.{vC} E] [Category.{vD} H]
    [MonoidalCategory E] [MonoidalCategory H] [BraidedCategory E] [BraidedCategory H]
    (F : E ⥤ H) (e : 𝟙_ H ⟶ F.obj (𝟙_ E))
    (m : ∀ X Y, F.obj X ⊗ F.obj Y ⟶ F.obj (X ⊗ Y))
    (hb : ∀ X Y, m X Y ≫ F.map (β_ X Y).hom = (β_ _ _).hom ≫ m Y X)
    (hl : ∀ X, (λ_ (F.obj X)).hom = (e ⊗ₘ 𝟙 _) ≫ m _ X ≫ F.map (λ_ X).hom)
    (X : E) : (ρ_ (F.obj X)).hom =
      (𝟙 _ ⊗ₘ e) ≫ m X _ ≫ F.map (ρ_ X).hom := by
  calc
    (ρ_ (F.obj X)).hom = (β_ _ _).hom ≫ (λ_ (F.obj X)).hom :=
      (braiding_leftUnitor _).symm
    _ = (β_ _ _).hom ≫ (e ⊗ₘ 𝟙 _) ≫ m _ X ≫ F.map (λ_ X).hom := by rw [hl]
    _ = (𝟙 _ ⊗ₘ e) ≫ (β_ _ _).hom ≫ m _ X ≫ F.map (λ_ X).hom := by
      simp only [tensorHom_id, id_tensorHom]
      rw [← BraidedCategory.braiding_naturality_right_assoc]
    _ = (𝟙 _ ⊗ₘ e) ≫ m X _ ≫ F.map (β_ X _).hom ≫ F.map (λ_ X).hom := by
      simpa only [Category.assoc] using congrArg
        (fun k ↦ (𝟙 _ ⊗ₘ e) ≫ k ≫ F.map (λ_ X).hom) (hb X (𝟙_ E)).symm
    _ = (𝟙 _ ⊗ₘ e) ≫ m X _ ≫ F.map (ρ_ X).hom := by
      rw [← F.map_comp, braiding_leftUnitor]

section TensorUniversal

variable {C : Type uC} [Category.{vC} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{u}] [(J.W (A := AddCommGrpCat.{u})).IsMonoidal]

private lemma tensor_ext {X Y Z : Sheaf J AddCommGrpCat.{u}} {a b : X ⊗ Y ⟶ Z}
    (h : ∀ (V : Cᵒᵖ) (x : X.obj.obj V) (y : Y.obj.obj V),
      (a.hom.app V).hom
          (((Functor.LaxMonoidal.μ (sheafToPresheaf J AddCommGrpCat.{u}) X Y).app V).hom
            (x ⊗ₜ[ℤ] y)) =
        (b.hom.app V).hom
          (((Functor.LaxMonoidal.μ (sheafToPresheaf J AddCommGrpCat.{u}) X Y).app V).hom
            (x ⊗ₜ[ℤ] y))) : a = b := by
  apply Sheaf.tensor_hom_ext
  apply NatTrans.ext
  funext V
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.toIntLinearMap_injective
  apply TensorProduct.ext'
  exact h V

private def tensorComparison (X Y : Sheaf J AddCommGrpCat.{u}) :
    (presheafToSheaf J AddCommGrpCat.{u}).obj (X.obj ⊗ Y.obj) ⟶ X ⊗ Y :=
  Functor.OplaxMonoidal.δ (presheafToSheaf J AddCommGrpCat.{u}) X.obj Y.obj ≫
    ((sheafificationAdjunction J AddCommGrpCat.{u}).counit.app X ⊗ₘ
      (sheafificationAdjunction J AddCommGrpCat.{u}).counit.app Y)

private lemma tensorComparison_isIso (X Y : Sheaf J AddCommGrpCat.{u}) :
    IsIso (tensorComparison J X Y) := by
  dsimp only [tensorComparison]
  infer_instance

private def tensorPresheafLift {X Y Z : Sheaf J AddCommGrpCat.{u}}
    (b : ∀ V : Cᵒᵖ, X.obj.obj V →+ Y.obj.obj V →+ Z.obj.obj V)
    (hn : ∀ {V W : Cᵒᵖ} (g : V ⟶ W) (x : X.obj.obj V) (y : Y.obj.obj V),
      b W (X.obj.map g x) (Y.obj.map g y) = Z.obj.map g (b V x y)) :
    X.obj ⊗ Y.obj ⟶ Z.obj :=
    { app := fun V ↦ AddCommGrpCat.ofHom (TensorProduct.liftAddHom (b V) (by
        intro n x y
        rw [map_zsmul, map_zsmul]
        rfl))
      naturality := by
        intro V W g
        apply AddCommGrpCat.hom_ext
        apply AddMonoidHom.toIntLinearMap_injective
        apply TensorProduct.ext'
        intro x y
        change (TensorProduct.liftAddHom (b W) (by
            intro n x y
            rw [map_zsmul, map_zsmul]
            rfl))
            ((X.obj.map g ⊗ₘ Y.obj.map g).hom (x ⊗ₜ[ℤ] y)) =
          (Z.obj.map g).hom ((TensorProduct.liftAddHom (b V) (by
            intro n x y
            rw [map_zsmul, map_zsmul]
            rfl)) (x ⊗ₜ[ℤ] y))
        rw [AddCommGrpCat.MonoidalCategory.tensorHom_tmul,
          TensorProduct.liftAddHom_tmul, TensorProduct.liftAddHom_tmul]
        exact hn g x y }

private def tensorLift {X Y Z : Sheaf J AddCommGrpCat.{u}}
    (b : ∀ V : Cᵒᵖ, X.obj.obj V →+ Y.obj.obj V →+ Z.obj.obj V)
    (hn : ∀ {V W : Cᵒᵖ} (g : V ⟶ W) (x : X.obj.obj V) (y : Y.obj.obj V),
      b W (X.obj.map g x) (Y.obj.map g y) = Z.obj.map g (b V x y)) : X ⊗ Y ⟶ Z := by
  let a := sheafificationAdjunction J AddCommGrpCat.{u}
  let d := tensorComparison J X Y
  have : IsIso d := tensorComparison_isIso J X Y
  exact inv d ≫ (a.homEquiv _ _).symm (tensorPresheafLift J b hn)

private lemma tensorLift_spec {X Y Z : Sheaf J AddCommGrpCat.{u}}
    (b : ∀ V : Cᵒᵖ, X.obj.obj V →+ Y.obj.obj V →+ Z.obj.obj V)
    (hn : ∀ {V W : Cᵒᵖ} (g : V ⟶ W) (x : X.obj.obj V) (y : Y.obj.obj V),
      b W (X.obj.map g x) (Y.obj.map g y) = Z.obj.map g (b V x y))
    (V : Cᵒᵖ) (x : X.obj.obj V) (y : Y.obj.obj V) :
    ((tensorLift J b hn).hom.app V).hom
      (((Functor.LaxMonoidal.μ (sheafToPresheaf J AddCommGrpCat.{u}) X Y).app V).hom
        (x ⊗ₜ[ℤ] y)) = b V x y := by
  let a := sheafificationAdjunction J AddCommGrpCat.{u}
  let d := tensorComparison J X Y
  have hd : IsIso d := tensorComparison_isIso J X Y
  have hμ : Functor.LaxMonoidal.μ (sheafToPresheaf J AddCommGrpCat.{u}) X Y =
      a.homEquiv _ _ d := rfl
  have h := a.homEquiv_naturality_right d (tensorLift J b hn)
  rw [← hμ] at h
  dsimp only [tensorLift] at h
  rw [← Category.assoc, IsIso.hom_inv_id, Category.id_comp,
    Equiv.apply_symm_apply] at h
  have hh := congrArg (fun k => k.hom (x ⊗ₜ[ℤ] y)) (congr_app h.symm V)
  change ((tensorLift J b hn).hom.app V).hom
      (((Functor.LaxMonoidal.μ (sheafToPresheaf J AddCommGrpCat.{u}) X Y).app V).hom
        (x ⊗ₜ[ℤ] y)) =
    (TensorProduct.liftAddHom (b V) (by
      intro n x y
      rw [map_zsmul, map_zsmul]
      rfl)) (x ⊗ₜ[ℤ] y) at hh
  exact hh.trans (TensorProduct.liftAddHom_tmul _ _ _ _)

set_option backward.isDefEq.respectTransparency false in
private lemma unit_ext {Z : Sheaf J AddCommGrpCat.{u}}
    {a b : 𝟙_ (Sheaf J AddCommGrpCat.{u}) ⟶ Z}
    (h : ∀ V : Cᵒᵖ, (a.hom.app V).hom
        (((Functor.LaxMonoidal.ε (sheafToPresheaf J AddCommGrpCat.{u})).app V).hom
          (ULift.up 1)) =
      (b.hom.app V).hom
        (((Functor.LaxMonoidal.ε (sheafToPresheaf J AddCommGrpCat.{u})).app V).hom
          (ULift.up 1))) : a = b := by
  apply Sheaf.unit_hom_ext
  ext V n
  obtain ⟨n⟩ := n
  have hn : (ULift.up n : ULift.{u} ℤ) = n • (ULift.up 1 : ULift.{u} ℤ) := by
    apply ULift.ext
    simp
  change (a.hom.app V).hom
      (((Functor.LaxMonoidal.ε (sheafToPresheaf J AddCommGrpCat.{u})).app V).hom
        (ULift.up n)) =
    (b.hom.app V).hom
      (((Functor.LaxMonoidal.ε (sheafToPresheaf J AddCommGrpCat.{u})).app V).hom
        (ULift.up n))
  rw [hn, map_zsmul, map_zsmul, map_zsmul, h V]

private def unitLift {Z : Sheaf J AddCommGrpCat.{u}}
    (z : ∀ V : Cᵒᵖ, Z.obj.obj V)
    (hn : ∀ {V W : Cᵒᵖ} (g : V ⟶ W), Z.obj.map g (z V) = z W) :
    𝟙_ (Sheaf J AddCommGrpCat.{u}) ⟶ Z := by
  let t : 𝟙_ (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ⟶ Z.obj :=
    { app := fun V ↦ AddCommGrpCat.ofHom
        { toFun := fun n ↦ n.down • z V
          map_zero' := zero_zsmul _
          map_add' := fun n m ↦ add_zsmul _ _ _ }
      naturality := by
        intro V W g
        ext n
        change n.down • z W = (Z.obj.map g).hom (n.down • z V)
        rw [map_zsmul, hn] }
  let a := sheafificationAdjunction J AddCommGrpCat.{u}
  exact Functor.LaxMonoidal.ε (presheafToSheaf J AddCommGrpCat.{u}) ≫
    (a.homEquiv _ _).symm t

private lemma unitLift_spec {Z : Sheaf J AddCommGrpCat.{u}}
    (z : ∀ V : Cᵒᵖ, Z.obj.obj V)
    (hn : ∀ {V W : Cᵒᵖ} (g : V ⟶ W), Z.obj.map g (z V) = z W)
    (V : Cᵒᵖ) :
    ((unitLift J z hn).hom.app V).hom
      (((Functor.LaxMonoidal.ε (sheafToPresheaf J AddCommGrpCat.{u})).app V).hom
        (ULift.up 1)) = z V := by
  let a := sheafificationAdjunction J AddCommGrpCat.{u}
  have hε : Functor.LaxMonoidal.ε (sheafToPresheaf J AddCommGrpCat.{u}) =
      a.homEquiv _ _ (Functor.OplaxMonoidal.η (presheafToSheaf J AddCommGrpCat.{u})) := rfl
  have h := a.homEquiv_naturality_right
    (Functor.OplaxMonoidal.η (presheafToSheaf J AddCommGrpCat.{u})) (unitLift J z hn)
  rw [← hε] at h
  dsimp only [unitLift] at h
  rw [← Category.assoc, Functor.Monoidal.η_ε, Category.id_comp,
    Equiv.apply_symm_apply] at h
  have hh := congrArg (fun k => k.hom (ULift.up 1)) (congr_app h.symm V)
  change ((unitLift J z hn).hom.app V).hom
    (((Functor.LaxMonoidal.ε (sheafToPresheaf J AddCommGrpCat.{u})).app V).hom
      (ULift.up 1)) = (1 : ℤ) • z V at hh
  simpa only [one_zsmul] using hh

attribute [irreducible] tensorLift unitLift

end TensorUniversal

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [UnivLE.{max uC vC, u}] [UnivLE.{max uD vD, u}]
  [HasSheafify J AddCommGrpCat.{u}] [HasSheafify K AddCommGrpCat.{u}]
  [(J.W (A := AddCommGrpCat.{u})).IsMonoidal]
  [(K.W (A := AddCommGrpCat.{u})).IsMonoidal]

/-- The section of the universal bilinear pairing, using the actual inclusion tensorator.
Source: Stacks 03EK (blueprint: lem-sfb-internal-module-inverse-image-comparison). -/
def tensorSection (X Y : Sheaf J AddCommGrpCat.{u}) (V : Cᵒᵖ)
    (x : X.obj.obj V) (y : Y.obj.obj V) : (X ⊗ Y).obj.obj V :=
  ((Functor.LaxMonoidal.μ (sheafToPresheaf J AddCommGrpCat.{u}) X Y).app V).hom
    (x ⊗ₜ[ℤ] y)

/-- The section 1 of the sheafified constant integers, using the inclusion unit.
Source: Stacks 03EK (blueprint: lem-sfb-internal-module-inverse-image-comparison). -/
def integerOne (V : Cᵒᵖ) : (𝟙_ (Sheaf J AddCommGrpCat.{u})).obj.obj V :=
  ((Functor.LaxMonoidal.ε (sheafToPresheaf J AddCommGrpCat.{u})).app V).hom (ULift.up 1)

omit [UnivLE.{max uC vC, u}] [UnivLE.{max uD vD, u}] in
private lemma tensor_ext3 {X Y Z T : Sheaf J AddCommGrpCat.{u}}
    {a b : (X ⊗ Y) ⊗ Z ⟶ T}
    (h : ∀ (V : Cᵒᵖ) (x : X.obj.obj V) (y : Y.obj.obj V) (z : Z.obj.obj V),
      (a.hom.app V).hom
          (tensorSection J (X ⊗ Y) Z V (tensorSection J X Y V x y) z) =
        (b.hom.app V).hom
          (tensorSection J (X ⊗ Y) Z V (tensorSection J X Y V x y) z)) : a = b := by
  let U := sheafToPresheaf J AddCommGrpCat.{u}
  let adj := sheafificationAdjunction J AddCommGrpCat.{u}
  let φ := Functor.OplaxMonoidal.δ (presheafToSheaf J AddCommGrpCat.{u}) X.obj Y.obj ≫
    (adj.counit.app X ⊗ₘ adj.counit.app Y)
  have : IsIso φ := tensorComparison_isIso J X Y
  have hμ : J.W (Functor.LaxMonoidal.μ U X Y) := by
    change J.W (adj.homEquiv _ _ φ)
    rw [Adjunction.homEquiv_unit]
    exact J.W.comp_mem _ _ (J.W_adj_unit_app adj _) (J.W.of_isIso _)
  apply Sheaf.tensor_hom_ext
  apply ((J.W.whiskerRight_mem _ hμ Z.obj) T.obj T.property).injective
  apply NatTrans.ext
  funext V
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.toIntLinearMap_injective
  apply TensorProduct.ext_threefold
  exact h V

omit [UnivLE.{max uC vC, u}] [UnivLE.{max uD vD, u}] in
set_option backward.isDefEq.respectTransparency false in
private lemma tensorSection_associator (X Y Z : Sheaf J AddCommGrpCat.{u})
    (V : Cᵒᵖ) (x : X.obj.obj V) (y : Y.obj.obj V) (z : Z.obj.obj V) :
    (((α_ X Y Z).hom).hom.app V).hom
        (tensorSection J (X ⊗ Y) Z V (tensorSection J X Y V x y) z) =
      tensorSection J X (Y ⊗ Z) V x (tensorSection J Y Z V y z) := by
  let U := sheafToPresheaf J AddCommGrpCat.{u}
  have h := congrArg (fun k => k.hom ((x ⊗ₜ[ℤ] y) ⊗ₜ[ℤ] z))
    (congr_app (Functor.LaxMonoidal.associativity U X Y Z) V)
  change (((α_ X Y Z).hom).hom.app V).hom
      (((Functor.LaxMonoidal.μ U (X ⊗ Y) Z).app V).hom
        ((((Functor.LaxMonoidal.μ U X Y).app V) ▷ Z.obj.obj V).hom
          ((x ⊗ₜ[ℤ] y) ⊗ₜ[ℤ] z))) =
    ((Functor.LaxMonoidal.μ U X (Y ⊗ Z)).app V).hom
      (((X.obj.obj V) ◁ (Functor.LaxMonoidal.μ U Y Z).app V).hom
        (((α_ (X.obj.obj V) (Y.obj.obj V) (Z.obj.obj V)).hom).hom
          ((x ⊗ₜ[ℤ] y) ⊗ₜ[ℤ] z))) at h
  rw [AddCommGrpCat.MonoidalCategory.whiskerRight_tmul,
    AddCommGrpCat.MonoidalCategory.associator_hom_tmul,
    AddCommGrpCat.MonoidalCategory.whiskerLeft_tmul] at h
  exact h

omit [UnivLE.{max uC vC, u}] [UnivLE.{max uD vD, u}] in
set_option backward.isDefEq.respectTransparency false in
private lemma tensorSection_leftUnitor (X : Sheaf J AddCommGrpCat.{u})
    (V : Cᵒᵖ) (x : X.obj.obj V) :
    (((λ_ X).hom).hom.app V).hom
        (tensorSection J (𝟙_ _) X V (integerOne J V) x) = x := by
  let U := sheafToPresheaf J AddCommGrpCat.{u}
  have h := congrArg (fun k => k.hom (ULift.up 1 ⊗ₜ[ℤ] x))
    (congr_app (Functor.LaxMonoidal.left_unitality U X) V).symm
  change (((λ_ X).hom).hom.app V).hom
      (((Functor.LaxMonoidal.μ U (𝟙_ _) X).app V).hom
        (((Functor.LaxMonoidal.ε U).app V ▷ X.obj.obj V).hom (ULift.up 1 ⊗ₜ[ℤ] x))) =
    ((λ_ (X.obj.obj V)).hom).hom (ULift.up 1 ⊗ₜ[ℤ] x) at h
  rw [AddCommGrpCat.MonoidalCategory.whiskerRight_tmul,
    AddCommGrpCat.MonoidalCategory.leftUnitor_hom_tmul] at h
  simpa only [U, tensorSection, integerOne, one_zsmul] using h

omit [UnivLE.{max uC vC, u}] [UnivLE.{max uD vD, u}] in
private lemma tensorSection_braiding (X Y : Sheaf J AddCommGrpCat.{u})
    (V : Cᵒᵖ) (x : X.obj.obj V) (y : Y.obj.obj V) :
    (((β_ X Y).hom).hom.app V).hom (tensorSection J X Y V x y) =
      tensorSection J Y X V y x := by
  have h := congr_app (Functor.LaxBraided.braided
    (F := sheafToPresheaf J AddCommGrpCat.{u}) X Y) V
  exact congrArg (fun k => k.hom (x ⊗ₜ[ℤ] y)) h

omit [UnivLE.{max uD vD, u}] in
private lemma unit_tensor_ext {X Y : Sheaf J AddCommGrpCat.{u}}
    {a b : 𝟙_ (Sheaf J AddCommGrpCat.{u}) ⊗ X ⟶ Y}
    (h : ∀ (V : Cᵒᵖ) (x : X.obj.obj V),
      (a.hom.app V).hom (tensorSection J _ X V (integerOne J V) x) =
        (b.hom.app V).hom (tensorSection J _ X V (integerOne J V) x)) : a = b := by
  apply (cancel_epi (λ_ X).inv).mp
  ext V x
  have hs := congrArg (fun z ↦ (((λ_ X).inv).hom.app V).hom z)
    (tensorSection_leftUnitor J X V x)
  have hi (z : (𝟙_ (Sheaf J AddCommGrpCat.{u}) ⊗ X).obj.obj V) :
      (((λ_ X).inv).hom.app V).hom ((((λ_ X).hom).hom.app V).hom z) = z :=
    congrArg (fun k ↦ (k.hom.app V).hom z) (λ_ X).hom_inv_id
  rw [hi] at hs
  change (a.hom.app V).hom ((((λ_ X).inv).hom.app V).hom x) =
    (b.hom.app V).hom ((((λ_ X).inv).hom.app V).hom x)
  rw [← hs]
  exact h V x

/-- Tensor and unit normalization for a finite-product algebraic lift. The graph
conditions quantify over every test sheaf, so the product and terminal test objects
recover exactly the universal-pairing and constant-1 formulas.
Source: Stacks 03EL and 00YV
(blueprint: lem-sfb-internal-module-inverse-image-comparison). -/
def TensorNormalization (L : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    (A : AbelianInverseImagePresentation L) (q : A.functor.LaxMonoidal) : Prop :=
  letI := q
  (∀ (X Y : Sheaf J AddCommGrpCat.{u}) (T : Sheaf J (Type u))
    (a : T ⟶ (sheafCompose J (forget AddCommGrpCat.{u})).obj X)
    (b : T ⟶ (sheafCompose J (forget AddCommGrpCat.{u})).obj Y)
    (t : T ⟶ (sheafCompose J (forget AddCommGrpCat.{u})).obj (X ⊗ Y)),
    (∀ (U : Cᵒᵖ) (x : T.obj.obj U),
      t.hom.app U x = tensorSection J X Y U (a.hom.app U x) (b.hom.app U x)) →
    ∀ (V : Dᵒᵖ) (x : (L.obj T).obj.obj V),
      (A.underlying.inv.app (X ⊗ Y)).hom.app V ((L.map t).hom.app V x) =
        ((Functor.LaxMonoidal.μ A.functor X Y).hom.app V).hom
          (tensorSection K (A.functor.obj X) (A.functor.obj Y) V
            ((A.underlying.inv.app X).hom.app V ((L.map a).hom.app V x))
            ((A.underlying.inv.app Y).hom.app V ((L.map b).hom.app V x)))) ∧
  (∀ (T : Sheaf J (Type u))
    (a : T ⟶ (sheafCompose J (forget AddCommGrpCat.{u})).obj
      (𝟙_ (Sheaf J AddCommGrpCat.{u}))),
    (∀ (U : Cᵒᵖ) (x : T.obj.obj U), a.hom.app U x = integerOne J U) →
    ∀ (V : Dᵒᵖ) (x : (L.obj T).obj.obj V),
      (A.underlying.inv.app (𝟙_ (Sheaf J AddCommGrpCat.{u}))).hom.app V
          ((L.map a).hom.app V x) =
        ((Functor.LaxMonoidal.ε A.functor).hom.app V).hom (integerOne K V))

-- Generalized sections let us compare the actual sheafified tensor pairings.
private abbrev sets (X : Sheaf J AddCommGrpCat.{u}) : Sheaf J (Type u) :=
  (sheafCompose J (forget AddCommGrpCat.{u})).obj X

private def addGraph (X : Sheaf J AddCommGrpCat.{u}) : sets J X ⊗ sets J X ⟶ sets J X :=
  ⟨{ app := fun V => ↾fun x => @id (X.obj.obj V) x.1 + @id (X.obj.obj V) x.2
     naturality := by
       intro V W g
       ext x
       exact ((X.obj.map g).hom.map_add x.1 x.2).symm }⟩

private def pairingGraph (X Y : Sheaf J AddCommGrpCat.{u}) :
    sets J X ⊗ sets J Y ⟶ sets J (X ⊗ Y) :=
  ⟨{ app := fun V => ↾fun x => tensorSection J X Y V x.1 x.2
     naturality := by
       intro V W g
       ext x
       let a : X.obj.obj V := x.1
       let b : Y.obj.obj V := x.2
       have h := congrArg (fun k => k.hom (a ⊗ₜ[ℤ] b))
         ((Functor.LaxMonoidal.μ (sheafToPresheaf J AddCommGrpCat.{u}) X Y).naturality g)
       change ((Functor.LaxMonoidal.μ (sheafToPresheaf J AddCommGrpCat.{u}) X Y).app W).hom
         ((X.obj.map g ⊗ₘ Y.obj.map g).hom (a ⊗ₜ[ℤ] b)) = _ at h
       rw [AddCommGrpCat.MonoidalCategory.tensorHom_tmul] at h
       exact h }⟩

private def oneGraph : 𝟙_ (Sheaf J (Type u)) ⟶
    sets J (𝟙_ (Sheaf J AddCommGrpCat.{u})) :=
  ⟨{ app := fun V => ↾fun _ => integerOne J V
     naturality := by
       intro V W g
       ext x
       have h := congrArg (fun k => k.hom (ULift.up 1))
         ((Functor.LaxMonoidal.ε (sheafToPresheaf J AddCommGrpCat.{u})).naturality g)
       exact h }⟩

private def pairSource (L : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    [PreservesFiniteProducts L] (X Y : Sheaf J (Type u)) (V : Dᵒᵖ)
    (x : (L.obj X).obj.obj V) (y : (L.obj Y).obj.obj V) :
    (L.obj (X ⊗ Y)).obj.obj V :=
  (inv (CartesianMonoidalCategory.prodComparison L X Y)).hom.app V (x, y)

omit [UnivLE.{max uC vC, u}] [UnivLE.{max uD vD, u}]
  [HasSheafify J AddCommGrpCat.{u}] [HasSheafify K AddCommGrpCat.{u}]
  [(J.W (A := AddCommGrpCat.{u})).IsMonoidal]
  [(K.W (A := AddCommGrpCat.{u})).IsMonoidal] in
private lemma pairSource_fst (L : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    [PreservesFiniteProducts L] (X Y : Sheaf J (Type u)) (V : Dᵒᵖ)
    (x : (L.obj X).obj.obj V) (y : (L.obj Y).obj.obj V) :
    (L.map (CartesianMonoidalCategory.fst X Y)).hom.app V
      (pairSource J K L X Y V x y) = x := by
  have h := CartesianMonoidalCategory.inv_prodComparison_map_fst L X Y
  exact congrArg (fun k => k.hom.app V (x, y)) h

omit [UnivLE.{max uC vC, u}] [UnivLE.{max uD vD, u}]
  [HasSheafify J AddCommGrpCat.{u}] [HasSheafify K AddCommGrpCat.{u}]
  [(J.W (A := AddCommGrpCat.{u})).IsMonoidal]
  [(K.W (A := AddCommGrpCat.{u})).IsMonoidal] in
private lemma pairSource_snd (L : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    [PreservesFiniteProducts L] (X Y : Sheaf J (Type u)) (V : Dᵒᵖ)
    (x : (L.obj X).obj.obj V) (y : (L.obj Y).obj.obj V) :
    (L.map (CartesianMonoidalCategory.snd X Y)).hom.app V
      (pairSource J K L X Y V x y) = y := by
  have h := CartesianMonoidalCategory.inv_prodComparison_map_snd L X Y
  exact congrArg (fun k => k.hom.app V (x, y)) h

omit [UnivLE.{max uC vC, u}] [UnivLE.{max uD vD, u}]
  [HasSheafify J AddCommGrpCat.{u}] [HasSheafify K AddCommGrpCat.{u}]
  [(J.W (A := AddCommGrpCat.{u})).IsMonoidal]
  [(K.W (A := AddCommGrpCat.{u})).IsMonoidal] in
private lemma underlying_hom_inv (L : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    (A : AbelianInverseImagePresentation L) (X : Sheaf J AddCommGrpCat.{u})
    (V : Dᵒᵖ) (x : (A.functor.obj X).obj.obj V) :
    (A.underlying.inv.app X).hom.app V ((A.underlying.hom.app X).hom.app V x) = x :=
  congrArg (fun k => k.hom.app V x) (A.underlying.hom_inv_id_app X)

omit [UnivLE.{max uD vD, u}]
  [HasSheafify J AddCommGrpCat.{u}] [HasSheafify K AddCommGrpCat.{u}]
  [(J.W (A := AddCommGrpCat.{u})).IsMonoidal]
  [(K.W (A := AddCommGrpCat.{u})).IsMonoidal] in
private lemma underlying_inv_hom (L : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    (A : AbelianInverseImagePresentation L) (X : Sheaf J AddCommGrpCat.{u})
    (V : Dᵒᵖ) (x : (L.obj (sets J X)).obj.obj V) :
    (A.underlying.hom.app X).hom.app V ((A.underlying.inv.app X).hom.app V x) = x :=
  congrArg (fun k => k.hom.app V x) (A.underlying.inv_hom_id_app X)

private abbrev abelianPair (L : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    [PreservesFiniteProducts L] (A : AbelianInverseImagePresentation L)
    (X Y : Sheaf J AddCommGrpCat.{u}) (V : Dᵒᵖ)
    (r : (A.functor.obj X).obj.obj V) (s : (A.functor.obj Y).obj.obj V) :=
  pairSource J K L (sets J X) (sets J Y) V
    ((A.underlying.hom.app X).hom.app V r) ((A.underlying.hom.app Y).hom.app V s)

omit [UnivLE.{max uD vD, u}]
  [HasSheafify J AddCommGrpCat.{u}] [HasSheafify K AddCommGrpCat.{u}]
  [(J.W (A := AddCommGrpCat.{u})).IsMonoidal]
  [(K.W (A := AddCommGrpCat.{u})).IsMonoidal] in
private lemma abelianPair_add (L : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    [PreservesFiniteProducts L] (A : AbelianInverseImagePresentation L)
    (X : Sheaf J AddCommGrpCat.{u}) (V : Dᵒᵖ)
    (r s : (A.functor.obj X).obj.obj V) :
    (A.underlying.hom.app X).hom.app V (r + s) =
      (L.map (addGraph J X)).hom.app V (abelianPair J K L A X X V r s) := by
  have h := A.map_add X (sets J X ⊗ sets J X)
    (CartesianMonoidalCategory.fst _ _) (CartesianMonoidalCategory.snd _ _)
    (addGraph J X) (fun _ _ => rfl) V (abelianPair J K L A X X V r s)
  simp only [abelianPair, pairSource_fst, pairSource_snd, underlying_hom_inv] at h
  simp only [id_eq] at h
  have hh := congrArg (fun x => (A.underlying.hom.app X).hom.app V x) h
  simpa only [underlying_inv_hom, abelianPair] using hh.symm


omit [UnivLE.{max uD vD, u}] in
private lemma normalization_unique (L : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    [PreservesFiniteProducts L] (A : AbelianInverseImagePresentation L)
    (q q' : A.functor.LaxMonoidal)
    (hq : TensorNormalization J K L A q) (hq' : TensorNormalization J K L A q') :
    q = q' := by
  apply Functor.LaxMonoidal.ext
  · apply unit_ext K
    intro V
    let x := (inv (CartesianMonoidalCategory.terminalComparison L)).hom.app V PUnit.unit
    exact (hq.2 _ (oneGraph J) (fun _ _ ↦ rfl) V x).symm.trans
      (hq'.2 _ (oneGraph J) (fun _ _ ↦ rfl) V x)
  · funext X Y
    apply tensor_ext K
    intro V x y
    let z := abelianPair J K L A X Y V x y
    have h := hq.1 X Y (sets J X ⊗ sets J Y)
      (CartesianMonoidalCategory.fst _ _) (CartesianMonoidalCategory.snd _ _)
      (pairingGraph J X Y) (fun _ _ ↦ rfl) V z
    have h' := hq'.1 X Y (sets J X ⊗ sets J Y)
      (CartesianMonoidalCategory.fst _ _) (CartesianMonoidalCategory.snd _ _)
      (pairingGraph J X Y) (fun _ _ ↦ rfl) V z
    dsimp only [z, abelianPair] at h h'
    simp only [pairSource_fst, pairSource_snd, underlying_hom_inv] at h h'
    exact h.symm.trans h'

section TransportPairing

variable (L : Sheaf J (Type u) ⥤ Sheaf K (Type u))
  [PreservesFiniteProducts L] (A : AbelianInverseImagePresentation L)

private def transportedPairing (X Y : Sheaf J AddCommGrpCat.{u}) :
    sets K (A.functor.obj X) ⊗ sets K (A.functor.obj Y) ⟶
      sets K (A.functor.obj (X ⊗ Y)) :=
  (A.underlying.hom.app X ⊗ₘ A.underlying.hom.app Y) ≫
    inv (CartesianMonoidalCategory.prodComparison L (sets J X) (sets J Y)) ≫
      L.map (pairingGraph J X Y) ≫ A.underlying.inv.app (X ⊗ Y)

private def transportedPairingSection (X Y : Sheaf J AddCommGrpCat.{u}) (V : Dᵒᵖ)
    (x : (A.functor.obj X).obj.obj V) (y : (A.functor.obj Y).obj.obj V) :
    (A.functor.obj (X ⊗ Y)).obj.obj V :=
  (transportedPairing J K L A X Y).hom.app V (x, y)

omit [UnivLE.{max uD vD, u}]
  [HasSheafify K AddCommGrpCat.{u}] [(K.W (A := AddCommGrpCat.{u})).IsMonoidal] in
private lemma pairingGraph_lift (X Y : Sheaf J AddCommGrpCat.{u})
    (T : Sheaf J (Type u)) (a : T ⟶ sets J X) (b : T ⟶ sets J Y)
    (V : Cᵒᵖ) (x : T.obj.obj V) :
    (CartesianMonoidalCategory.lift a b ≫ pairingGraph J X Y).hom.app V x =
      tensorSection J X Y V (a.hom.app V x) (b.hom.app V x) := rfl

omit [HasSheafify K AddCommGrpCat.{u}] [(K.W (A := AddCommGrpCat.{u})).IsMonoidal] in
private lemma transportedPairing_graph (X Y : Sheaf J AddCommGrpCat.{u})
    (T : Sheaf J (Type u)) (a : T ⟶ sets J X) (b : T ⟶ sets J Y)
    (t : T ⟶ sets J (X ⊗ Y))
    (ht : ∀ (U : Cᵒᵖ) (x : T.obj.obj U),
      t.hom.app U x = tensorSection J X Y U (a.hom.app U x) (b.hom.app U x))
    (V : Dᵒᵖ) (x : (L.obj T).obj.obj V) :
    (A.underlying.inv.app (X ⊗ Y)).hom.app V ((L.map t).hom.app V x) =
      (transportedPairing J K L A X Y).hom.app V
        ((A.underlying.inv.app X).hom.app V ((L.map a).hom.app V x),
          (A.underlying.inv.app Y).hom.app V ((L.map b).hom.app V x)) := by
  have he : t = CartesianMonoidalCategory.lift a b ≫ pairingGraph J X Y := by
    ext U z
    exact ht U z
  have hp : L.map (CartesianMonoidalCategory.lift a b) ≫
      CartesianMonoidalCategory.prodComparison L (sets J X) (sets J Y) =
        CartesianMonoidalCategory.lift (L.map a) (L.map b) := by
    apply CartesianMonoidalCategory.hom_ext <;>
      simp [CartesianMonoidalCategory.prodComparison, ← L.map_comp]
  have hp' : L.map (CartesianMonoidalCategory.lift a b) =
      CartesianMonoidalCategory.lift (L.map a) (L.map b) ≫
        inv (CartesianMonoidalCategory.prodComparison L (sets J X) (sets J Y)) :=
    (IsIso.eq_comp_inv _).mpr hp
  rw [he, L.map_comp]
  change (A.underlying.inv.app (X ⊗ Y)).hom.app V
    ((L.map (pairingGraph J X Y)).hom.app V
      ((L.map (CartesianMonoidalCategory.lift a b)).hom.app V x)) = _
  rw [hp']
  dsimp only [transportedPairing]
  change _ = (A.underlying.inv.app (X ⊗ Y)).hom.app V
    ((L.map (pairingGraph J X Y)).hom.app V
      ((inv (CartesianMonoidalCategory.prodComparison L (sets J X) (sets J Y))).hom.app V
        ((A.underlying.hom.app X).hom.app V
            ((A.underlying.inv.app X).hom.app V ((L.map a).hom.app V x)),
          (A.underlying.hom.app Y).hom.app V
            ((A.underlying.inv.app Y).hom.app V ((L.map b).hom.app V x)))))
  rw [underlying_inv_hom, underlying_inv_hom]
  rfl

omit [UnivLE.{max uD vD, u}]
  [HasSheafify J AddCommGrpCat.{u}] [HasSheafify K AddCommGrpCat.{u}]
  [(J.W (A := AddCommGrpCat.{u})).IsMonoidal]
  [(K.W (A := AddCommGrpCat.{u})).IsMonoidal] [PreservesFiniteProducts L] in
private lemma transported_map {X Y : Sheaf J AddCommGrpCat.{u}} (g : X ⟶ Y)
    (T : Sheaf J (Type u)) (a : T ⟶ sets J X)
    (b : T ⟶ sets J Y)
    (hb : ∀ (U : Cᵒᵖ) (x : T.obj.obj U),
      b.hom.app U x = (g.hom.app U).hom (a.hom.app U x))
    (V : Dᵒᵖ) (x : (L.obj T).obj.obj V) :
    (A.underlying.inv.app Y).hom.app V ((L.map b).hom.app V x) =
      ((A.functor.map g).hom.app V).hom
        ((A.underlying.inv.app X).hom.app V ((L.map a).hom.app V x)) := by
  have he : b = a ≫ (sheafCompose J (forget AddCommGrpCat.{u})).map g := by
    ext U z
    exact hb U z
  rw [he, L.map_comp]
  exact congrArg (fun m ↦ m.hom.app V ((L.map a).hom.app V x))
    (A.underlying.inv.naturality g)

omit [HasSheafify K AddCommGrpCat.{u}] [(K.W (A := AddCommGrpCat.{u})).IsMonoidal] in
private lemma transportedPairing_braided (X Y : Sheaf J AddCommGrpCat.{u})
    (V : Dᵒᵖ) (r : (A.functor.obj X).obj.obj V) (s : (A.functor.obj Y).obj.obj V) :
    ((A.functor.map (β_ X Y).hom).hom.app V).hom
        (transportedPairingSection J K L A X Y V r s) =
      transportedPairingSection J K L A Y X V s r := by
  let T := sets J X ⊗ sets J Y
  let a : T ⟶ sets J X := CartesianMonoidalCategory.fst _ _
  let b : T ⟶ sets J Y := CartesianMonoidalCategory.snd _ _
  let p : T ⟶ sets J (X ⊗ Y) :=
    CartesianMonoidalCategory.lift a b ≫ pairingGraph J X Y
  let p' : T ⟶ sets J (Y ⊗ X) := CartesianMonoidalCategory.lift b a ≫ pairingGraph J Y X
  let w := abelianPair J K L A X Y V r s
  have hp := transportedPairing_graph J K L A X Y T a b p (pairingGraph_lift J _ _ T _ _) V w
  have hp' := transportedPairing_graph J K L A Y X T b a p' (pairingGraph_lift J _ _ T _ _) V w
  have ha : (A.underlying.inv.app X).hom.app V ((L.map a).hom.app V w) = r := by
    change (A.underlying.inv.app X).hom.app V
      ((L.map (CartesianMonoidalCategory.fst _ _)).hom.app V
        (abelianPair J K L A X Y V r s)) = r
    rw [pairSource_fst, underlying_hom_inv]
  have hb : (A.underlying.inv.app Y).hom.app V ((L.map b).hom.app V w) = s := by
    change (A.underlying.inv.app Y).hom.app V
      ((L.map (CartesianMonoidalCategory.snd _ _)).hom.app V
        (abelianPair J K L A X Y V r s)) = s
    rw [pairSource_snd, underlying_hom_inv]
  rw [ha, hb] at hp hp'
  have h := transported_map J K L A (β_ X Y).hom T p p'
    (by
      intro U x
      exact (tensorSection_braiding J X Y U x.1 x.2).symm) V w
  rw [hp, hp'] at h
  exact h.symm

omit [HasSheafify K AddCommGrpCat.{u}] [(K.W (A := AddCommGrpCat.{u})).IsMonoidal] in
set_option backward.isDefEq.respectTransparency true in
private lemma transportedPairing_add_left (X Y : Sheaf J AddCommGrpCat.{u})
    (V : Dᵒᵖ) (r s : (A.functor.obj X).obj.obj V) (t : (A.functor.obj Y).obj.obj V) :
    transportedPairingSection J K L A X Y V (r + s) (t) =
      @id ((A.functor.obj (X ⊗ Y)).obj.obj V)
        (transportedPairingSection J K L A X Y V (r) (t)) +
        @id ((A.functor.obj (X ⊗ Y)).obj.obj V)
          (transportedPairingSection J K L A X Y V (s) (t)) := by
  let T := (sets J X ⊗ sets J X) ⊗ sets J Y
  let a : T ⟶ sets J X := CartesianMonoidalCategory.fst _ _ ≫
    CartesianMonoidalCategory.fst _ _
  let b : T ⟶ sets J X := CartesianMonoidalCategory.fst _ _ ≫
    CartesianMonoidalCategory.snd _ _
  let c : T ⟶ sets J Y := CartesianMonoidalCategory.snd _ _
  let ab : T ⟶ sets J X := CartesianMonoidalCategory.fst _ _ ≫ addGraph J X
  let p : T ⟶ sets J (X ⊗ Y) := CartesianMonoidalCategory.lift a c ≫ pairingGraph J X Y
  let p' : T ⟶ sets J (X ⊗ Y) := CartesianMonoidalCategory.lift b c ≫ pairingGraph J X Y
  let pp : T ⟶ sets J (X ⊗ Y) := CartesianMonoidalCategory.lift ab c ≫ pairingGraph J X Y
  let w := pairSource J K L (sets J X ⊗ sets J X) (sets J Y) V
    (abelianPair J K L A X X V r s) ((A.underlying.hom.app Y).hom.app V t)
  have ha : (A.underlying.inv.app X).hom.app V ((L.map a).hom.app V w) = r := by
    dsimp only [a]
    rw [L.map_comp]
    change (A.underlying.inv.app X).hom.app V
      ((L.map (CartesianMonoidalCategory.fst _ _)).hom.app V
        ((L.map (CartesianMonoidalCategory.fst _ _)).hom.app V w)) = _
    dsimp only [w]
    erw [pairSource_fst]
    dsimp only [abelianPair]
    rw [pairSource_fst, underlying_hom_inv]
  have hb : (A.underlying.inv.app X).hom.app V ((L.map b).hom.app V w) = s := by
    dsimp only [b]
    rw [L.map_comp]
    change (A.underlying.inv.app X).hom.app V
      ((L.map (CartesianMonoidalCategory.snd _ _)).hom.app V
        ((L.map (CartesianMonoidalCategory.fst _ _)).hom.app V w)) = _
    dsimp only [w]
    erw [pairSource_fst]
    dsimp only [abelianPair]
    rw [pairSource_snd, underlying_hom_inv]
  have hc : (A.underlying.inv.app Y).hom.app V ((L.map c).hom.app V w) = t := by
    dsimp only [c, w]
    rw [pairSource_snd, underlying_hom_inv]
  have hab := A.map_add X T a b ab (fun _ _ ↦ rfl) V w
  rw [ha, hb] at hab
  have hp := transportedPairing_graph J K L A X Y T a c p (pairingGraph_lift J _ _ T _ _) V w
  have hp' := transportedPairing_graph J K L A X Y T b c p' (pairingGraph_lift J _ _ T _ _) V w
  have hpp := transportedPairing_graph J K L A X Y T ab c pp (pairingGraph_lift J _ _ T _ _) V w
  rw [ha, hc] at hp
  rw [hb, hc] at hp'
  rw [hab, hc] at hpp
  have h := A.map_add (X ⊗ Y) T p p' pp (by
    intro U x
    change tensorSection J X Y U
        (@id (X.obj.obj U) x.1.1 + @id (X.obj.obj U) x.1.2) x.2 =
      tensorSection J X Y U x.1.1 x.2 + tensorSection J X Y U x.1.2 x.2
    set_option backward.isDefEq.respectTransparency false in
      simp only [tensorSection, TensorProduct.add_tmul, map_add, id_eq]) V w
  rw [hp, hp', hpp] at h
  exact h

omit [HasSheafify K AddCommGrpCat.{u}] [(K.W (A := AddCommGrpCat.{u})).IsMonoidal] in
set_option backward.isDefEq.respectTransparency true in
private lemma transportedPairing_add_right (X Y : Sheaf J AddCommGrpCat.{u})
    (V : Dᵒᵖ) (r : (A.functor.obj X).obj.obj V) (s t : (A.functor.obj Y).obj.obj V) :
    transportedPairingSection J K L A X Y V (r) (s + t) =
      @id ((A.functor.obj (X ⊗ Y)).obj.obj V)
        (transportedPairingSection J K L A X Y V (r) (s)) +
        @id ((A.functor.obj (X ⊗ Y)).obj.obj V)
          (transportedPairingSection J K L A X Y V (r) (t)) := by
  apply (ConcreteCategory.bijective_of_isIso
    ((A.functor.map (β_ X Y).hom).hom.app V)).1
  simp only [id_eq]
  rw [map_add, transportedPairing_braided, transportedPairing_braided,
    transportedPairing_braided]
  exact transportedPairing_add_left J K L A Y X V s t r

private def transportedBilinear (X Y : Sheaf J AddCommGrpCat.{u}) (V : Dᵒᵖ) :
    (A.functor.obj X).obj.obj V →+
      (A.functor.obj Y).obj.obj V →+ (A.functor.obj (X ⊗ Y)).obj.obj V where
  toFun r :=
    { toFun := fun s ↦ transportedPairingSection J K L A X Y V (r) (s)
      map_zero' := by
        have h := transportedPairing_add_right J K L A X Y V r 0 0
        simp only [add_zero, id_eq] at h
        exact (add_left_cancel ((add_zero _).trans h)).symm
      map_add' := transportedPairing_add_right J K L A X Y V r }
  map_zero' := by
    ext s
    have h := transportedPairing_add_left J K L A X Y V 0 0 s
    simp only [zero_add, id_eq] at h
    exact (add_left_cancel ((add_zero _).trans h)).symm
  map_add' r s := by
    ext t
    exact transportedPairing_add_left J K L A X Y V r s t

omit [HasSheafify K AddCommGrpCat.{u}] [(K.W (A := AddCommGrpCat.{u})).IsMonoidal] in
private lemma transportedBilinear_natural (X Y : Sheaf J AddCommGrpCat.{u})
    {V W : Dᵒᵖ} (g : V ⟶ W)
    (x : (A.functor.obj X).obj.obj V) (y : (A.functor.obj Y).obj.obj V) :
    transportedBilinear J K L A X Y W
        ((A.functor.obj X).obj.map g x) ((A.functor.obj Y).obj.map g y) =
      (A.functor.obj (X ⊗ Y)).obj.map g (transportedBilinear J K L A X Y V x y) :=
  congrArg (fun k ↦ k (x, y)) ((transportedPairing J K L A X Y).hom.naturality g)

private def transportedTensor (X Y : Sheaf J AddCommGrpCat.{u}) :
    A.functor.obj X ⊗ A.functor.obj Y ⟶ A.functor.obj (X ⊗ Y) :=
  tensorLift K (transportedBilinear J K L A X Y)
    (transportedBilinear_natural J K L A X Y)

private lemma transportedTensor_spec (X Y : Sheaf J AddCommGrpCat.{u})
    (V : Dᵒᵖ) (x : (A.functor.obj X).obj.obj V) (y : (A.functor.obj Y).obj.obj V) :
    ((transportedTensor J K L A X Y).hom.app V).hom
        (tensorSection K (A.functor.obj X) (A.functor.obj Y) V x y) =
      transportedPairingSection J K L A X Y V (x) (y) :=
  tensorLift_spec K (transportedBilinear J K L A X Y)
    (transportedBilinear_natural J K L A X Y) V x y

private def transportedOne :
    𝟙_ (Sheaf K (Type u)) ⟶ sets K (A.functor.obj (𝟙_ (Sheaf J AddCommGrpCat.{u}))) :=
  inv (CartesianMonoidalCategory.terminalComparison L) ≫ L.map (oneGraph J) ≫
    A.underlying.inv.app _

private def transportedUnit :
    𝟙_ (Sheaf K AddCommGrpCat.{u}) ⟶ A.functor.obj (𝟙_ (Sheaf J AddCommGrpCat.{u})) :=
  unitLift K (fun V ↦ (transportedOne J K L A).hom.app V PUnit.unit) (by
    intro V W g
    exact (congrArg (fun k ↦ k PUnit.unit)
      ((transportedOne J K L A).hom.naturality g)).symm)

private lemma transportedUnit_spec (V : Dᵒᵖ) :
    ((transportedUnit J K L A).hom.app V).hom (integerOne K V) =
      (transportedOne J K L A).hom.app V PUnit.unit :=
  unitLift_spec K (fun V ↦ (transportedOne J K L A).hom.app V PUnit.unit) (by
    intro V W g
    exact (congrArg (fun k ↦ k PUnit.unit)
      ((transportedOne J K L A).hom.naturality g)).symm) V

attribute [irreducible] transportedTensor transportedUnit

private lemma transportedUnit_graph
    (T : Sheaf J (Type u)) (a : T ⟶ sets J (𝟙_ (Sheaf J AddCommGrpCat.{u})))
    (ha : ∀ (U : Cᵒᵖ) (x : T.obj.obj U), a.hom.app U x = integerOne J U)
    (V : Dᵒᵖ) (x : (L.obj T).obj.obj V) :
    (A.underlying.inv.app _).hom.app V ((L.map a).hom.app V x) =
      ((transportedUnit J K L A).hom.app V).hom (integerOne K V) := by
  have he : a = CartesianMonoidalCategory.toUnit T ≫ oneGraph J := by
    ext U z
    exact ha U z
  have ht : L.map (CartesianMonoidalCategory.toUnit T) =
      CartesianMonoidalCategory.toUnit (L.obj T) ≫
        inv (CartesianMonoidalCategory.terminalComparison L) := by
    apply (IsIso.eq_comp_inv _).mpr
    exact CartesianMonoidalCategory.map_toUnit_comp_terminalComparison L T
  rw [he, L.map_comp, ht, transportedUnit_spec]
  rfl

omit [UnivLE.{max uC vC, u}] [UnivLE.{max uD vD, u}] in
private lemma tensorSection_natural {X Y X' Y' : Sheaf J AddCommGrpCat.{u}}
    (h : X ⟶ X') (k : Y ⟶ Y') (V : Cᵒᵖ) (x : X.obj.obj V) (y : Y.obj.obj V) :
    ((h ⊗ₘ k).hom.app V).hom (tensorSection J X Y V x y) =
      tensorSection J X' Y' V ((h.hom.app V).hom x) ((k.hom.app V).hom y) := by
  have hn := congr_app (Functor.LaxMonoidal.μ_natural
    (sheafToPresheaf J AddCommGrpCat.{u}) h k) V
  exact congrArg (fun m => m.hom (x ⊗ₜ[ℤ] y)) hn.symm

private lemma transportedTensor_natural
    {X Y X' Y' : Sheaf J AddCommGrpCat.{u}} (h : X ⟶ X') (k : Y ⟶ Y') :
    (A.functor.map h ⊗ₘ A.functor.map k) ≫ transportedTensor J K L A X' Y' =
      transportedTensor J K L A X Y ≫ A.functor.map (h ⊗ₘ k) := by
  apply tensor_ext K
  intro V x y
  change ((transportedTensor J K L A X' Y').hom.app V).hom
      (((A.functor.map h ⊗ₘ A.functor.map k).hom.app V).hom
        (tensorSection K (A.functor.obj X) (A.functor.obj Y) V x y)) =
    ((A.functor.map (h ⊗ₘ k)).hom.app V).hom
      (((transportedTensor J K L A X Y).hom.app V).hom
        (tensorSection K (A.functor.obj X) (A.functor.obj Y) V x y))
  rw [tensorSection_natural, transportedTensor_spec, transportedTensor_spec]
  let U := sheafCompose J (forget AddCommGrpCat.{u})
  let a := CartesianMonoidalCategory.fst (sets J X) (sets J Y) ≫ U.map h
  let b := CartesianMonoidalCategory.snd (sets J X) (sets J Y) ≫ U.map k
  let t := pairingGraph J X Y ≫ U.map (h ⊗ₘ k)
  let z := abelianPair J K L A X Y V x y
  have hp := transportedPairing_graph J K L A X' Y' (sets J X ⊗ sets J Y) a b t
    (by intro W w; exact tensorSection_natural J h k W w.1 w.2) V z
  have hn (P Q : Sheaf J AddCommGrpCat.{u}) (g : P ⟶ Q)
      (w : (L.obj (sets J P)).obj.obj V) :
      (A.underlying.inv.app Q).hom.app V ((L.map (U.map g)).hom.app V w) =
        ((A.functor.map g).hom.app V).hom ((A.underlying.inv.app P).hom.app V w) :=
    congrArg (fun m ↦ m.hom.app V w) (A.underlying.inv.naturality g)
  have ha : (A.underlying.inv.app X').hom.app V ((L.map a).hom.app V z) =
      ((A.functor.map h).hom.app V).hom x := by
    dsimp only [a]
    rw [L.map_comp]
    change (A.underlying.inv.app X').hom.app V
      ((L.map (U.map h)).hom.app V
        ((L.map (CartesianMonoidalCategory.fst _ _)).hom.app V z)) = _
    rw [hn, pairSource_fst, underlying_hom_inv]
  have hb : (A.underlying.inv.app Y').hom.app V ((L.map b).hom.app V z) =
      ((A.functor.map k).hom.app V).hom y := by
    dsimp only [b]
    rw [L.map_comp]
    change (A.underlying.inv.app Y').hom.app V
      ((L.map (U.map k)).hom.app V
        ((L.map (CartesianMonoidalCategory.snd _ _)).hom.app V z)) = _
    rw [hn, pairSource_snd, underlying_hom_inv]
  rw [ha, hb] at hp
  dsimp only [t] at hp
  rw [L.map_comp] at hp
  change (A.underlying.inv.app (X' ⊗ Y')).hom.app V
    ((L.map (U.map (h ⊗ₘ k))).hom.app V
      ((L.map (pairingGraph J X Y)).hom.app V z)) = _ at hp
  rw [hn] at hp
  exact hp.symm

private lemma transportedTensor_associativity (X Y Z : Sheaf J AddCommGrpCat.{u}) :
    (transportedTensor J K L A X Y ⊗ₘ 𝟙 (A.functor.obj Z)) ≫
        transportedTensor J K L A (X ⊗ Y) Z ≫ A.functor.map (α_ X Y Z).hom =
      (α_ (A.functor.obj X) (A.functor.obj Y) (A.functor.obj Z)).hom ≫
        (𝟙 (A.functor.obj X) ⊗ₘ transportedTensor J K L A Y Z) ≫
          transportedTensor J K L A X (Y ⊗ Z) := by
  apply tensor_ext3 K
  intro V r s t
  let T := (sets J X ⊗ sets J Y) ⊗ sets J Z
  let a : T ⟶ sets J X := CartesianMonoidalCategory.fst _ _ ≫
    CartesianMonoidalCategory.fst _ _
  let b : T ⟶ sets J Y := CartesianMonoidalCategory.fst _ _ ≫
    CartesianMonoidalCategory.snd _ _
  let c : T ⟶ sets J Z := CartesianMonoidalCategory.snd _ _
  let ab : T ⟶ sets J (X ⊗ Y) := CartesianMonoidalCategory.lift a b ≫ pairingGraph J X Y
  let bc : T ⟶ sets J (Y ⊗ Z) := CartesianMonoidalCategory.lift b c ≫ pairingGraph J Y Z
  let left : T ⟶ sets J ((X ⊗ Y) ⊗ Z) :=
    CartesianMonoidalCategory.lift ab c ≫ pairingGraph J (X ⊗ Y) Z
  let right : T ⟶ sets J (X ⊗ (Y ⊗ Z)) :=
    CartesianMonoidalCategory.lift a bc ≫ pairingGraph J X (Y ⊗ Z)
  let w := pairSource J K L (sets J X ⊗ sets J Y) (sets J Z) V
    (abelianPair J K L A X Y V r s) ((A.underlying.hom.app Z).hom.app V t)
  have ha : (A.underlying.inv.app X).hom.app V ((L.map a).hom.app V w) = r := by
    dsimp only [a]
    rw [L.map_comp]
    change (A.underlying.inv.app X).hom.app V
      ((L.map (CartesianMonoidalCategory.fst _ _)).hom.app V
        ((L.map (CartesianMonoidalCategory.fst _ _)).hom.app V w)) = _
    dsimp only [w]
    erw [pairSource_fst]
    dsimp only [abelianPair]
    rw [pairSource_fst, underlying_hom_inv]
  have hb : (A.underlying.inv.app Y).hom.app V ((L.map b).hom.app V w) = s := by
    dsimp only [b]
    rw [L.map_comp]
    change (A.underlying.inv.app Y).hom.app V
      ((L.map (CartesianMonoidalCategory.snd _ _)).hom.app V
        ((L.map (CartesianMonoidalCategory.fst _ _)).hom.app V w)) = _
    dsimp only [w]
    erw [pairSource_fst]
    dsimp only [abelianPair]
    rw [pairSource_snd, underlying_hom_inv]
  have hc : (A.underlying.inv.app Z).hom.app V ((L.map c).hom.app V w) = t := by
    dsimp only [c, w]
    rw [pairSource_snd, underlying_hom_inv]
  have hab := transportedPairing_graph J K L A X Y T a b ab (pairingGraph_lift J _ _ T _ _) V w
  have hbc := transportedPairing_graph J K L A Y Z T b c bc (pairingGraph_lift J _ _ T _ _) V w
  rw [ha, hb] at hab
  rw [hb, hc] at hbc
  have hl := transportedPairing_graph J K L A (X ⊗ Y) Z T ab c left
    (pairingGraph_lift J _ _ T _ _) V w
  have hr := transportedPairing_graph J K L A X (Y ⊗ Z) T a bc right
    (pairingGraph_lift J _ _ T _ _) V w
  rw [hab, hc] at hl
  rw [ha, hbc] at hr
  have h := transported_map J K L A (α_ X Y Z).hom T left right
    (by
      intro U x
      exact (tensorSection_associator J X Y Z U x.1.1 x.1.2 x.2).symm) V w
  rw [hl, hr] at h
  change ((A.functor.map (α_ X Y Z).hom).hom.app V).hom
      (((transportedTensor J K L A (X ⊗ Y) Z).hom.app V).hom
        (((transportedTensor J K L A X Y ⊗ₘ 𝟙 _).hom.app V).hom
          (tensorSection K _ _ V (tensorSection K _ _ V r s) t))) =
    ((transportedTensor J K L A X (Y ⊗ Z)).hom.app V).hom
      (((𝟙 _ ⊗ₘ transportedTensor J K L A Y Z).hom.app V).hom
        ((((α_ (A.functor.obj X) (A.functor.obj Y) (A.functor.obj Z)).hom).hom.app V).hom
          (tensorSection K _ _ V (tensorSection K _ _ V r s) t)))
  rw [tensorSection_natural, tensorSection_associator, tensorSection_natural]
  rw [transportedTensor_spec, transportedTensor_spec, transportedTensor_spec,
    transportedTensor_spec]
  exact h.symm

private lemma transportedTensor_left_unitality (X : Sheaf J AddCommGrpCat.{u}) :
    (λ_ (A.functor.obj X)).hom =
      (transportedUnit J K L A ⊗ₘ 𝟙 _) ≫ transportedTensor J K L A (𝟙_ _) X ≫
        A.functor.map (λ_ X).hom := by
  apply unit_tensor_ext K
  intro V r
  let T := sets J X
  let a : T ⟶ sets J (𝟙_ (Sheaf J AddCommGrpCat.{u})) :=
    CartesianMonoidalCategory.toUnit T ≫ oneGraph J
  let b : T ⟶ sets J X := 𝟙 _
  let p : T ⟶ sets J (𝟙_ (Sheaf J AddCommGrpCat.{u}) ⊗ X) :=
    CartesianMonoidalCategory.lift a b ≫ pairingGraph J _ X
  let w := (A.underlying.hom.app X).hom.app V r
  have ha := transportedUnit_graph J K L A T a (fun _ _ ↦ rfl) V w
  have hb : (A.underlying.inv.app X).hom.app V ((L.map b).hom.app V w) = r := by
    dsimp only [b]
    rw [L.map_id]
    exact underlying_hom_inv J K L A X V r
  have hp := transportedPairing_graph J K L A _ X T a b p (pairingGraph_lift J _ _ T _ _) V w
  rw [ha, hb] at hp
  have h := transported_map J K L A (λ_ X).hom T p b
    (by
      intro U x
      exact (tensorSection_leftUnitor J X U x).symm) V w
  rw [hb, hp] at h
  change (((λ_ (A.functor.obj X)).hom).hom.app V).hom
      (tensorSection K _ _ V (integerOne K V) r) =
    ((A.functor.map (λ_ X).hom).hom.app V).hom
      (((transportedTensor J K L A _ X).hom.app V).hom
        (((transportedUnit J K L A ⊗ₘ 𝟙 _).hom.app V).hom
          (tensorSection K _ _ V (integerOne K V) r)))
  rw [tensorSection_leftUnitor, tensorSection_natural]
  change r = ((A.functor.map (λ_ X).hom).hom.app V).hom
    (((transportedTensor J K L A _ X).hom.app V).hom
      (tensorSection K _ _ V
        (((transportedUnit J K L A).hom.app V).hom (integerOne K V)) r))
  rw [transportedTensor_spec]
  exact h

private lemma transportedTensor_braided (X Y : Sheaf J AddCommGrpCat.{u}) :
    transportedTensor J K L A X Y ≫ A.functor.map (β_ X Y).hom =
      (β_ (A.functor.obj X) (A.functor.obj Y)).hom ≫ transportedTensor J K L A Y X := by
  apply tensor_ext K
  intro V r s
  change ((A.functor.map (β_ X Y).hom).hom.app V).hom
      (((transportedTensor J K L A X Y).hom.app V).hom
        (tensorSection K _ _ V r s)) =
    ((transportedTensor J K L A Y X).hom.app V).hom
      ((((β_ (A.functor.obj X) (A.functor.obj Y)).hom).hom.app V).hom (tensorSection K _ _ V r s))
  rw [tensorSection_braiding, transportedTensor_spec, transportedTensor_spec]
  exact transportedPairing_braided J K L A X Y V r s

private lemma transportedTensor_right_unitality (X : Sheaf J AddCommGrpCat.{u}) :
    (ρ_ (A.functor.obj X)).hom =
      (𝟙 _ ⊗ₘ transportedUnit J K L A) ≫ transportedTensor J K L A X (𝟙_ _) ≫
        A.functor.map (ρ_ X).hom := by
  exact right_unit_of_left_and_braiding A.functor (transportedUnit J K L A)
    (transportedTensor J K L A) (transportedTensor_braided J K L A)
    (transportedTensor_left_unitality J K L A) X

@[instance_reducible] private def normalizedLax : A.functor.LaxMonoidal :=
  Functor.LaxMonoidal.ofTensorHom
    (transportedUnit J K L A) (transportedTensor J K L A)
    (transportedTensor_natural J K L A)
    (transportedTensor_associativity J K L A)
    (transportedTensor_left_unitality J K L A)
    (transportedTensor_right_unitality J K L A)

private lemma normalizedLax_spec :
    TensorNormalization J K L A (normalizedLax J K L A) := by
  constructor
  · intro X Y T a b t ht V x
    exact (transportedPairing_graph J K L A X Y T a b t ht V x).trans
      (transportedTensor_spec J K L A X Y V _ _).symm
  · intro T a ha V x
    exact transportedUnit_graph J K L A T a ha V x

private lemma normalizedLax_ε :
    (normalizedLax J K L A).ε = transportedUnit J K L A := rfl

private lemma normalizedLax_μ :
    (normalizedLax J K L A).μ = transportedTensor J K L A := rfl

-- Later proofs use the map equations without unfolding the coherence structure.
attribute [irreducible] normalizedLax

private lemma normalized_tensor_graph (X Y : Sheaf J AddCommGrpCat.{u}) :
    pairingGraph K (A.functor.obj X) (A.functor.obj Y) ≫
        (sheafCompose K (forget AddCommGrpCat.{u})).map (transportedTensor J K L A X Y) =
      (A.underlying.hom.app X ⊗ₘ A.underlying.hom.app Y) ≫
        inv (CartesianMonoidalCategory.prodComparison L (sets J X) (sets J Y)) ≫
          L.map (pairingGraph J X Y) ≫ A.underlying.inv.app (X ⊗ Y) := by
  ext V p
  exact transportedTensor_spec J K L A X Y V p.1 p.2

omit [UnivLE.{max uC vC, u}] [UnivLE.{max uD vD, u}]
  [HasSheafify J AddCommGrpCat.{u}] [HasSheafify K AddCommGrpCat.{u}]
  [(J.W (A := AddCommGrpCat.{u})).IsMonoidal]
  [(K.W (A := AddCommGrpCat.{u})).IsMonoidal] [PreservesFiniteProducts L] in
set_option backward.isDefEq.respectTransparency false in
private lemma underlying_tensor_hom_inv (X Y : Sheaf J AddCommGrpCat.{u}) :
    (A.underlying.hom.app X ⊗ₘ A.underlying.hom.app Y) ≫
        (A.underlying.inv.app X ⊗ₘ A.underlying.inv.app Y) = 𝟙 _ :=
  by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext V
    apply ConcreteCategory.hom_ext
    intro p
    exact Prod.ext (underlying_hom_inv J K L A X V p.1)
      (underlying_hom_inv J K L A Y V p.2)

omit [UnivLE.{max uD vD, u}]
  [HasSheafify J AddCommGrpCat.{u}] [HasSheafify K AddCommGrpCat.{u}]
  [(J.W (A := AddCommGrpCat.{u})).IsMonoidal]
  [(K.W (A := AddCommGrpCat.{u})).IsMonoidal] [PreservesFiniteProducts L] in
set_option backward.isDefEq.respectTransparency false in
private lemma underlying_tensor_inv_hom (X Y : Sheaf J AddCommGrpCat.{u}) :
    (A.underlying.inv.app X ⊗ₘ A.underlying.inv.app Y) ≫
        (A.underlying.hom.app X ⊗ₘ A.underlying.hom.app Y) = 𝟙 _ :=
  by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext V
    apply ConcreteCategory.hom_ext
    intro p
    exact Prod.ext (underlying_inv_hom J K L A X V p.1)
      (underlying_inv_hom J K L A Y V p.2)

omit [UnivLE.{max uD vD, u}] in
private lemma pairingGraph_natural {X Y X' Y' : Sheaf J AddCommGrpCat.{u}}
    (h : X ⟶ X') (k : Y ⟶ Y') :
    pairingGraph J X Y ≫ (sheafCompose J (forget AddCommGrpCat.{u})).map (h ⊗ₘ k) =
      ((sheafCompose J (forget AddCommGrpCat.{u})).map h ⊗ₘ
        (sheafCompose J (forget AddCommGrpCat.{u})).map k) ≫ pairingGraph J X' Y' := by
  ext V p
  exact tensorSection_natural J h k V p.1 p.2

omit [UnivLE.{max uD vD, u}] in
private lemma pairingGraph_ext {X Y Z : Sheaf J AddCommGrpCat.{u}} {a b : X ⊗ Y ⟶ Z}
    (h : pairingGraph J X Y ≫ (sheafCompose J (forget AddCommGrpCat.{u})).map a =
      pairingGraph J X Y ≫ (sheafCompose J (forget AddCommGrpCat.{u})).map b) : a = b := by
  apply tensor_ext J
  intro V x y
  exact congrArg (fun m ↦ m.hom.app V (x, y)) h

attribute [irreducible] transportedPairing transportedBilinear

set_option backward.isDefEq.respectTransparency false in
private lemma tensor_graph_of_normalization (q : A.functor.LaxMonoidal)
    (hq : TensorNormalization J K L A q) (X Y : Sheaf J AddCommGrpCat.{u}) :
    letI := q
    pairingGraph K (A.functor.obj X) (A.functor.obj Y) ≫
        (sheafCompose K (forget AddCommGrpCat.{u})).map
          (Functor.LaxMonoidal.μ A.functor X Y) =
      (A.underlying.hom.app X ⊗ₘ A.underlying.hom.app Y) ≫
        inv (CartesianMonoidalCategory.prodComparison L (sets J X) (sets J Y)) ≫
          L.map (pairingGraph J X Y) ≫ A.underlying.inv.app (X ⊗ Y) := by
  let := q
  ext V p
  have h := hq.1 X Y (sets J X ⊗ sets J Y)
    (CartesianMonoidalCategory.fst _ _) (CartesianMonoidalCategory.snd _ _)
    (pairingGraph J X Y) (fun _ _ ↦ rfl) V
    (abelianPair J K L A X Y V p.1 p.2)
  simp only [abelianPair, pairSource_fst, pairSource_snd] at h
  rw [underlying_hom_inv J K L A X V p.1, underlying_hom_inv J K L A Y V p.2] at h
  exact h.symm

private lemma unit_graph_of_normalization (q : A.functor.LaxMonoidal)
    (hq : TensorNormalization J K L A q) :
    letI := q
    oneGraph K ≫ (sheafCompose K (forget AddCommGrpCat.{u})).map
        (Functor.LaxMonoidal.ε A.functor) =
      inv (CartesianMonoidalCategory.terminalComparison L) ≫
        L.map (oneGraph J) ≫ A.underlying.inv.app (𝟙_ (Sheaf J AddCommGrpCat.{u})) := by
  let := q
  ext V x
  have h := hq.2 _ (oneGraph J) (fun _ _ ↦ rfl) V
    ((inv (CartesianMonoidalCategory.terminalComparison L)).hom.app V PUnit.unit)
  exact h.symm

end TransportPairing

set_option backward.isDefEq.respectTransparency true

variable
  (f : GeometricMorphism (Sheaf K (Type u)) (Sheaf J (Type u)))
  (A : AbelianInverseImagePresentation f.inverse)
  (B : AbelianInverseImagePresentation f.direct)
  (adj : A.functor ⊣ B.functor)
  (unit_eq : ∀ X : Sheaf J AddCommGrpCat.{u},
    (sheafCompose J (forget AddCommGrpCat.{u})).map (adj.unit.app X) ≫
      B.underlying.hom.app (A.functor.obj X) ≫
        f.direct.map (A.underlying.hom.app X) =
      f.adj.unit.app ((sheafCompose J (forget AddCommGrpCat.{u})).obj X))

omit [HasSheafify J AddCommGrpCat.{u}] [HasSheafify K AddCommGrpCat.{u}]
  [(J.W (A := AddCommGrpCat.{u})).IsMonoidal]
  [(K.W (A := AddCommGrpCat.{u})).IsMonoidal] in
include unit_eq in
private lemma underlying_adjunct (X : Sheaf J AddCommGrpCat.{u})
    (Y : Sheaf K AddCommGrpCat.{u}) (g : A.functor.obj X ⟶ Y) :
    f.adj.unit.app (sets J X) ≫
        f.direct.map (A.underlying.inv.app X ≫
          (sheafCompose K (forget AddCommGrpCat.{u})).map g) =
      (sheafCompose J (forget AddCommGrpCat.{u})).map ((adj.homEquiv X Y) g) ≫
        B.underlying.hom.app Y := by
  rw [← unit_eq X]
  simp only [Functor.map_comp, Category.assoc, Adjunction.homEquiv_unit]
  rw [← f.direct.map_comp_assoc, A.underlying.hom_inv_id_app]
  rw [f.direct.map_id ((A.functor ⋙ sheafCompose K (forget AddCommGrpCat.{u})).obj X)]
  change (sheafCompose J (forget AddCommGrpCat.{u})).map (adj.unit.app X) ≫
      B.underlying.hom.app (A.functor.obj X) ≫
        f.direct.map ((sheafCompose K (forget AddCommGrpCat.{u})).map g) = _
  exact congrArg (fun k ↦
    (sheafCompose J (forget AddCommGrpCat.{u})).map (adj.unit.app X) ≫ k)
      (B.underlying.hom.naturality g).symm

omit [HasSheafify K AddCommGrpCat.{u}] [(K.W (A := AddCommGrpCat.{u})).IsMonoidal] in
include unit_eq in
private lemma inverse_pairing_ext (X Y : Sheaf J AddCommGrpCat.{u})
    (Z : Sheaf K AddCommGrpCat.{u}) (a b : A.functor.obj (X ⊗ Y) ⟶ Z)
    (h : f.inverse.map (pairingGraph J X Y) ≫ A.underlying.inv.app (X ⊗ Y) ≫
        (sheafCompose K (forget AddCommGrpCat.{u})).map a =
      f.inverse.map (pairingGraph J X Y) ≫ A.underlying.inv.app (X ⊗ Y) ≫
        (sheafCompose K (forget AddCommGrpCat.{u})).map b) : a = b := by
  apply (adj.homEquiv _ _).injective
  apply pairingGraph_ext J
  apply (cancel_mono (B.underlying.hom.app Z)).mp
  rw [Category.assoc, Category.assoc,
    ← underlying_adjunct J K f A B adj unit_eq,
    ← underlying_adjunct J K f A B adj unit_eq]
  rw [← f.adj.unit_naturality_assoc, ← f.adj.unit_naturality_assoc]
  simpa only [Functor.map_comp, Category.assoc] using
    congrArg (fun k ↦ f.adj.unit.app (sets J X ⊗ sets J Y) ≫ f.direct.map k) h

omit [HasSheafify K AddCommGrpCat.{u}] [(K.W (A := AddCommGrpCat.{u})).IsMonoidal] in
include unit_eq in
private lemma inverse_one_ext (Z : Sheaf K AddCommGrpCat.{u})
    (a b : A.functor.obj (𝟙_ (Sheaf J AddCommGrpCat.{u})) ⟶ Z)
    (h : f.inverse.map (oneGraph J) ≫ A.underlying.inv.app _ ≫
        (sheafCompose K (forget AddCommGrpCat.{u})).map a =
      f.inverse.map (oneGraph J) ≫ A.underlying.inv.app _ ≫
        (sheafCompose K (forget AddCommGrpCat.{u})).map b) : a = b := by
  apply (adj.homEquiv _ _).injective
  apply unit_ext J
  intro V
  have he : oneGraph J ≫ (sheafCompose J (forget AddCommGrpCat.{u})).map
        ((adj.homEquiv _ _) a) =
      oneGraph J ≫ (sheafCompose J (forget AddCommGrpCat.{u})).map
        ((adj.homEquiv _ _) b) := by
    apply (cancel_mono (B.underlying.hom.app Z)).mp
    rw [Category.assoc, Category.assoc,
      ← underlying_adjunct J K f A B adj unit_eq,
      ← underlying_adjunct J K f A B adj unit_eq]
    rw [← f.adj.unit_naturality_assoc, ← f.adj.unit_naturality_assoc]
    simpa only [Functor.map_comp, Category.assoc] using
      congrArg (fun k ↦ f.adj.unit.app (𝟙_ (Sheaf J (Type u))) ≫ f.direct.map k) h
  exact congrArg (fun k ↦ k.hom.app V PUnit.unit) he

omit [UnivLE.{max uD vD, u}]
  [HasSheafify J AddCommGrpCat.{u}] [HasSheafify K AddCommGrpCat.{u}]
  [(J.W (A := AddCommGrpCat.{u})).IsMonoidal]
  [(K.W (A := AddCommGrpCat.{u})).IsMonoidal] in
private lemma underlying_inv_naturality (X Y : Sheaf J AddCommGrpCat.{u}) (h : X ⟶ Y)
    (V : Dᵒᵖ) (x : (f.inverse.obj (sets J X)).obj.obj V) :
    (A.underlying.inv.app Y).hom.app V
        ((f.inverse.map ((sheafCompose J (forget AddCommGrpCat.{u})).map h)).hom.app V x) =
      ((A.functor.map h).hom.app V).hom ((A.underlying.inv.app X).hom.app V x) :=
  congrArg (fun k => k.hom.app V x) (A.underlying.inv.naturality h)

omit [UnivLE.{max uD vD, u}] in
private lemma transport_bilinear (q : A.functor.LaxMonoidal)
    (hq : TensorNormalization J K f.inverse A q)
    (X Y Z : Sheaf J AddCommGrpCat.{u}) (b : X ⊗ Y ⟶ Z)
    (V : Dᵒᵖ) (x : (f.inverse.obj (sets J X ⊗ sets J Y)).obj.obj V) :
    letI := q
    (A.underlying.inv.app Z).hom.app V
      ((f.inverse.map (pairingGraph J X Y ≫
        (sheafCompose J (forget AddCommGrpCat.{u})).map b)).hom.app V x) =
      ((A.functor.map b).hom.app V).hom
        (((Functor.LaxMonoidal.μ A.functor X Y).hom.app V).hom
          (tensorSection K (A.functor.obj X) (A.functor.obj Y) V
            ((A.underlying.inv.app X).hom.app V
              ((f.inverse.map (CartesianMonoidalCategory.fst _ _)).hom.app V x))
            ((A.underlying.inv.app Y).hom.app V
              ((f.inverse.map (CartesianMonoidalCategory.snd _ _)).hom.app V x)))) := by
  let := q
  rw [f.inverse.map_comp]
  change (A.underlying.inv.app Z).hom.app V
    ((f.inverse.map ((sheafCompose J (forget AddCommGrpCat.{u})).map b)).hom.app V
      ((f.inverse.map (pairingGraph J X Y)).hom.app V x)) = _
  rw [underlying_inv_naturality J K f A]
  congr 1
  exact hq.1 X Y (sets J X ⊗ sets J Y)
    (CartesianMonoidalCategory.fst _ _) (CartesianMonoidalCategory.snd _ _)
    (pairingGraph J X Y) (fun _ _ => rfl) V x

omit [UnivLE.{max uD vD, u}] in
private lemma transport_one (q : A.functor.LaxMonoidal)
    (hq : TensorNormalization J K f.inverse A q)
    (Z : Sheaf J AddCommGrpCat.{u}) (b : 𝟙_ (Sheaf J AddCommGrpCat.{u}) ⟶ Z)
    (V : Dᵒᵖ) (x : (f.inverse.obj (𝟙_ (Sheaf J (Type u)))).obj.obj V) :
    letI := q
    (A.underlying.inv.app Z).hom.app V
      ((f.inverse.map (oneGraph J ≫
        (sheafCompose J (forget AddCommGrpCat.{u})).map b)).hom.app V x) =
      ((A.functor.map b).hom.app V).hom
        (((Functor.LaxMonoidal.ε A.functor).hom.app V).hom (integerOne K V)) := by
  let := q
  rw [f.inverse.map_comp]
  change (A.underlying.inv.app Z).hom.app V
    ((f.inverse.map ((sheafCompose J (forget AddCommGrpCat.{u})).map b)).hom.app V
      ((f.inverse.map (oneGraph J)).hom.app V x)) = _
  rw [underlying_inv_naturality J K f A]
  congr 1
  exact hq.2 _ (oneGraph J) (fun _ _ => rfl) V x

omit [UnivLE.{max uD vD, u}] in
private lemma abelianPair_bilinear (q : A.functor.LaxMonoidal)
    (hq : TensorNormalization J K f.inverse A q)
    [PreservesFiniteProducts f.inverse]
    (X Y Z : Sheaf J AddCommGrpCat.{u}) (b : X ⊗ Y ⟶ Z)
    (V : Dᵒᵖ) (r : (A.functor.obj X).obj.obj V) (s : (A.functor.obj Y).obj.obj V) :
    letI := q
    (A.underlying.hom.app Z).hom.app V
      (((A.functor.map b).hom.app V).hom
        (((Functor.LaxMonoidal.μ A.functor X Y).hom.app V).hom
          (tensorSection K (A.functor.obj X) (A.functor.obj Y) V r s))) =
      (f.inverse.map (pairingGraph J X Y ≫
        (sheafCompose J (forget AddCommGrpCat.{u})).map b)).hom.app V
          (abelianPair J K f.inverse A X Y V r s) := by
  let := q
  have h := transport_bilinear J K f A q hq X Y Z b V
    (abelianPair J K f.inverse A X Y V r s)
  simp only [abelianPair, pairSource_fst, pairSource_snd, underlying_hom_inv] at h
  have hh := congrArg (fun x => (A.underlying.hom.app Z).hom.app V x) h
  simpa only [underlying_inv_hom, abelianPair] using hh.symm

private def terminalSource (L : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    [PreservesFiniteProducts L] (V : Dᵒᵖ) :
    (L.obj (𝟙_ (Sheaf J (Type u)))).obj.obj V :=
  (inv (CartesianMonoidalCategory.terminalComparison L)).hom.app V PUnit.unit

omit [UnivLE.{max uD vD, u}] in
private lemma terminalSource_one (q : A.functor.LaxMonoidal)
    (hq : TensorNormalization J K f.inverse A q)
    [PreservesFiniteProducts f.inverse]
    (Z : Sheaf J AddCommGrpCat.{u}) (b : 𝟙_ (Sheaf J AddCommGrpCat.{u}) ⟶ Z)
    (V : Dᵒᵖ) :
    letI := q
    (A.underlying.hom.app Z).hom.app V
      (((A.functor.map b).hom.app V).hom
        (((Functor.LaxMonoidal.ε A.functor).hom.app V).hom (integerOne K V))) =
      (f.inverse.map (oneGraph J ≫
        (sheafCompose J (forget AddCommGrpCat.{u})).map b)).hom.app V
          (terminalSource J K f.inverse V) := by
  let := q
  have h := transport_one J K f A q hq Z b V (terminalSource J K f.inverse V)
  have hh := congrArg (fun x => (A.underlying.hom.app Z).hom.app V x) h
  simpa only [underlying_inv_hom] using hh.symm

/-- The canonical direct-image lax tensor structure is uniquely determined by the
universal bilinear pairing and 1. Source: Stacks 03EK, 00YV
(blueprint: lem-sfb-internal-module-inverse-image-comparison).

Proof (node step 1). The right adjoint preserves finite products. Transport the
universal bilinear pairing by its inverse product comparison. The abelian lift
preserves addition and zero, so this pairing is separately additive. Extend uniquely
through Mathlib's integer tensor product and the sheafification adjunction,
using `TensorProduct.liftAddHom` and the invertible canonical tensor comparison.
Extend n to n times the transported 1 for the unit. Associativity and the unit laws
hold on universal pairs and triples, hence everywhere by uniqueness. This also
proves uniqueness of both structure maps and consequently of the lax structure. -/
theorem directLax_existsUnique :
    ∃! q : B.functor.LaxMonoidal, TensorNormalization K J f.direct B q := by
  have : f.direct.IsRightAdjoint := f.adj.isRightAdjoint
  exact ⟨normalizedLax K J f.direct B, normalizedLax_spec K J f.direct B,
    fun q hq ↦ normalization_unique K J f.direct B q _ hq
      (normalizedLax_spec K J f.direct B)⟩

/-- The uniquely normalized direct-image lax structure.
Source: Stacks 03EK (blueprint: lem-sfb-internal-module-inverse-image-comparison). -/
@[instance_reducible] def directLax : B.functor.LaxMonoidal :=
  Classical.choose (directLax_existsUnique J K f B)

/-- The oplax mate of the actual canonical direct-image lax structure.
Source: Mathlib monoidal-adjunction mates and Stacks 03EL
(blueprint: lem-sfb-internal-module-inverse-image-comparison). -/
@[instance_reducible] def inverseOplax : A.functor.OplaxMonoidal :=
  letI := directLax J K f B
  adj.leftAdjointOplaxMonoidal

include unit_eq in
set_option backward.isDefEq.respectTransparency false in
private lemma inverseOplax_tensor_graph (X Y : Sheaf J AddCommGrpCat.{u}) :
    letI := inverseOplax J K f A B adj
    f.inverse.map (pairingGraph J X Y) ≫ A.underlying.inv.app (X ⊗ Y) ≫
        (sheafCompose K (forget AddCommGrpCat.{u})).map
          (Functor.OplaxMonoidal.δ A.functor X Y) =
      CartesianMonoidalCategory.prodComparison f.inverse (sets J X) (sets J Y) ≫
        (A.underlying.inv.app X ⊗ₘ A.underlying.inv.app Y) ≫
          pairingGraph K (A.functor.obj X) (A.functor.obj Y) := by
  let := f.leftExact
  have : f.direct.IsRightAdjoint := f.adj.isRightAdjoint
  let := directLax J K f B
  let := inverseOplax J K f A B adj
  let U := sheafCompose J (forget AddCommGrpCat.{u})
  let V := sheafCompose K (forget AddCommGrpCat.{u})
  let m := Functor.LaxMonoidal.μ B.functor (A.functor.obj X) (A.functor.obj Y)
  let d := Functor.OplaxMonoidal.δ A.functor X Y
  have hd : (adj.homEquiv _ _) d =
      (adj.unit.app X ⊗ₘ adj.unit.app Y) ≫ m :=
    (adj.homEquiv (X ⊗ Y) (A.functor.obj X ⊗ A.functor.obj Y)).apply_symm_apply
      ((adj.unit.app X ⊗ₘ adj.unit.app Y) ≫ m)
  have hn := (Classical.choose_spec (directLax_existsUnique J K f B)).1
  have hm : pairingGraph J (B.functor.obj (A.functor.obj X))
        (B.functor.obj (A.functor.obj Y)) ≫ U.map m ≫
        B.underlying.hom.app (A.functor.obj X ⊗ A.functor.obj Y) =
      (B.underlying.hom.app (A.functor.obj X) ⊗ₘ
          B.underlying.hom.app (A.functor.obj Y)) ≫
        inv (CartesianMonoidalCategory.prodComparison f.direct
          (sets K (A.functor.obj X)) (sets K (A.functor.obj Y))) ≫
          f.direct.map (pairingGraph K (A.functor.obj X) (A.functor.obj Y)) := by
    have hh := congrArg
      (fun k ↦ k ≫ B.underlying.hom.app (A.functor.obj X ⊗ A.functor.obj Y))
      (tensor_graph_of_normalization K J f.direct B _ hn
        (A.functor.obj X) (A.functor.obj Y))
    simp only [Category.assoc, Iso.inv_hom_id_app] at hh
    exact hh.trans (congrArg (fun k ↦
      ((B.underlying.hom.app (A.functor.obj X) ⊗ₘ
          B.underlying.hom.app (A.functor.obj Y)) ≫
        inv (CartesianMonoidalCategory.prodComparison f.direct
          (sets K (A.functor.obj X)) (sets K (A.functor.obj Y)))) ≫ k)
      (Category.comp_id (f.direct.map
        (pairingGraph K (A.functor.obj X) (A.functor.obj Y)))))
  have hη (Z : Sheaf J AddCommGrpCat.{u}) :
      f.adj.unit.app (sets J Z) ≫ f.direct.map (A.underlying.inv.app Z) =
        U.map (adj.unit.app Z) ≫ B.underlying.hom.app (A.functor.obj Z) := by
    rw [← unit_eq Z, Category.assoc, Category.assoc, ← f.direct.map_comp,
      A.underlying.hom_inv_id_app]
    rw [f.direct.map_id ((A.functor ⋙ sheafCompose K (forget AddCommGrpCat.{u})).obj Z)]
    change U.map (adj.unit.app Z) ≫ B.underlying.hom.app (A.functor.obj Z) = _
    rfl
  have hp : f.adj.unit.app (sets J X ⊗ sets J Y) ≫
        f.direct.map (CartesianMonoidalCategory.prodComparison f.inverse
          (sets J X) (sets J Y)) ≫
        CartesianMonoidalCategory.prodComparison f.direct
          (f.inverse.obj (sets J X)) (f.inverse.obj (sets J Y)) =
      f.adj.unit.app (sets J X) ⊗ₘ f.adj.unit.app (sets J Y) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, CartesianMonoidalCategory.prodComparison_fst,
        ← f.direct.map_comp, CartesianMonoidalCategory.prodComparison_fst]
      have hproj := CartesianMonoidalCategory.tensorHom_fst
        (f.adj.unit.app (sets J X)) (f.adj.unit.app (sets J Y))
      dsimp only [Functor.comp_obj] at hproj
      erw [hproj]
      exact f.adj.unit_naturality (CartesianMonoidalCategory.fst _ _)
    · simp only [Category.assoc, CartesianMonoidalCategory.prodComparison_snd,
        ← f.direct.map_comp, CartesianMonoidalCategory.prodComparison_snd]
      have hproj := CartesianMonoidalCategory.tensorHom_snd
        (f.adj.unit.app (sets J X)) (f.adj.unit.app (sets J Y))
      dsimp only [Functor.comp_obj] at hproj
      erw [hproj]
      exact f.adj.unit_naturality (CartesianMonoidalCategory.snd _ _)
  apply (f.adj.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, f.direct.map_comp]
  rw [f.adj.unit_naturality_assoc]
  rw [← f.direct.map_comp]
  rw [underlying_adjunct J K f A B adj unit_eq, hd, U.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% pairingGraph_natural J (adj.unit.app X) (adj.unit.app Y), hm]
  have hpair :
      (U.map (adj.unit.app X) ⊗ₘ U.map (adj.unit.app Y)) ≫
          (B.underlying.hom.app (A.functor.obj X) ⊗ₘ
            B.underlying.hom.app (A.functor.obj Y)) =
        (f.adj.unit.app (sets J X) ⊗ₘ f.adj.unit.app (sets J Y)) ≫
          (f.direct.map (A.underlying.inv.app X) ⊗ₘ
            f.direct.map (A.underlying.inv.app Y)) := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext W
    apply ConcreteCategory.hom_ext
    intro z
    exact Prod.ext (congrArg (fun k ↦ k.hom.app W z.1) (hη X).symm)
      (congrArg (fun k ↦ k.hom.app W z.2) (hη Y).symm)
  have hnprod := CartesianMonoidalCategory.prodComparison_inv_natural
    f.direct (A.underlying.inv.app X) (A.underlying.inv.app Y)
  have hp' : f.adj.unit.app (sets J X ⊗ sets J Y) ≫
        f.direct.map (CartesianMonoidalCategory.prodComparison f.inverse
          (sets J X) (sets J Y)) =
      (f.adj.unit.app (sets J X) ⊗ₘ f.adj.unit.app (sets J Y)) ≫
        inv (CartesianMonoidalCategory.prodComparison f.direct
          (f.inverse.obj (sets J X)) (f.inverse.obj (sets J Y))) := by
    apply (IsIso.eq_comp_inv _).mpr
    exact (Category.assoc _ _ _).trans hp
  have hpair' := congrArg (fun k ↦ k ≫
    inv (CartesianMonoidalCategory.prodComparison f.direct
      (sets K (A.functor.obj X)) (sets K (A.functor.obj Y))) ≫
        f.direct.map (pairingGraph K (A.functor.obj X) (A.functor.obj Y))) hpair
  have hnat := congrArg (fun k ↦
    (f.adj.unit.app (sets J X) ⊗ₘ f.adj.unit.app (sets J Y)) ≫ k ≫
      f.direct.map (pairingGraph K (A.functor.obj X) (A.functor.obj Y))) hnprod.symm
  have hfinal := congrArg (fun k ↦ k ≫
    f.direct.map (A.underlying.inv.app X ⊗ₘ A.underlying.inv.app Y) ≫
      f.direct.map (pairingGraph K (A.functor.obj X) (A.functor.obj Y))) hp'.symm
  exact hpair'.trans ((Category.assoc _ _ _).trans
    (hnat.trans ((Category.assoc _ _ _).symm.trans
      (hfinal.trans (Category.assoc _ _ _)))))


include unit_eq in
private lemma inverseOplax_unit_graph :
    letI := inverseOplax J K f A B adj
    f.inverse.map (oneGraph J) ≫ A.underlying.inv.app (𝟙_ (Sheaf J AddCommGrpCat.{u})) ≫
        (sheafCompose K (forget AddCommGrpCat.{u})).map
          (Functor.OplaxMonoidal.η A.functor) =
      CartesianMonoidalCategory.terminalComparison f.inverse ≫ oneGraph K := by
  let := f.leftExact
  have : f.direct.IsRightAdjoint := f.adj.isRightAdjoint
  let := directLax J K f B
  let := inverseOplax J K f A B adj
  let U := sheafCompose J (forget AddCommGrpCat.{u})
  let e : 𝟙_ (Sheaf J AddCommGrpCat.{u}) ⟶
      B.functor.obj (𝟙_ (Sheaf K AddCommGrpCat.{u})) := Functor.LaxMonoidal.ε B.functor
  let d : A.functor.obj (𝟙_ (Sheaf J AddCommGrpCat.{u})) ⟶
      𝟙_ (Sheaf K AddCommGrpCat.{u}) := Functor.OplaxMonoidal.η A.functor
  have hd : (adj.homEquiv _ _) d = e :=
    (adj.homEquiv (𝟙_ (Sheaf J AddCommGrpCat.{u}))
      (𝟙_ (Sheaf K AddCommGrpCat.{u}))).apply_symm_apply e
  have hn := (Classical.choose_spec (directLax_existsUnique J K f B)).1
  have he : oneGraph J ≫ U.map e ≫ B.underlying.hom.app (𝟙_ (Sheaf K AddCommGrpCat.{u})) =
      inv (CartesianMonoidalCategory.terminalComparison f.direct) ≫
        f.direct.map (oneGraph K) := by
    have hh := congrArg
      (fun k ↦ k ≫ B.underlying.hom.app (𝟙_ (Sheaf K AddCommGrpCat.{u})))
      (unit_graph_of_normalization K J f.direct B _ hn)
    simp only [Category.assoc, Iso.inv_hom_id_app] at hh
    exact hh.trans (congrArg (fun k ↦
      inv (CartesianMonoidalCategory.terminalComparison f.direct) ≫ k)
      (Category.comp_id (f.direct.map (oneGraph K))))
  have ht : f.adj.unit.app (𝟙_ (Sheaf J (Type u))) ≫
        f.direct.map (CartesianMonoidalCategory.terminalComparison f.inverse) =
      inv (CartesianMonoidalCategory.terminalComparison f.direct) := by
    apply (cancel_mono (CartesianMonoidalCategory.terminalComparison f.direct)).mp
    exact CartesianMonoidalCategory.toUnit_unique _ _
  apply (f.adj.homEquiv (𝟙_ (Sheaf J (Type u)))
    (sets K (𝟙_ (Sheaf K AddCommGrpCat.{u})))).injective
  simp only [Adjunction.homEquiv_unit, f.direct.map_comp]
  rw [f.adj.unit_naturality_assoc]
  rw [← f.direct.map_comp]
  rw [underlying_adjunct J K f A B adj unit_eq, hd, he, ← ht, Category.assoc]

include unit_eq in
private lemma inverseOplax_tensor_inverse (X Y : Sheaf J AddCommGrpCat.{u}) :
    letI := f.leftExact
    letI := inverseOplax J K f A B adj
    transportedTensor J K f.inverse A X Y ≫ Functor.OplaxMonoidal.δ A.functor X Y = 𝟙 _ ∧
      Functor.OplaxMonoidal.δ A.functor X Y ≫ transportedTensor J K f.inverse A X Y = 𝟙 _ := by
  let := f.leftExact
  let := inverseOplax J K f A B adj
  let U := sheafCompose K (forget AddCommGrpCat.{u})
  have hg := inverseOplax_tensor_graph J K f A B adj unit_eq X Y
  have hm := normalized_tensor_graph J K f.inverse A X Y
  constructor
  · apply pairingGraph_ext K
    rw [Functor.map_comp, ← Category.assoc, hm]
    simp only [Category.assoc]
    rw [hg]
    simp only [IsIso.inv_hom_id_assoc, Functor.map_id, Category.comp_id]
    exact (congrArg (fun k ↦ k ≫ pairingGraph K (A.functor.obj X) (A.functor.obj Y))
      (underlying_tensor_hom_inv J K f.inverse A X Y)).trans (Category.id_comp _)
  · apply inverse_pairing_ext J K f A B adj unit_eq X Y _
    simp only [Functor.map_comp, Functor.map_id]
    rw [reassoc_of% hg, hm]
    erw [reassoc_of% underlying_tensor_inv_hom J K f.inverse A X Y]
    simp only [IsIso.hom_inv_id_assoc]
    rfl

include unit_eq in
private lemma inverseOplax_unit_inverse :
    letI := f.leftExact
    letI := inverseOplax J K f A B adj
    transportedUnit J K f.inverse A ≫ Functor.OplaxMonoidal.η A.functor = 𝟙 _ ∧
      Functor.OplaxMonoidal.η A.functor ≫ transportedUnit J K f.inverse A = 𝟙 _ := by
  let := f.leftExact
  let := inverseOplax J K f A B adj
  let U := sheafCompose K (forget AddCommGrpCat.{u})
  have hg := inverseOplax_unit_graph J K f A B adj unit_eq
  have hm : oneGraph K ≫ U.map (transportedUnit J K f.inverse A) =
      inv (CartesianMonoidalCategory.terminalComparison f.inverse) ≫
        f.inverse.map (oneGraph J) ≫ A.underlying.inv.app _ := by
    ext V x
    exact transportedUnit_spec J K f.inverse A V
  constructor
  · apply unit_ext K
    intro V
    have h : oneGraph K ≫ U.map
        (transportedUnit J K f.inverse A ≫ Functor.OplaxMonoidal.η A.functor) = oneGraph K := by
      rw [U.map_comp, ← Category.assoc, hm, Category.assoc, Category.assoc, hg]
      simp only [IsIso.inv_hom_id_assoc]
    exact congrArg (fun k ↦ k.hom.app V PUnit.unit) h
  · apply inverse_one_ext J K f A B adj unit_eq
    simp only [Functor.map_comp, Functor.map_id]
    rw [reassoc_of% hg, hm]
    simp only [IsIso.hom_inv_id_assoc]
    rfl

include unit_eq in
/-- Inverting the canonical oplax mate gives the uniquely normalized symmetric
strong tensor structure. Source: Stacks 03EL, 00YV
(blueprint: lem-sfb-internal-module-inverse-image-comparison).

Proof (node steps 2--3). By lem-sfb-monoidal-adjunction-mates the adjunct of d is
m composed with the tensor of the two units. Step 1 and unit_eq identify its
underlying adjunct on the universal pairing p with G(p) rho^{-1}(eta times eta).
Naturality of the set unit then gives d L(p) = p lambda, by injectivity of the SET
adjunction. Separate additivity of L(p) lambda^{-1} gives an additive extension phi.
Tensor uniqueness gives d phi = 1. Maps out of L(X tensor Y) are determined by
precomposition with L(p), using the abelian adjunction, unit_eq, and injectivity of
the set adjunction, so phi d = 1 as well. The same argument with the integer section
1 gives d0 L(1) = 1 lambda_* and an inverse to d0. Thus the mate is strong and its
inverse has exactly TensorNormalization. Symmetry follows on the universal pairing;
coherence and uniqueness follow from tensor and integer-unit uniqueness. -/
theorem inverseBraided_existsUnique :
    ∃! q : A.functor.Braided,
      q.toMonoidal.toOplaxMonoidal = inverseOplax J K f A B adj ∧
      TensorNormalization J K f.inverse A q.toMonoidal.toLaxMonoidal := by
  let := f.leftExact
  let := inverseOplax J K f A B adj
  have hu := inverseOplax_unit_inverse J K f A B adj unit_eq
  have ht := inverseOplax_tensor_inverse J K f A B adj unit_eq
  have : IsIso (Functor.OplaxMonoidal.η A.functor) :=
    ⟨⟨transportedUnit J K f.inverse A, hu.2, hu.1⟩⟩
  have (X Y : Sheaf J AddCommGrpCat.{u}) :
      IsIso (Functor.OplaxMonoidal.δ A.functor X Y) :=
    ⟨⟨transportedTensor J K f.inverse A X Y, (ht X Y).2, (ht X Y).1⟩⟩
  let m := Functor.Monoidal.ofOplaxMonoidal A.functor
  have hε : m.toLaxMonoidal.ε = transportedUnit J K f.inverse A :=
    IsIso.inv_eq_of_hom_inv_id hu.2
  have hμ : m.toLaxMonoidal.μ = transportedTensor J K f.inverse A := by
    funext X Y
    exact IsIso.inv_eq_of_hom_inv_id (ht X Y).2
  have hq : m.toLaxMonoidal = normalizedLax J K f.inverse A :=
    Functor.LaxMonoidal.ext
      (hε.trans (normalizedLax_ε J K f.inverse A).symm)
      (hμ.trans (normalizedLax_μ J K f.inverse A).symm)
  let q : A.functor.Braided :=
    { m with
      braided X Y := by
        change m.toLaxMonoidal.μ X Y ≫ A.functor.map (β_ X Y).hom =
          (β_ _ _).hom ≫ m.toLaxMonoidal.μ Y X
        rw [hμ]
        exact transportedTensor_braided J K f.inverse A X Y }
  refine ⟨q, ⟨?_, ?_⟩, ?_⟩
  · rfl
  · change TensorNormalization J K f.inverse A m.toLaxMonoidal
    rw [hq]
    exact normalizedLax_spec J K f.inverse A
  · intro q' hq'
    apply Functor.Braided.toMonoidal_injective
    apply Functor.Monoidal.toOplaxMonoidal_injective
    exact hq'.1

/-- The canonical strong structure, uniquely characterized by its oplax mate and
universal-pairing normalization, rather than an arbitrary monoidal choice.
Source: Stacks 03EL (blueprint: lem-sfb-internal-module-inverse-image-comparison). -/
@[instance_reducible] def inverseBraided : A.functor.Braided :=
  Classical.choose (inverseBraided_existsUnique J K f A B adj unit_eq)


/-- The canonical same-universe lift of the underlying set sheaf. It is used only
because the recorded algebraic-inverse-image interface explicitly uses `ULift`.
Source: size convention and Stacks 00YV
(blueprint: lem-sfb-internal-module-inverse-image-comparison). -/
def underlyingULift (X : Sheaf J AddCommGrpCat.{u}) :
    (sheafCompose J (forget AddCommGrpCat.{u})).obj X ⟶
      (sheafCompose J (forget AddCommGrpCat.{u} ⋙ uliftFunctor.{u, u})).obj X :=
  (sheafCompose_map J
    (Functor.whiskerLeft (forget AddCommGrpCat.{u}) uliftFunctorTrivial.inv)).app X

section Complexes
universe uE vE uH vH

/-- The termwise natural comparison and its image in the derived category. The
component formula fixes the complex isomorphism; the last equation fixes its derived
image to be localization of that very chain map.
Source: Stacks 05RR (blueprint: lem-sfb-internal-module-inverse-image-comparison). -/
def ComplexComparison
    {E : Type uE} {H : Type uH} [Category.{vE} E] [Category.{vH} H]
    [HasZeroMorphisms E] [Abelian H] (F G : E ⥤ H) (θ : F ≅ G) : Prop :=
  ∃ hF : F.PreservesZeroMorphisms, ∃ hG : G.PreservesZeroMorphisms,
    letI := hF
    letI := hG
    (∀ (P : CochainComplex E ℤ) (n : ℤ),
      ((NatIso.mapHomologicalComplex θ (.up ℤ)).hom.app P).f n = θ.hom.app (P.X n)) ∧
    (∀ (P : CochainComplex E ℤ) (i j : ℤ),
      F.map (P.d i j) ≫ θ.hom.app (P.X j) =
        θ.hom.app (P.X i) ≫ G.map (P.d i j)) ∧
    (letI := HasDerivedCategory.standard H
     ∃ d : F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ≅
         G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q,
       ∀ P : CochainComplex E ℤ,
         d.hom.app P = DerivedCategory.Q.map
           ((NatIso.mapHomologicalComplex θ (.up ℤ)).hom.app P))

omit [UnivLE.{max uC vC, u}] [UnivLE.{max uD vD, u}]
  [HasSheafify J AddCommGrpCat.{u}] [HasSheafify K AddCommGrpCat.{u}]
  [(J.W (A := AddCommGrpCat.{u})).IsMonoidal]
  [(K.W (A := AddCommGrpCat.{u})).IsMonoidal] in
private theorem complexComparison_of_iso
    {E : Type uE} {H : Type uH} [Category.{vE} E] [Category.{vH} H]
    [HasZeroMorphisms E] [Abelian H] (F G : E ⥤ H) (θ : F ≅ G)
    (hF : F.PreservesZeroMorphisms) : ComplexComparison F G θ := by
  have hG : G.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_iso θ
  refine ⟨hF, hG, ?_, ?_, ?_⟩
  · intro P n
    rfl
  · intro P i j
    exact θ.hom.naturality (P.d i j)
  · let := HasDerivedCategory.standard H
    exact ⟨Functor.isoWhiskerRight (NatIso.mapHomologicalComplex θ (.up ℤ)) DerivedCategory.Q,
      fun _ ↦ rfl⟩

end Complexes

/-- The full ring, semilinear-module and unbounded-complex comparison for a specified
strong lift. All underlying identifications are fixed, so this is a canonical
comparison, not just existence of some equivalence of module categories.
Source: Stacks 03D2 and 00YV
(blueprint: lem-sfb-internal-module-inverse-image-comparison). -/
def ComparisonStatement (q : A.functor.Braided) : Prop :=
  letI := q
  letI : UnivLE.{uC, u} :=
    @UnivLE.trans.{uC, max uC vC, u} univLE_max inferInstance
  letI : UnivLE.{vC, u} :=
    @UnivLE.trans.{vC, max uC vC, u} univLE_max inferInstance
  letI : UnivLE.{uD, u} :=
    @UnivLE.trans.{uD, max uD vD, u} univLE_max inferInstance
  letI : UnivLE.{vD, u} :=
    @UnivLE.trans.{vD, max uD vD, u} univLE_max inferInstance
  letI : PreservesLimitsOfSize.{vC, max uC vC} (forget CommRingCat.{u}) :=
    preservesLimitsOfSize_of_univLE.{u, u, vC, max uC vC} (forget CommRingCat.{u})
  letI : PreservesLimitsOfSize.{vD, max uD vD} (forget CommRingCat.{u}) :=
    preservesLimitsOfSize_of_univLE.{u, u, vD, max uD vD} (forget CommRingCat.{u})
  letI : J.HasSheafCompose (forget CommRingCat.{u} ⋙ uliftFunctor.{u, u}) :=
    hasSheafCompose_of_preservesLimitsOfSize J
  letI : K.HasSheafCompose (forget CommRingCat.{u} ⋙ uliftFunctor.{u, u}) :=
    hasSheafCompose_of_preservesLimitsOfSize K
  letI : EssentiallySmall.{u} D := inferInstance
  letI (X : Dᵒᵖ) :
      HasLimitsOfShape (StructuredArrow X (equivSmallModel.{u} D).inverse.op)
        AddCommGrpCat.{u} := HasLimitsOfShape.of_small.{u, u} AddCommGrpCat.{u} _
  letI : K.WEqualsLocallyBijective AddCommGrpCat.{u} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{vD, u, uD, u + 1, u, u, u}
      K (A := AddCommGrpCat.{u})
  ∀ (R : Sheaf J AddCommGrpCat.{u}) [MonObj R] [IsCommMonObj R]
    (RI : Sheaf K CommRingCat.{u})
    (I : SheafOfModules.AlgebraicInverseImageOfUniverses
      f.inverse (InternalAbelianSheafModule.sectionRingSheaf J R) RI),
    ∃ σ : InternalAbelianSheafModule.sectionRingSheaf K (A.functor.obj R) ≅ RI,
      (∀ (V : Dᵒᵖ) (r : (A.functor.obj R).obj.obj V),
        ULift.up ((σ.hom.hom.app V).hom r) =
          (I.ringUnderlying.hom.hom.app V)
            ((f.inverse.map (underlyingULift J R)).hom.app V
              ((A.underlying.hom.app R).hom.app V r))) ∧
      ∃ θ : A.functor.mapMod R ⋙
            (InternalAbelianSheafModule.sectionModuleEquivalence K (A.functor.obj R)).functor ≅
          (InternalAbelianSheafModule.sectionModuleEquivalence J R).functor ⋙ I.modules ⋙
            SheafOfModules.restrictScalars
              ((sheafCompose K (forget₂ CommRingCat RingCat)).map σ.hom),
        (∀ (M : Mod (Sheaf J AddCommGrpCat.{u}) R) (V : Dᵒᵖ)
          (x : (A.functor.obj M.X).obj.obj V),
          (I.moduleUnderlying.hom.app
              ((InternalAbelianSheafModule.sectionModuleEquivalence J R).functor.obj M)).hom.app
              V (ULift.up (((θ.hom.app M).val.app V).hom x)) =
            (f.inverse.map (underlyingULift J M.X)).hom.app V
              ((A.underlying.hom.app M.X).hom.app V x)) ∧
        ComplexComparison _ _ θ

omit [UnivLE.{max uD vD, u}]
  [HasSheafify J AddCommGrpCat.{u}] [HasSheafify K AddCommGrpCat.{u}]
  [(J.W (A := AddCommGrpCat.{u})).IsMonoidal]
  [(K.W (A := AddCommGrpCat.{u})).IsMonoidal] in
private lemma graph_compare_add [PreservesFiniteProducts f.inverse]
    (X : Sheaf J AddCommGrpCat.{u}) (V : Dᵒᵖ)
    {N : Type u} [AddCommGroup N]
    (e : (A.functor.obj X).obj.obj V → N)
    (p : (f.inverse.obj (sets J X)).obj.obj V → N)
    (he : ∀ w, e ((A.underlying.inv.app X).hom.app V w) = p w)
    (h : ∀ z : (f.inverse.obj (sets J X ⊗ sets J X)).obj.obj V,
      p ((f.inverse.map (addGraph J X)).hom.app V z) =
        p ((f.inverse.map (CartesianMonoidalCategory.fst _ _)).hom.app V z) +
          p ((f.inverse.map (CartesianMonoidalCategory.snd _ _)).hom.app V z))
    (r s : (A.functor.obj X).obj.obj V) : e (r + s) = e r + e s := by
  have h' := h (abelianPair J K f.inverse A X X V r s)
  rw [← he, ← he, ← he] at h'
  simp only [abelianPair, pairSource_fst, pairSource_snd, underlying_hom_inv] at h'
  have hh := abelianPair_add J K f.inverse A X V r s
  have hh' := congrArg (fun w ↦ e ((A.underlying.inv.app X).hom.app V w)) hh
  rw [underlying_hom_inv] at hh'
  exact hh'.trans h'

omit [UnivLE.{max uD vD, u}] in
private lemma graph_compare_bilinear [PreservesFiniteProducts f.inverse]
    (q : A.functor.LaxMonoidal)
    (hq : TensorNormalization J K f.inverse A q)
    (X Y Z : Sheaf J AddCommGrpCat.{u}) (b : X ⊗ Y ⟶ Z) (V : Dᵒᵖ)
    {N P Q : Type u} (eX : (A.functor.obj X).obj.obj V → N)
    (eY : (A.functor.obj Y).obj.obj V → P) (eZ : (A.functor.obj Z).obj.obj V → Q)
    (pX : (f.inverse.obj (sets J X)).obj.obj V → N)
    (pY : (f.inverse.obj (sets J Y)).obj.obj V → P)
    (pZ : (f.inverse.obj (sets J Z)).obj.obj V → Q)
    (hX : ∀ w, eX ((A.underlying.inv.app X).hom.app V w) = pX w)
    (hY : ∀ w, eY ((A.underlying.inv.app Y).hom.app V w) = pY w)
    (hZ : ∀ w, eZ ((A.underlying.inv.app Z).hom.app V w) = pZ w)
    (op : N → P → Q)
    (h : ∀ z : (f.inverse.obj (sets J X ⊗ sets J Y)).obj.obj V,
      pZ ((f.inverse.map (pairingGraph J X Y ≫
        (sheafCompose J (forget AddCommGrpCat.{u})).map b)).hom.app V z) =
        op (pX ((f.inverse.map (CartesianMonoidalCategory.fst _ _)).hom.app V z))
          (pY ((f.inverse.map (CartesianMonoidalCategory.snd _ _)).hom.app V z)))
    (r : (A.functor.obj X).obj.obj V) (s : (A.functor.obj Y).obj.obj V) :
    letI := q
    eZ (((A.functor.map b).hom.app V).hom
      (((Functor.LaxMonoidal.μ A.functor X Y).hom.app V).hom
        (tensorSection K _ _ V r s))) = op (eX r) (eY s) := by
  let := q
  have h' := h (abelianPair J K f.inverse A X Y V r s)
  rw [← hX, ← hY, ← hZ] at h'
  simp only [abelianPair, pairSource_fst, pairSource_snd, underlying_hom_inv] at h'
  have hh := abelianPair_bilinear J K f A q hq X Y Z b V r s
  have hh' := congrArg (fun w ↦ eZ ((A.underlying.inv.app Z).hom.app V w)) hh
  rw [underlying_hom_inv] at hh'
  exact hh'.trans h'

private def sectionModuleIso (R₀ : Sheaf K RingCat.{u})
    (M N : SheafOfModules.{u} R₀)
    (e : sets K ((SheafOfModules.toSheaf R₀).obj M) ≅
      sets K ((SheafOfModules.toSheaf R₀).obj N))
    (ha : ∀ (V : Dᵒᵖ) (x y : M.val.obj V),
      e.hom.hom.app V (x + y) =
        @id (N.val.obj V) (e.hom.hom.app V x) + @id (N.val.obj V) (e.hom.hom.app V y))
    (hs : ∀ (V : Dᵒᵖ) (r : R₀.obj.obj V) (x : M.val.obj V),
      e.hom.hom.app V (r • x) = r • @id (N.val.obj V) (e.hom.hom.app V x)) : M ≅ N := by
  let lm (V : Dᵒᵖ) : M.val.obj V →ₗ[R₀.obj.obj V] N.val.obj V :=
    { toFun := fun x ↦ e.hom.hom.app V x
      map_add' := ha V
      map_smul' := hs V }
  let p : M.val ≅ N.val :=
    PresheafOfModules.isoMk
      (fun V ↦ (LinearEquiv.ofBijective (lm V)
        (ConcreteCategory.bijective_of_isIso (e.hom.hom.app V))).toModuleIso)
      (by
        intro V W g
        ext x
        exact congrArg (fun k ↦ k x) (e.hom.hom.naturality g))
  exact
    { hom := ⟨p.hom⟩
      inv := ⟨p.inv⟩
      hom_inv_id := SheafOfModules.hom_ext p.hom_inv_id
      inv_hom_id := SheafOfModules.hom_ext p.inv_hom_id }

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 600000 in
-- Elaborate the reconstructed ring/module structures and their componentwise comparisons.
private theorem comparison_of_normalization [A.functor.PreservesZeroMorphisms]
    (q : A.functor.Braided)
    (hq : TensorNormalization J K f.inverse A q.toMonoidal.toLaxMonoidal) :
    ComparisonStatement J K f A q := by
  let := q
  have : UnivLE.{uD, u} :=
    @UnivLE.trans.{uD, max uD vD, u} univLE_max inferInstance
  have : UnivLE.{vD, u} :=
    @UnivLE.trans.{vD, max uD vD, u} univLE_max inferInstance
  let : EssentiallySmall.{u} D := inferInstance
  let (X : Dᵒᵖ) :
      HasLimitsOfShape (StructuredArrow X (equivSmallModel.{u} D).inverse.op)
        AddCommGrpCat.{u} := HasLimitsOfShape.of_small.{u, u} AddCommGrpCat.{u} _
  have : K.WEqualsLocallyBijective AddCommGrpCat.{u} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{vD, u, uD, u + 1, u, u, u}
      K (A := AddCommGrpCat.{u})
  dsimp only [ComparisonStatement]
  intro R _ _ RI I
  have hUL (X : Sheaf J AddCommGrpCat.{u}) : IsIso (underlyingULift J X) := by
    unfold underlyingULift
    exact ⟨⟨(sheafCompose_map J
      (Functor.whiskerLeft (forget AddCommGrpCat.{u}) uliftFunctorTrivial.hom)).app X,
      by ext V x; rfl, by ext V x; rfl⟩⟩
  let e : sets K (A.functor.obj R) ≅
      (sheafCompose K (forget CommRingCat.{u})).obj RI :=
    A.underlying.app R ≪≫ f.inverse.mapIso (asIso (underlyingULift J R)) ≪≫
      I.ringUnderlying ≪≫
        { hom := (sheafCompose_map K
          (Functor.whiskerLeft (forget CommRingCat.{u}) uliftFunctorTrivial.hom)).app RI
          inv := (sheafCompose_map K
          (Functor.whiskerLeft (forget CommRingCat.{u}) uliftFunctorTrivial.inv)).app RI
          hom_inv_id := by ext V x; rfl
          inv_hom_id := by ext V x; rfl }
  have he (V : Dᵒᵖ) (r : (A.functor.obj R).obj.obj V) :
      ULift.up (e.hom.hom.app V r) =
        I.ringUnderlying.hom.hom.app V
          ((f.inverse.map (underlyingULift J R)).hom.app V
            ((A.underlying.hom.app R).hom.app V r)) := rfl
  have hm : PreservesFiniteLimits f.inverse := f.leftExact
  have ev (V : Dᵒᵖ) (w : (f.inverse.obj (sets J R)).obj.obj V) :
      e.hom.hom.app V ((A.underlying.inv.app R).hom.app V w) =
        (I.ringUnderlying.hom.hom.app V
          ((f.inverse.map (underlyingULift J R)).hom.app V w)).down := by
    change (I.ringUnderlying.hom.hom.app V
      ((f.inverse.map (underlyingULift J R)).hom.app V
        ((A.underlying.hom.app R).hom.app V
          ((A.underlying.inv.app R).hom.app V w)))).down = _
    rw [underlying_inv_hom]
  have eadd (V : Dᵒᵖ) (r s : (A.functor.obj R).obj.obj V) :
      e.hom.hom.app V (r + s) = @id (RI.obj.obj V) (e.hom.hom.app V r) +
        @id (RI.obj.obj V) (e.hom.hom.app V s) := by
    apply graph_compare_add J K f A R V (N := RI.obj.obj V) (e.hom.hom.app V)
      (fun w ↦ (I.ringUnderlying.hom.hom.app V
        ((f.inverse.map (underlyingULift J R)).hom.app V w)).down) (ev V)
    intro z
    let a := CartesianMonoidalCategory.fst (sets J R) (sets J R) ≫ underlyingULift J R
    let b := CartesianMonoidalCategory.snd (sets J R) (sets J R) ≫ underlyingULift J R
    let t := addGraph J R ≫ underlyingULift J R
    have h := I.ringAdd (sets J R ⊗ sets J R) a b t (fun _ _ => rfl) V z
    change (I.ringUnderlying.hom.hom.app V
      ((f.inverse.map t).hom.app V z)).down =
        (I.ringUnderlying.hom.hom.app V ((f.inverse.map a).hom.app V z)).down +
        (I.ringUnderlying.hom.hom.app V ((f.inverse.map b).hom.app V z)).down at h
    dsimp only [a, b, t] at h
    simp only [Functor.map_comp] at h
    change (I.ringUnderlying.hom.hom.app V
      ((f.inverse.map (underlyingULift J R)).hom.app V
        ((f.inverse.map (addGraph J R)).hom.app V z))).down =
      (I.ringUnderlying.hom.hom.app V
        ((f.inverse.map (underlyingULift J R)).hom.app V
          ((f.inverse.map (CartesianMonoidalCategory.fst _ _)).hom.app V z))).down +
      (I.ringUnderlying.hom.hom.app V
        ((f.inverse.map (underlyingULift J R)).hom.app V
          ((f.inverse.map (CartesianMonoidalCategory.snd _ _)).hom.app V z))).down at h
    exact h
  have emul (V : Dᵒᵖ)
      (r s : (InternalAbelianSheafModule.sectionRingSheaf K (A.functor.obj R)).obj.obj V) :
      e.hom.hom.app V (r * s) = @id (RI.obj.obj V) (e.hom.hom.app V r) *
        @id (RI.obj.obj V) (e.hom.hom.app V s) := by
    apply graph_compare_bilinear J K f A _ hq R R R (MonObj.mul (X := R)) V
      (N := RI.obj.obj V) (P := RI.obj.obj V) (Q := RI.obj.obj V)
      (e.hom.hom.app V) (e.hom.hom.app V) (e.hom.hom.app V)
      (fun w ↦ (I.ringUnderlying.hom.hom.app V
        ((f.inverse.map (underlyingULift J R)).hom.app V w)).down)
      (fun w ↦ (I.ringUnderlying.hom.hom.app V
        ((f.inverse.map (underlyingULift J R)).hom.app V w)).down)
      (fun w ↦ (I.ringUnderlying.hom.hom.app V
        ((f.inverse.map (underlyingULift J R)).hom.app V w)).down)
      (ev V) (ev V) (ev V) (fun r s ↦ r * s)
    intro z
    let a := CartesianMonoidalCategory.fst (sets J R) (sets J R) ≫ underlyingULift J R
    let b := CartesianMonoidalCategory.snd (sets J R) (sets J R) ≫ underlyingULift J R
    let t := pairingGraph J R R ≫
      (sheafCompose J (forget AddCommGrpCat.{u})).map (MonObj.mul (X := R)) ≫ underlyingULift J R
    have h := I.ringMul (sets J R ⊗ sets J R) a b t (fun _ _ => rfl) V z
    change (I.ringUnderlying.hom.hom.app V ((f.inverse.map t).hom.app V z)).down =
      (I.ringUnderlying.hom.hom.app V ((f.inverse.map a).hom.app V z)).down *
        (I.ringUnderlying.hom.hom.app V ((f.inverse.map b).hom.app V z)).down at h
    have ht : t = (pairingGraph J R R ≫
        (sheafCompose J (forget AddCommGrpCat.{u})).map (MonObj.mul (X := R))) ≫
        underlyingULift J R :=
      (Category.assoc _ _ _).symm
    rw [ht] at h
    dsimp only [a, b] at h
    simp only [Functor.map_comp] at h
    change (I.ringUnderlying.hom.hom.app V
      ((f.inverse.map (underlyingULift J R)).hom.app V
        ((f.inverse.map ((sheafCompose J (forget AddCommGrpCat.{u})).map
          (MonObj.mul (X := R)))).hom.app V
          ((f.inverse.map (pairingGraph J R R)).hom.app V z)))).down =
      (I.ringUnderlying.hom.hom.app V
        ((f.inverse.map (underlyingULift J R)).hom.app V
          ((f.inverse.map (CartesianMonoidalCategory.fst _ _)).hom.app V z))).down *
      (I.ringUnderlying.hom.hom.app V
        ((f.inverse.map (underlyingULift J R)).hom.app V
          ((f.inverse.map (CartesianMonoidalCategory.snd _ _)).hom.app V z))).down at h
    simpa only [Functor.map_comp, ObjectProperty.FullSubcategory.comp_hom,
      NatTrans.comp_app, types_comp_apply, id_eq] using h
  have eone (V : Dᵒᵖ) :
      e.hom.hom.app V
        (1 : (InternalAbelianSheafModule.sectionRingSheaf K (A.functor.obj R)).obj.obj V) =
        (1 : RI.obj.obj V) := by
    let t := (oneGraph J ≫
      (sheafCompose J (forget AddCommGrpCat.{u})).map (MonObj.one (X := R))) ≫ underlyingULift J R
    have h := I.ringOne _ t (fun _ _ => rfl) V (terminalSource J K f.inverse V)
    change (I.ringUnderlying.hom.hom.app V
      ((f.inverse.map t).hom.app V (terminalSource J K f.inverse V))).down = 1 at h
    dsimp only [t] at h
    rw [Functor.map_comp] at h
    change (I.ringUnderlying.hom.hom.app V
      ((f.inverse.map (underlyingULift J R)).hom.app V
        ((f.inverse.map (oneGraph J ≫
          (sheafCompose J (forget AddCommGrpCat.{u})).map (MonObj.one (X := R)))).hom.app V
          (terminalSource J K f.inverse V)))).down = 1 at h
    rw [← ev V, ← terminalSource_one J K f A _ hq, underlying_hom_inv] at h
    exact h
  let S := InternalAbelianSheafModule.sectionRingSheaf K (A.functor.obj R)
  let σhom : S ⟶ RI :=
    ⟨{ app := fun V => @CommRingCat.ofHom (S.obj.obj V) (RI.obj.obj V) _ _
         (show S.obj.obj V →+* RI.obj.obj V from
           { @AddMonoidHom.mk' (S.obj.obj V) (RI.obj.obj V) _ _
               (fun r => e.hom.hom.app V r) (fun r s => eadd V r s) with
             map_one' := eone V
             map_mul' := emul V })
       naturality := by
         intro V W g
         ext r
         exact congrArg (fun k => k r) (e.hom.hom.naturality g) }⟩
  have hσ : IsIso ((sheafCompose K (forget CommRingCat.{u})).map σhom) :=
    show IsIso e.hom from inferInstance
  have : IsIso σhom := isIso_of_reflects_iso σhom (sheafCompose K (forget CommRingCat.{u}))
  refine ⟨asIso σhom, he, ?_⟩
  let E := (InternalAbelianSheafModule.sectionModuleEquivalence J R).functor
  let F := A.functor.mapMod R ⋙
    (InternalAbelianSheafModule.sectionModuleEquivalence K (A.functor.obj R)).functor
  let G := E ⋙ I.modules ⋙ SheafOfModules.restrictScalars
    ((sheafCompose K (forget₂ CommRingCat RingCat)).map σhom)
  let eM (M : Mod (Sheaf J AddCommGrpCat.{u}) R) :
      sets K (A.functor.obj M.X) ≅
        sets K ((SheafOfModules.toSheaf _).obj (I.modules.obj (E.obj M))) :=
    A.underlying.app M.X ≪≫ f.inverse.mapIso (asIso (underlyingULift J M.X)) ≪≫
      (I.moduleUnderlying.app (E.obj M)).symm ≪≫
        { hom := (sheafCompose_map K
            (Functor.whiskerLeft (forget AddCommGrpCat.{u}) uliftFunctorTrivial.hom)).app _
          inv := (sheafCompose_map K
            (Functor.whiskerLeft (forget AddCommGrpCat.{u}) uliftFunctorTrivial.inv)).app _
          hom_inv_id := by ext V x; rfl
          inv_hom_id := by ext V x; rfl }
  have evM (M : Mod (Sheaf J AddCommGrpCat.{u}) R) (V : Dᵒᵖ)
      (w : (f.inverse.obj (sets J M.X)).obj.obj V) :
      (eM M).hom.hom.app V ((A.underlying.inv.app M.X).hom.app V w) =
        ((I.moduleUnderlying.inv.app (E.obj M)).hom.app V
          ((f.inverse.map (underlyingULift J M.X)).hom.app V w)).down := by
    change ((I.moduleUnderlying.inv.app (E.obj M)).hom.app V
      ((f.inverse.map (underlyingULift J M.X)).hom.app V
        ((A.underlying.hom.app M.X).hom.app V
          ((A.underlying.inv.app M.X).hom.app V w)))).down = _
    rw [underlying_inv_hom]
  have eMadd (M : Mod (Sheaf J AddCommGrpCat.{u}) R) (V : Dᵒᵖ)
      (r s : (A.functor.obj M.X).obj.obj V) :
      (eM M).hom.hom.app V (r + s) =
        @id ((I.modules.obj (E.obj M)).val.obj V) ((eM M).hom.hom.app V r) +
          @id ((I.modules.obj (E.obj M)).val.obj V) ((eM M).hom.hom.app V s) := by
    apply graph_compare_add J K f A M.X V
      (N := (I.modules.obj (E.obj M)).val.obj V) ((eM M).hom.hom.app V)
      (fun w ↦ ((I.moduleUnderlying.inv.app (E.obj M)).hom.app V
        ((f.inverse.map (underlyingULift J M.X)).hom.app V w)).down) (evM M V)
    intro z
    let a := CartesianMonoidalCategory.fst (sets J M.X) (sets J M.X) ≫ underlyingULift J M.X
    let b := CartesianMonoidalCategory.snd (sets J M.X) (sets J M.X) ≫ underlyingULift J M.X
    let t := addGraph J M.X ≫ underlyingULift J M.X
    have h := I.moduleAdd (E.obj M) (sets J M.X ⊗ sets J M.X) a b t
      (fun _ _ => rfl) V z
    change ((I.moduleUnderlying.inv.app (E.obj M)).hom.app V
      ((f.inverse.map t).hom.app V z)).down =
        ((I.moduleUnderlying.inv.app (E.obj M)).hom.app V
          ((f.inverse.map a).hom.app V z)).down +
        ((I.moduleUnderlying.inv.app (E.obj M)).hom.app V
          ((f.inverse.map b).hom.app V z)).down at h
    dsimp only [a, b, t] at h
    simp only [Functor.map_comp] at h
    change ((I.moduleUnderlying.inv.app (E.obj M)).hom.app V
      ((f.inverse.map (underlyingULift J M.X)).hom.app V
        ((f.inverse.map (addGraph J M.X)).hom.app V z))).down =
      ((I.moduleUnderlying.inv.app (E.obj M)).hom.app V
        ((f.inverse.map (underlyingULift J M.X)).hom.app V
          ((f.inverse.map (CartesianMonoidalCategory.fst _ _)).hom.app V z))).down +
      ((I.moduleUnderlying.inv.app (E.obj M)).hom.app V
        ((f.inverse.map (underlyingULift J M.X)).hom.app V
          ((f.inverse.map (CartesianMonoidalCategory.snd _ _)).hom.app V z))).down at h
    exact h
  have eMsmul (M : Mod (Sheaf J AddCommGrpCat.{u}) R) (V : Dᵒᵖ)
      (r : S.obj.obj V) (x : (F.obj M).val.obj V) :
      (eM M).hom.hom.app V (r • x) =
        @id (RI.obj.obj V) (e.hom.hom.app V r) •
          @id ((I.modules.obj (E.obj M)).val.obj V) ((eM M).hom.hom.app V x) := by
    apply graph_compare_bilinear J K f A _ hq R M.X M.X (Mod.act M.X) V
      (N := RI.obj.obj V) (P := (I.modules.obj (E.obj M)).val.obj V)
      (Q := (I.modules.obj (E.obj M)).val.obj V)
      (e.hom.hom.app V) ((eM M).hom.hom.app V) ((eM M).hom.hom.app V)
      (fun w ↦ (I.ringUnderlying.hom.hom.app V
        ((f.inverse.map (underlyingULift J R)).hom.app V w)).down)
      (fun w ↦ ((I.moduleUnderlying.inv.app (E.obj M)).hom.app V
        ((f.inverse.map (underlyingULift J M.X)).hom.app V w)).down)
      (fun w ↦ ((I.moduleUnderlying.inv.app (E.obj M)).hom.app V
        ((f.inverse.map (underlyingULift J M.X)).hom.app V w)).down)
      (ev V) (evM M V) (evM M V) (fun r x ↦ r • x)
    intro z
    let a := CartesianMonoidalCategory.fst (sets J R) (sets J M.X) ≫ underlyingULift J R
    let b := CartesianMonoidalCategory.snd (sets J R) (sets J M.X) ≫ underlyingULift J M.X
    let t := (pairingGraph J R M.X ≫
      (sheafCompose J (forget AddCommGrpCat.{u})).map (Mod.act M.X)) ≫ underlyingULift J M.X
    have h := I.moduleSMul (E.obj M) (sets J R ⊗ sets J M.X) a b t
      (fun _ _ => rfl) V z
    dsimp only [a, b, t] at h
    simp only [Functor.map_comp] at h
    change ((I.moduleUnderlying.inv.app (E.obj M)).hom.app V
      ((f.inverse.map (underlyingULift J M.X)).hom.app V
        ((f.inverse.map ((sheafCompose J (forget AddCommGrpCat.{u})).map
          (Mod.act M.X))).hom.app V ((f.inverse.map (pairingGraph J R M.X)).hom.app V z)))).down =
      @id (RI.obj.obj V) ((I.ringUnderlying.hom.hom.app V
        ((f.inverse.map (underlyingULift J R)).hom.app V
          ((f.inverse.map (CartesianMonoidalCategory.fst _ _)).hom.app V z))).down) •
      @id ((I.modules.obj (E.obj M)).val.obj V)
        (((I.moduleUnderlying.inv.app (E.obj M)).hom.app V
        ((f.inverse.map (underlyingULift J M.X)).hom.app V
          ((f.inverse.map (CartesianMonoidalCategory.snd _ _)).hom.app V z))).down) at h
    simpa only [Functor.map_comp, ObjectProperty.FullSubcategory.comp_hom,
      NatTrans.comp_app, types_comp_apply, id_eq] using h
  let θM (M : Mod (Sheaf J AddCommGrpCat.{u}) R) : F.obj M ≅ G.obj M :=
    sectionModuleIso K _ (F.obj M) (G.obj M) (eM M) (eMadd M) (eMsmul M)
  have hnat {M N : Mod (Sheaf J AddCommGrpCat.{u}) R} (h : M ⟶ N) :
      F.map h ≫ (θM N).hom = (θM M).hom ≫ G.map h := by
    have hA : CommSq _ _ _ _ := ⟨A.underlying.hom.naturality h.hom⟩
    have hU := f.inverse.map_commSq
      (show CommSq _ _ _ _ from ⟨(sheafCompose_map J
        (Functor.whiskerLeft (forget AddCommGrpCat.{u})
          uliftFunctorTrivial.inv)).naturality h.hom⟩)
    have hI : CommSq _ _ _ _ := ⟨I.moduleUnderlying.inv.naturality (E.map h)⟩
    have hD : CommSq _ _ _ _ := ⟨(sheafCompose_map K
      (Functor.whiskerLeft (forget AddCommGrpCat.{u})
        uliftFunctorTrivial.hom)).naturality
        ((SheafOfModules.toSheaf _).map (I.modules.map (E.map h)))⟩
    have hs := ((hA.vert_comp hU).vert_comp hI).vert_comp hD
    ext V x
    exact congrArg (fun k => k.hom.app V x) hs.w
  let θ : F ≅ G := NatIso.ofComponents θM hnat
  refine ⟨θ, ?_, ?_⟩
  · intro M V x
    change (I.moduleUnderlying.hom.app (E.obj M)).hom.app V
      (ULift.up ((eM M).hom.hom.app V x)) = _
    change (I.moduleUnderlying.hom.app (E.obj M)).hom.app V
      ((I.moduleUnderlying.inv.app (E.obj M)).hom.app V
        ((f.inverse.map (underlyingULift J M.X)).hom.app V
          ((A.underlying.hom.app M.X).hom.app V x))) = _
    exact congrArg (fun k => k.hom.app V
      ((f.inverse.map (underlyingULift J M.X)).hom.app V
        ((A.underlying.hom.app M.X).hom.app V x)))
      (I.moduleUnderlying.inv_hom_id_app (E.obj M))
  · have hF : F.PreservesZeroMorphisms :=
      ⟨fun M N => by
        ext V x
        exact congrArg (fun k => (k.hom.app V).hom x)
          (A.functor.map_zero M.X N.X)⟩
    exact complexComparison_of_iso F G θ hF

/-- Internal tensor-module inverse image agrees canonically with finite-product
inverse image of sectionwise modules, also on unbounded complexes and their derived
images. No flatness, boundedness, resolutions or enough-points hypotheses occur.
Source: Stacks 03D2, 03EK, 03EL, 00YV and 05RR; blueprint parent inverse-image
identification (blueprint: lem-sfb-internal-module-inverse-image-comparison).

Proof, following all six steps of the node.
1. The unique direct lax structure is directLax_existsUnique, from the universal
bilinear pairing and the integer section 1 (sheaf tensor universal property).
2--3. inverseBraided_existsUnique identifies its oplax mate under the lifted
adjunction, proves its tensor and unit invertible by the SET-adjunction injectivity,
and identifies their inverses with inverse image of the pairing and 1.
4. For b : R tensor R to R and v : Z to R, transport gives L(b) mu and L(v) epsilon.
Precomposing with the universal pairing and 1 identifies these with finite-product
transport of section multiplication and one. Addition and zero are those of A.
Thus the fixed underlying comparison defines σ and its inverse as ring-sheaf maps.
5. For an action gamma, the same computation gives L(gamma) mu p = L(gamma p) lambda^{-1}.
The fixed underlying comparison is therefore additive and σ-semilinear in both
directions; this defines θ. Both functors map a morphism h to L(h), proving naturality.
6. Apply θ in every integer degree. Naturality at every differential proves the
chain-map equations, for unbounded complexes too. The inverses give a natural
isomorphism of complexes. Localization Q sends these inverse chain maps to inverse
maps in the derived category; the displayed derived normalization specifies exactly
that image. No preservation claim for arbitrary quasi-isomorphisms is needed. -/
theorem internalModuleInverseImageComparison :
    (inverseBraided J K f A B adj unit_eq).toMonoidal.toOplaxMonoidal =
        inverseOplax J K f A B adj ∧
    TensorNormalization J K f.inverse A
      (inverseBraided J K f A B adj unit_eq).toMonoidal.toLaxMonoidal ∧
    ComparisonStatement J K f A (inverseBraided J K f A B adj unit_eq) := by
  have h := (Classical.choose_spec (inverseBraided_existsUnique J K f A B adj unit_eq)).1
  have : A.functor.IsLeftAdjoint := adj.isLeftAdjoint
  exact ⟨h.1, h.2, comparison_of_normalization J K f A _ h.2⟩

end CategoryTheory.InternalModuleInverseImage
