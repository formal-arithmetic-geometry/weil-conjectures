/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import WeilConjectures.CategoryTheory.ObjectProperty.Duality

/-!
# Duality into an invertible object

Let `C` be a monoidal closed category, `T` an invertible object and `γ : T ≅ W` an isomorphism.
The contravariant functor `[-, W]` is then the coefficient dual `[-, 𝟙_ C]` twisted by `T`:
```
  θ_X : [X, W] ≅ [X, T] ≅ [X, 𝟙_ C ⊗ T] ≅ [X, 𝟙_ C] ⊗ T,
```
the first arrow being `[X, γ⁻¹]` and the last the inverse of the canonical map
`[X, 𝟙_ C] ⊗ T ⟶ [X, 𝟙_ C ⊗ T]`, an isomorphism since `T` is invertible
(`CategoryTheory.MonoidalClosed.isIso_ihomTensorToIhom`). This is the formal core of the
blueprint theorem `sk-thm-sf-dual-perfect`: an orientation `γ : Λ_X(d)[2d] ≅ ω_X` identifies
the Verdier dual `𝔻_X = RHom(-, ω_X)` with `K ↦ K^∨(d)[2d]`.

If `C` is moreover braided, the double-dual map `X ⟶ [[X, W], W]` is identified, under `θ`, with
the coefficient biduality `X ⟶ [[X, 𝟙_ C], 𝟙_ C]`. Hence it is an isomorphism for every
dualizable `X`, and `[-, W]` restricts to an anti-equivalence of the dualizable objects.

## Main definitions

- `CategoryTheory.MonoidalClosed.ihomIsoIhomUnitTensor`: `θ_X : [X, W] ≅ [X, 𝟙_ C] ⊗ T`.
- `CategoryTheory.MonoidalClosed.ihomFlipIsoIhomUnitTensor`: `θ` as a natural isomorphism
  `[-, W] ≅ [-, 𝟙_ C] ⊗ T`.
- `CategoryTheory.MonoidalClosed.ihomUnitToIhomTensor`: the isomorphism
  `[A, 𝟙_ C] ⟶ [A ⊗ T, T]` for an invertible `T`.
- `CategoryTheory.MonoidalClosed.ihomIhomIsoIhomIhomUnit`: the isomorphism
  `[[X, W], W] ≅ [[X, 𝟙_ C], 𝟙_ C]` induced by `θ_X`.
- `CategoryTheory.MonoidalClosed.dualizableIhomEquivalence`: the anti-equivalence of the
  dualizable objects given by `[-, W]`.

## Main statements

- `CategoryTheory.MonoidalClosed.whiskerLeft_ihomIsoIhomUnitTensor_hom_comp`: `θ` is compatible
  with the evaluations `X ⊗ [X, W] ⟶ W` and `X ⊗ [X, 𝟙_ C] ⟶ 𝟙_ C`.
- `CategoryTheory.MonoidalClosed.toIhomIhom_comp_ihomIhomIsoIhomIhomUnit_hom`: under `θ` the
  double-dual map into `[[X, W], W]` is the coefficient biduality.
- `CategoryTheory.MonoidalClosed.isIso_toIhomIhom_of_isDualizable`: biduality relative to `W`
  holds for every dualizable object.
-/

@[expose] public section

namespace CategoryTheory.MonoidalClosed

open MonoidalCategory Opposite

variable {C : Type*} [Category* C] [MonoidalCategory C] [MonoidalClosed C]

/-- The canonical map `[X, Z] ⊗ N ⟶ [X, Z ⊗ N]` is natural in `X`. -/
@[reassoc]
lemma pre_app_whiskerRight_comp_ihomTensorToIhom {X Y : C} (f : X ⟶ Y) (Z N : C) :
    (pre f).app Z ▷ N ≫ ihomTensorToIhom X Z N =
      ihomTensorToIhom Y Z N ≫ (pre f).app (Z ⊗ N) := by
  apply uncurry_injective
  rw [uncurry_whiskerRight_comp_ihomTensorToIhom, uncurry_pre_app, uncurry_pre,
    ihomTensorToIhom, uncurry_curry, associator_inv_naturality_left_assoc, comp_whiskerRight]

section Twist

variable {T W : C} (γ : T ≅ W) (hT : IsInvertible T)

/-- Duality into an object `W` isomorphic to an invertible object `T` is the coefficient dual
twisted by `T`:
```
  θ_X : [X, W] ≅ [X, T] ≅ [X, 𝟙_ C ⊗ T] ≅ [X, 𝟙_ C] ⊗ T,
```
the composite of `[X, γ⁻¹]`, of the left unitor and of the inverse of the canonical map
`[X, 𝟙_ C] ⊗ T ⟶ [X, 𝟙_ C ⊗ T]` (`CategoryTheory.MonoidalClosed.isIso_ihomTensorToIhom`). -/
noncomputable def ihomIsoIhomUnitTensor (X : C) : (ihom X).obj W ≅ (ihom X).obj (𝟙_ C) ⊗ T :=
  haveI := isIso_ihomTensorToIhom X (𝟙_ C) hT
  (ihom X).mapIso γ.symm ≪≫ (ihom X).mapIso (λ_ T).symm ≪≫
    (asIso (ihomTensorToIhom X (𝟙_ C) T)).symm

lemma ihomIsoIhomUnitTensor_inv (X : C) :
    (ihomIsoIhomUnitTensor γ hT X).inv =
      ihomTensorToIhom X (𝟙_ C) T ≫ (ihom X).map (λ_ T).hom ≫ (ihom X).map γ.hom := by
  simp [ihomIsoIhomUnitTensor]

/-- The isomorphism `θ_X : [X, W] ≅ [X, 𝟙_ C] ⊗ T` is natural in `X`. -/
@[reassoc]
lemma pre_app_comp_ihomIsoIhomUnitTensor_hom {X Y : C} (f : X ⟶ Y) :
    (pre f).app W ≫ (ihomIsoIhomUnitTensor γ hT X).hom =
      (ihomIsoIhomUnitTensor γ hT Y).hom ≫ (pre f).app (𝟙_ C) ▷ T := by
  rw [← cancel_epi (ihomIsoIhomUnitTensor γ hT Y).inv, Iso.inv_hom_id_assoc,
    ← cancel_mono (ihomIsoIhomUnitTensor γ hT X).inv, Category.assoc, Category.assoc,
    Iso.hom_inv_id, Category.comp_id, ihomIsoIhomUnitTensor_inv, ihomIsoIhomUnitTensor_inv,
    pre_app_whiskerRight_comp_ihomTensorToIhom_assoc]
  simp only [Category.assoc, NatTrans.naturality, NatTrans.naturality_assoc]

/-- Duality into an object `W` isomorphic to an invertible object `T` is the coefficient dual
twisted by `T`: the natural isomorphism `θ : [-, W] ≅ [-, 𝟙_ C] ⊗ T` of contravariant functors
with components `CategoryTheory.MonoidalClosed.ihomIsoIhomUnitTensor`. -/
noncomputable def ihomFlipIsoIhomUnitTensor :
    internalHom.flip.obj W ≅ internalHom.flip.obj (𝟙_ C) ⋙ tensorRight T :=
  NatIso.ofComponents (fun X ↦ ihomIsoIhomUnitTensor γ hT X.unop)
    (fun f ↦ pre_app_comp_ihomIsoIhomUnitTensor_hom γ hT f.unop)

@[simp]
lemma ihomFlipIsoIhomUnitTensor_app (X : Cᵒᵖ) :
    (ihomFlipIsoIhomUnitTensor γ hT).app X = ihomIsoIhomUnitTensor γ hT X.unop :=
  rfl

/-- The isomorphism `θ_X : [X, W] ≅ [X, 𝟙_ C] ⊗ T` is compatible with the evaluations: the
square
```
  X ⊗ [X, W] ────── X ◁ θ_X ──────→ X ⊗ ([X, 𝟙_ C] ⊗ T)
       │                                   │
       ev                         α⁻¹, ev ▷ T, λ
       ↓                                   ↓
       W ─────────────── γ⁻¹ ─────────────→ T
```
commutes. -/
@[reassoc]
lemma whiskerLeft_ihomIsoIhomUnitTensor_hom_comp (X : C) :
    X ◁ (ihomIsoIhomUnitTensor γ hT X).hom ≫ (α_ _ _ _).inv ≫
        (ihom.ev X).app (𝟙_ C) ▷ T ≫ (λ_ T).hom =
      (ihom.ev X).app W ≫ γ.inv := by
  rw [← reassoc_of% (whiskerLeft_ihomTensorToIhom_ev X (𝟙_ C) T),
    ← MonoidalCategory.whiskerLeft_comp_assoc]
  have : (ihomIsoIhomUnitTensor γ hT X).hom ≫ ihomTensorToIhom X (𝟙_ C) T =
      (ihom X).map γ.inv ≫ (ihom X).map (λ_ T).inv := by
    simp [ihomIsoIhomUnitTensor]
  rw [this, MonoidalCategory.whiskerLeft_comp_assoc, ihom.ev_naturality_assoc,
    ihom.ev_naturality_assoc, Iso.inv_hom_id, Category.comp_id]

/-- The compatibility of `θ_X` with the evaluations, read along `θ_X⁻¹`. -/
@[reassoc]
lemma whiskerLeft_ihomIsoIhomUnitTensor_inv_comp (X : C) :
    X ◁ (ihomIsoIhomUnitTensor γ hT X).inv ≫ (ihom.ev X).app W ≫ γ.inv =
      (α_ _ _ _).inv ≫ (ihom.ev X).app (𝟙_ C) ▷ T ≫ (λ_ T).hom := by
  rw [← whiskerLeft_ihomIsoIhomUnitTensor_hom_comp γ hT X,
    ← MonoidalCategory.whiskerLeft_comp_assoc, Iso.inv_hom_id, MonoidalCategory.whiskerLeft_id,
    Category.id_comp]

end Twist

section Braided

variable [BraidedCategory C]

/-- The map `[A, 𝟙_ C] ⟶ [A ⊗ T, T]`: the transpose of
```
                α, A ◁ β, α⁻¹                     ev ▷ T              λ
  (A ⊗ T) ⊗ [A, 𝟙_ C] ──────────→ (A ⊗ [A, 𝟙_ C]) ⊗ T ──────→ 𝟙_ C ⊗ T ──→ T.
```
It is an isomorphism for an invertible `T`
(`CategoryTheory.MonoidalClosed.isIso_ihomUnitToIhomTensor`). -/
noncomputable def ihomUnitToIhomTensor (A T : C) :
    (ihom A).obj (𝟙_ C) ⟶ (ihom (A ⊗ T)).obj T :=
  curry ((α_ A T _).hom ≫ A ◁ (β_ T _).hom ≫ (α_ A _ T).inv ≫
    (ihom.ev A).app (𝟙_ C) ▷ T ≫ (λ_ T).hom)

lemma uncurry_comp_ihomUnitToIhomTensor {A T Z : C} (x : Z ⟶ (ihom A).obj (𝟙_ C)) :
    uncurry (x ≫ ihomUnitToIhomTensor A T) =
      (α_ A T Z).hom ≫ A ◁ (β_ T Z).hom ≫ (α_ A Z T).inv ≫ uncurry x ▷ T ≫ (λ_ T).hom := by
  rw [uncurry_natural_left, ihomUnitToIhomTensor, uncurry_curry, uncurry_eq x,
    associator_naturality_right_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc,
    BraidedCategory.braiding_naturality_right, MonoidalCategory.whiskerLeft_comp_assoc,
    associator_inv_naturality_middle_assoc, comp_whiskerRight_assoc]

/-- For an invertible `T` the map `[A, 𝟙_ C] ⟶ [A ⊗ T, T]` is an isomorphism: both sides
corepresent `Z ↦ (A ⊗ Z ⟶ 𝟙_ C)`, since `- ⊗ T` is an autoequivalence. -/
theorem isIso_ihomUnitToIhomTensor (A : C) {T : C} (hT : IsInvertible T) :
    IsIso (ihomUnitToIhomTensor A T) := by
  obtain ⟨T', ⟨e⟩, ⟨e'⟩⟩ := hT
  let E := tensorRightEquivalenceOfTensorIso e e'
  let ι (Z : C) : (A ⊗ T) ⊗ Z ≅ (A ⊗ Z) ⊗ T :=
    α_ A T Z ≪≫ whiskerLeftIso A (β_ T Z) ≪≫ (α_ A Z T).symm
  have key {Z : C} (x : Z ⟶ (ihom A).obj (𝟙_ C)) :
      uncurry (x ≫ ihomUnitToIhomTensor A T) = (ι Z).hom ≫ uncurry x ▷ T ≫ (λ_ T).hom := by
    rw [uncurry_comp_ihomUnitToIhomTensor]
    simp [ι]
  refine isIso_of_yoneda_map_bijective _ (fun Z ↦ ⟨fun x x' h ↦ ?_, fun g ↦ ?_⟩)
  · have h' := congrArg uncurry h
    dsimp only at h'
    rw [key, key, cancel_epi, cancel_mono] at h'
    exact uncurry_injective (whiskerRight_injective_of_tensorIso e h')
  · let b : A ⊗ Z ⟶ 𝟙_ C := E.functor.preimage ((ι Z).inv ≫ uncurry g ≫ (λ_ T).inv)
    have hb : b ▷ T = (ι Z).inv ≫ uncurry g ≫ (λ_ T).inv := E.functor.map_preimage _
    refine ⟨curry b, uncurry_injective ?_⟩
    dsimp only
    rw [key, uncurry_curry, hb]
    simp

variable {T W : C} (γ : T ≅ W) (hT : IsInvertible T)

/-- Under `θ_X : [X, W] ≅ [X, 𝟙_ C] ⊗ T` the double-dual map into `[[X, W], W]` is the
coefficient biduality: the square
```
         X ────────────── toIhomIhomUnit X ──────────────→ [[X, 𝟙_ C], 𝟙_ C]
         │                                                          │
  toIhomIhom W X                                    ihomUnitToIhomTensor _ T
         ↓                                                          ↓
  [[X, W], W] ── [θ_X⁻¹, W] ──→ [[X, 𝟙_ C] ⊗ T, W] ── [_, γ⁻¹] ──→ [[X, 𝟙_ C] ⊗ T, T]
```
commutes. -/
@[reassoc]
lemma toIhomIhom_comp_pre_app_comp_map (X : C) :
    toIhomIhom W X ≫ (pre (ihomIsoIhomUnitTensor γ hT X).inv).app W ≫
        (ihom ((ihom X).obj (𝟙_ C) ⊗ T)).map γ.inv =
      toIhomIhomUnit X ≫ ihomUnitToIhomTensor ((ihom X).obj (𝟙_ C)) T := by
  apply uncurry_injective
  rw [← Category.assoc, uncurry_natural_right, uncurry_pre_app, uncurry_toIhomIhom,
    uncurry_comp_ihomUnitToIhomTensor,
    ← toIhomIhom_unit, uncurry_toIhomIhom, Category.assoc, Category.assoc,
    BraidedCategory.braiding_naturality_left_assoc, whiskerLeft_ihomIsoIhomUnitTensor_inv_comp,
    BraidedCategory.braiding_tensor_left_hom]
  simp

/-- The isomorphism `[[X, W], W] ≅ [[X, 𝟙_ C], 𝟙_ C]` induced by
`θ_X : [X, W] ≅ [X, 𝟙_ C] ⊗ T`:
```
  [[X, W], W] ≅ [[X, 𝟙_ C] ⊗ T, W] ≅ [[X, 𝟙_ C] ⊗ T, T] ≅ [[X, 𝟙_ C], 𝟙_ C],
```
the composite of `[θ_X⁻¹, W]`, of `[_, γ⁻¹]` and of the inverse of
`CategoryTheory.MonoidalClosed.ihomUnitToIhomTensor`. -/
noncomputable def ihomIhomIsoIhomIhomUnit (X : C) :
    (ihom ((ihom X).obj W)).obj W ≅ (ihom ((ihom X).obj (𝟙_ C))).obj (𝟙_ C) :=
  haveI := isIso_ihomUnitToIhomTensor ((ihom X).obj (𝟙_ C)) hT
  ((internalHom.flip.obj W).mapIso (ihomIsoIhomUnitTensor γ hT X).op).symm ≪≫
    (ihom _).mapIso γ.symm ≪≫ (asIso (ihomUnitToIhomTensor ((ihom X).obj (𝟙_ C)) T)).symm

/-- Under the isomorphism `[[X, W], W] ≅ [[X, 𝟙_ C], 𝟙_ C]` induced by `θ_X`, the double-dual
map `X ⟶ [[X, W], W]` is the coefficient biduality `X ⟶ [[X, 𝟙_ C], 𝟙_ C]`. -/
@[reassoc (attr := simp)]
lemma toIhomIhom_comp_ihomIhomIsoIhomIhomUnit_hom (X : C) :
    toIhomIhom W X ≫ (ihomIhomIsoIhomIhomUnit γ hT X).hom = toIhomIhomUnit X := by
  have h := toIhomIhom_comp_pre_app_comp_map γ hT X
  simp only [ihomIhomIsoIhomIhomUnit, Iso.trans_hom, Iso.symm_hom, asIso_inv, Functor.mapIso_inv,
    Functor.mapIso_hom, Iso.op_inv]
  change toIhomIhom W X ≫ (pre (ihomIsoIhomUnitTensor γ hT X).inv).app W ≫ _ ≫ _ = _
  rw [reassoc_of% h]
  simp

include γ hT in
/-- Duality into an object `W` isomorphic to an invertible object `T` preserves dualizable
objects: `[X, W] ≅ [X, 𝟙_ C] ⊗ T` is dualizable for a dualizable `X`. -/
theorem isDualizable_ihom_obj {X : C} (hX : IsDualizable X) :
    IsDualizable ((ihom X).obj W) :=
  (hX.ihom_unit.tensorObj hT.isDualizable).of_iso (ihomIsoIhomUnitTensor γ hT X).symm

include γ hT in
/-- Biduality relative to an object `W` isomorphic to an invertible object: for a dualizable
`X` the double-dual map `X ⟶ [[X, W], W]` is an isomorphism. -/
theorem isIso_toIhomIhom_of_isDualizable {X : C} (hX : IsDualizable X) :
    IsIso (toIhomIhom W X) := by
  obtain ⟨_⟩ := hX
  have := isIso_toIhomIhomUnit X
  rw [← toIhomIhom_comp_ihomIhomIsoIhomIhomUnit_hom γ hT X] at this
  exact IsIso.of_isIso_comp_right _ (ihomIhomIsoIhomIhomUnit γ hT X).hom

/-- Duality into an object `W` isomorphic to an invertible object restricts to an
anti-equivalence of the dualizable objects, with quasi-inverse itself: the unit and the counit
are the double-dual isomorphisms `X ≅ [[X, W], W]`
(`CategoryTheory.MonoidalClosed.isIso_toIhomIhom_of_isDualizable`). -/
noncomputable def dualizableIhomEquivalence :
    (ObjectProperty.FullSubcategory (IsDualizable (C := C)))ᵒᵖ ≌
      ObjectProperty.FullSubcategory (IsDualizable (C := C)) :=
  ObjectProperty.liftDualEquivalence _ (internalHom.flip.obj W)
    (fun _ hX ↦ isDualizable_ihom_obj γ hT hX) (toIhomIhomNatTrans W)
    (fun _ hX ↦ isIso_toIhomIhom_of_isDualizable γ hT hX)

end Braided

end CategoryTheory.MonoidalClosed
