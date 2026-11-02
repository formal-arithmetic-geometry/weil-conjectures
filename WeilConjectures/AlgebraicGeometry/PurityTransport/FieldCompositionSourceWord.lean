/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation

/-! # Categorical scalar calculation for the source-compositor word

Source: the scalar passage in smooth composition.
(blueprint: lem-pur-field-composition-source-word-scalar). -/

@[expose] public section
set_option autoImplicit false
open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.Functor.LaxMonoidal CategoryTheory.Functor.OplaxMonoidal

namespace AlgebraicGeometry.ProEtale.PurityTransport

/-- The source-compositor word assembled from geometric composition, line
multiplication, associativity, line pullback and a monoidal tensorator.
Source: smooth composition's source comparison
(blueprint: def-pur-field-composition-source-word). -/
def fieldCompSourceWord
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D) [F.Monoidal] (N : C) {T Lh Lx Lf : D} (Ly : C)
    (h : T ≅ F.obj N) (b : Lh ≅ Lx ⊗ Lf) (p : F.obj Ly ≅ Lx) :
    T ⊗ Lh ⟶ F.obj (N ⊗ Ly) ⊗ Lf :=
  (h.hom ⊗ₘ b.hom) ≫ (α_ _ _ _).inv ≫
    ((𝟙 _ ⊗ₘ p.inv) ⊗ₘ 𝟙 _) ≫ (μ F N Ly ⊗ₘ 𝟙 _)

private theorem fieldCompSourceWord_normalization
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D) [F.Monoidal] (N : C) {T Lh Lx Lf : D} (Ly : C)
    (h : T ≅ F.obj N) (b : Lh ≅ Lx ⊗ Lf) (p : F.obj Ly ≅ Lx) :
    fieldCompSourceWord F N Ly h b p ≫ (δ F N Ly ⊗ₘ 𝟙 _) ≫
      ((𝟙 _ ⊗ₘ p.hom) ⊗ₘ 𝟙 _) ≫ (α_ _ _ _).hom = h.hom ⊗ₘ b.hom := by
  simp only [fieldCompSourceWord, Category.assoc, Category.id_comp, Iso.inv_hom_id,
    tensorHom_id, ← comp_whiskerRight_assoc, Functor.Monoidal.μ_δ_assoc,
    tensorHom_comp_tensorHom, Category.comp_id, id_whiskerRight]

private theorem tensorCompLeft
    {D : Type*} [Category D] [MonoidalCategory D]
    {A B C X Y : D} (f : A ⟶ B) (g : B ⟶ C) (h : X ⟶ Y) :
    ((f ≫ g) ⊗ₘ h) = (f ⊗ₘ 𝟙 X) ≫ (g ⊗ₘ h) := by
  simp only [tensorHom_comp_tensorHom, Category.id_comp]

/-- Four elementary scalar squares imply scalar compatibility of the source word.
Source: smooth composition's scalar source calculation
(blueprint: lem-pur-field-composition-source-word-scalar).

Proof in words. Postcompose with the invertible target normalizer: inverse
pullback tensorator, line pullback, and tensor associator. This cancels the
source word on the target side. Naturality of the pullback tensorator and its
scalar square move the scalar comparison outside the source tensorator; the
tensorator and its inverse cancel. Naturality of the scalar tensorator moves
it across inverse line pullback. Its associativity equation then moves it
across the inverse tensor associator. The given line pullback square replaces
the remaining line factor. Naturality of the associator makes its inverse and
hom cancel. Finally scalar-tensorator naturality separates geometric and line
factors, which are exactly the geometric and line-product squares. -/
theorem fieldCompScalarSourceStep
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    [MonoidalCategory C] [MonoidalCategory D]
    [MonoidalCategory C'] [MonoidalCategory D']
    (F : C ⥤ D) [F.Monoidal] (F' : C' ⥤ D') [F'.Monoidal]
    (U : C ⥤ C') [U.Monoidal] (V : D ⥤ D') [V.Monoidal]
    (ρ : F ⋙ V ⟶ U ⋙ F')
    (N : C) (N' : C') (rg : U.obj N ⟶ N')
    {T Lh Lx Lf : D} {T' Lh' Lx' Lf' : D'} (Ly : C) (Ly' : C')
    (h : T ≅ F.obj N) (b : Lh ≅ Lx ⊗ Lf) (p : F.obj Ly ≅ Lx)
    (h' : T' ≅ F'.obj N') (b' : Lh' ≅ Lx' ⊗ Lf') (p' : F'.obj Ly' ≅ Lx')
    (rh : V.obj T ⟶ T') (th : V.obj Lh ⟶ Lh')
    (tx : V.obj Lx ⟶ Lx') (tf : V.obj Lf ⟶ Lf') (ty : U.obj Ly ⟶ Ly')
    (hgeom : V.map h.hom ≫ ρ.app N ≫ F'.map rg = rh ≫ h'.hom)
    (hprod : V.map b.hom ≫ δ V Lx Lf ≫ (tx ⊗ₘ tf) = th ≫ b'.hom)
    (hpull : V.map p.inv ≫ ρ.app Ly ≫ F'.map ty ≫ p'.hom = tx)
    (hten : ρ.app (N ⊗ Ly) ≫ F'.map (δ U N Ly) ≫ δ F' (U.obj N) (U.obj Ly) =
      V.map (δ F N Ly) ≫ δ V (F.obj N) (F.obj Ly) ≫ (ρ.app N ⊗ₘ ρ.app Ly)) :
    V.map (fieldCompSourceWord F N Ly h b p) ≫ δ V (F.obj (N ⊗ Ly)) Lf ≫
      (ρ.app (N ⊗ Ly) ⊗ₘ tf) ≫
      (F'.map (δ U N Ly ≫ (rg ⊗ₘ ty)) ⊗ₘ 𝟙 Lf') =
    (δ V T Lh ≫ (rh ⊗ₘ th)) ≫ fieldCompSourceWord F' N' Ly' h' b' p' := by
  have hn : ρ.app (N ⊗ Ly) ≫ F'.map (δ U N Ly ≫ (rg ⊗ₘ ty)) ≫
      δ F' N' Ly' =
      V.map (δ F N Ly) ≫ δ V (F.obj N) (F.obj Ly) ≫
        ((ρ.app N ≫ F'.map rg) ⊗ₘ (ρ.app Ly ≫ F'.map ty)) := by
    simp only [Functor.map_comp, Category.assoc]
    rw [← δ_natural F' rg ty]
    simpa only [Category.assoc, tensorHom_comp_tensorHom] using
      congrArg (fun z ↦ z ≫ (F'.map rg ⊗ₘ F'.map ty)) hten
  have : IsIso ((δ F' N' Ly' ⊗ₘ 𝟙 Lf') ≫
      ((𝟙 _ ⊗ₘ p'.hom) ⊗ₘ 𝟙 _) ≫ (α_ _ _ _).hom) := by infer_instance
  apply (cancel_mono ((δ F' N' Ly' ⊗ₘ 𝟙 Lf') ≫
    ((𝟙 _ ⊗ₘ p'.hom) ⊗ₘ 𝟙 _) ≫ (α_ _ _ _).hom)).mp
  simp only [Category.assoc, fieldCompSourceWord_normalization]
  simp only [fieldCompSourceWord, Functor.map_comp, Category.assoc]
  rw [tensorHom_comp_tensorHom_assoc, tensorHom_comp_tensorHom_assoc]
  simp only [Functor.map_comp, Category.assoc, Category.comp_id] at hn ⊢
  rw [hn]
  rw [tensorCompLeft, tensorCompLeft]
  have hv : δ V (F.obj (N ⊗ Ly)) Lf ≫ (V.map (δ F N Ly) ⊗ₘ 𝟙 _) =
      V.map (δ F N Ly ⊗ₘ 𝟙 Lf) ≫ δ V (F.obj N ⊗ F.obj Ly) Lf := by
    simpa only [Functor.map_id] using δ_natural V (δ F N Ly) (𝟙 Lf)
  simp only [Category.assoc]
  rw [reassoc_of% hv]
  simp only [← Functor.map_comp_assoc, tensorHom_comp_tensorHom,
    Functor.Monoidal.μ_δ, Category.comp_id]
  simp only [Functor.map_comp, Category.assoc]
  rw [← δ_natural_assoc V (𝟙 (F.obj N) ⊗ₘ p.inv) (𝟙 Lf)]
  rw [tensorHom_comp_tensorHom_assoc]
  simp only [Functor.map_id, Category.comp_id]
  rw [← δ_natural V (𝟙 (F.obj N)) p.inv]
  simp only [Functor.map_id]
  rw [tensorCompLeft]
  simp only [Category.assoc]
  have hx : (((𝟙 (V.obj (F.obj N)) ⊗ₘ V.map p.inv) ⊗ₘ 𝟙 (V.obj Lf)) ≫
      (((ρ.app N ≫ F'.map rg) ⊗ₘ (ρ.app Ly ≫ F'.map ty)) ⊗ₘ tf) ≫
      ((𝟙 (F'.obj N') ⊗ₘ p'.hom) ⊗ₘ 𝟙 Lf')) =
      (((ρ.app N ≫ F'.map rg) ⊗ₘ tx) ⊗ₘ tf) := by
    simp only [tensorHom_comp_tensorHom, Category.assoc, Category.id_comp,
      Category.comp_id, hpull]
  rw [reassoc_of% hx]
  have hassoc : V.map (α_ (F.obj N) Lx Lf).inv ≫
      δ V (F.obj N ⊗ Lx) Lf ≫ (δ V (F.obj N) Lx ⊗ₘ 𝟙 (V.obj Lf)) =
      δ V (F.obj N) (Lx ⊗ Lf) ≫ (𝟙 (V.obj (F.obj N)) ⊗ₘ δ V Lx Lf) ≫
        (α_ _ _ _).inv := by
    simpa only [tensorHom_id, id_tensorHom] using
      (CategoryTheory.Functor.OplaxMonoidal.associativity_inv V (F.obj N) Lx Lf).symm
  rw [reassoc_of% hassoc, ← associator_inv_naturality_assoc]
  simp only [Iso.inv_hom_id, Category.comp_id]
  rw [← δ_natural_assoc V h.hom b.hom]
  simp only [tensorHom_comp_tensorHom, Category.id_comp, hgeom, hprod]


end AlgebraicGeometry.ProEtale.PurityTransport
