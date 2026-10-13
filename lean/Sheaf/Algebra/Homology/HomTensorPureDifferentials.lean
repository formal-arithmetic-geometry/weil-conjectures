/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q2
-/
module

public import Sheaf.Algebra.Homology.HomTensorDegreewise
import Sheaf.Algebra.Homology.HomTensorSectionNaturality

/-!
# Tensor summand differentials on pure tensors

Source: Stacks Project, More on Algebra, Tag 0A5Y; Modules on Sites, Section 03EK.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.MonoidalCategory Opposite

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{max u v})

set_option hygiene false in
set_option quotPrecheck false in
local notation "Mod" => SheafOfModules.{max u v}
  ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)

private noncomputable def sheafEvaluation {A B : Mod} (V : Cᵒᵖ) (x : A.val.obj V) :
    (A ⟶ B) →+ B.val.obj V where
  toFun f := (f.val.app V).hom x
  map_zero' := rfl
  map_add' _ _ := rfl

set_option synthInstance.maxSize 256 in
private lemma tensorSectionMap_tmul {A A' B B' : Mod} (f : A ⟶ A') (g : B ⟶ B')
    (V : Cᵒᵖ) (x : A.val.obj V) (y : B.val.obj V) :
    letI := SheafOfModules.monoidalCategory R
    ((f ⊗ₘ g).val.app V).hom
      (((homTensorSectionMap R A B).app V).hom (x ⊗ₜ[R.obj.obj V] y)) =
      ((homTensorSectionMap R A' B').app V).hom
        ((f.val.app V).hom x ⊗ₜ[R.obj.obj V] (g.val.app V).hom y) := by
  let := SheafOfModules.monoidalCategory R
  have h := congrArg (fun k : A.val ⊗ B.val ⟶ (A' ⊗ B').val =>
    (k.app V).hom (x ⊗ₜ[R.obj.obj V] y)) (homTensorSectionMap_natural R f g)
  change ((f ⊗ₘ g).val.app V).hom
      (((homTensorSectionMap R A B).app V).hom (x ⊗ₜ[R.obj.obj V] y)) =
    ((homTensorSectionMap R A' B').app V).hom
      (((f.val ⊗ₘ g.val).app V).hom (x ⊗ₜ[R.obj.obj V] y)) at h
  exact h.trans (congrArg ((homTensorSectionMap R A' B').app V).hom
    (ModuleCat.MonoidalCategory.tensorHom_tmul (R := R.obj.obj V) (f.val.app V) (g.val.app V) x y))

set_option maxHeartbeats 800000 in
-- The summand maps use dependent coproduct indices and the localized tensor.
set_option synthInstance.maxSize 256 in
/-- The two tensor summand differentials on localized pure tensors.
Source: Stacks Project, More on Algebra, Tag 0A5Y, tensor differential formula;
Modules on Sites, Section 03EK, tensor sheafification.
(blueprint: lem-sc-hom-tensor-pure-differentials).

Proof: Mathlib's mapBifunctor.d₁_eq and d₂_eq identify these summand maps
with the left and right whiskerings followed by the next summand inclusion.
For cochains the first sign is one and the second is (-1)^p. Naturality
of the sheafification unit and tensor comparison identifies the whiskerings
on the presheaf tensor with the tensor of the component maps. The module
tensor map sends x tensor y respectively to d_K x tensor y and x tensor
d_L y. Evaluation at every object gives the two displayed equations.
All degrees are integers; the sign formula remains valid in negative degrees,
and zero differentials give zero tensors on both sides. -/
theorem homTensor_pure_differentials (K L : CochainComplex Mod ℤ)
    (p q t : ℤ) (h : p + q = t) :
    letI := SheafOfModules.monoidalCategory R
    ∀ (V : Cᵒᵖ) (x : (K.X p).val.obj V) (y : (L.X q).val.obj V),
      ((HomologicalComplex.mapBifunctor.d₁ K L (curriedTensor Mod)
          (ComplexShape.up ℤ) p q (t + 1)).val.app V).hom
        (((homTensorSectionMap R (K.X p) (L.X q)).app V).hom
          (x ⊗ₜ[R.obj.obj V] y)) =
        ((CochainComplex.ιMapBifunctor K L (curriedTensor Mod)
          (p + 1) q (t + 1) (by omega)).val.app V).hom
          (((homTensorSectionMap R (K.X (p + 1)) (L.X q)).app V).hom
            (((K.d p (p + 1)).val.app V).hom x ⊗ₜ[R.obj.obj V] y)) ∧
      ((HomologicalComplex.mapBifunctor.d₂ K L (curriedTensor Mod)
          (ComplexShape.up ℤ) p q (t + 1)).val.app V).hom
        (((homTensorSectionMap R (K.X p) (L.X q)).app V).hom
          (x ⊗ₜ[R.obj.obj V] y)) =
        p.negOnePow • ((CochainComplex.ιMapBifunctor K L (curriedTensor Mod)
          p (q + 1) (t + 1) (by omega)).val.app V).hom
          (((homTensorSectionMap R (K.X p) (L.X (q + 1))).app V).hom
            (x ⊗ₜ[R.obj.obj V] ((L.d q (q + 1)).val.app V).hom y))  := by
  let := SheafOfModules.monoidalCategory R
  intro V x y
  have hd1 := HomologicalComplex.mapBifunctor.d₁_eq (K₁ := K) (K₂ := L)
    (F := curriedTensor Mod) (c := ComplexShape.up ℤ)
    (show (ComplexShape.up ℤ).Rel p (p + 1) from rfl) q (t + 1) (by
      change p + 1 + q = t + 1
      omega)
  have hd2 := HomologicalComplex.mapBifunctor.d₂_eq (K₁ := K) (K₂ := L)
    (F := curriedTensor Mod) (c := ComplexShape.up ℤ)
    p (show (ComplexShape.up ℤ).Rel q (q + 1) from rfl) (t + 1) (by
      change p + (q + 1) = t + 1
      omega)
  have e1 : (ComplexShape.up ℤ).ε₁ (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (p, q) = 1 := rfl
  have e2 : (ComplexShape.up ℤ).ε₂ (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (p, q) = p.negOnePow := rfl
  rw [e1, one_smul] at hd1
  rw [e2] at hd2
  constructor
  · have ht := tensorSectionMap_tmul R (K.d p (p + 1)) (𝟙 (L.X q)) V x y
    rw [tensorHom_id] at ht
    erw [hd1]
    exact congrArg
      ((CochainComplex.ιMapBifunctor K L (curriedTensor Mod)
        (p + 1) q (t + 1) (by omega)).val.app V).hom ht
  · let ev := sheafEvaluation R
      (B := (CochainComplex.mapBifunctor K L (curriedTensor Mod)).X (t + 1)) V
      (((homTensorSectionMap R (K.X p) (L.X q)).app V).hom
        (x ⊗ₜ[R.obj.obj V] y))
    change ev (HomologicalComplex.mapBifunctor.d₂ K L (curriedTensor Mod)
      (ComplexShape.up ℤ) p q (t + 1)) = _
    rw [hd2, Units.smul_def, map_zsmul]
    have ht := tensorSectionMap_tmul R (𝟙 (K.X p)) (L.d q (q + 1)) V x y
    rw [id_tensorHom] at ht
    exact congrArg
      (fun z => (p.negOnePow : ℤ) •
        ((CochainComplex.ιMapBifunctor K L (curriedTensor Mod)
          p (q + 1) (t + 1) (by omega)).val.app V).hom z) ht

end CategoryTheory
