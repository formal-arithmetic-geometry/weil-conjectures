/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperStarMon.Comp

/-!
# The identity isomorphism of the derived pullback is monoidal

For a scheme `X`, the identity isomorphism `L(𝟙 X)^* ≅ 𝟭`
(`AlgebraicGeometry.ProEtale.leftDerivedUpperStarId`) of the derived pullback of pro-étale
sheaves is monoidal: it is compatible with the tensor comparison
`L(𝟙 X)^*(K ⊗ᴸ M) ⟶ L(𝟙 X)^*K ⊗ᴸ L(𝟙 X)^*M`.

## Main results

- `AlgebraicGeometry.ProEtale.leftDerivedUpperStarCongr_hom_tensor`: the transport isomorphisms
  `La^* ≅ Lb^*` along `a = b` commute with the tensor comparisons.
- `AlgebraicGeometry.ProEtale.leftDerivedUpperStarTensorComparison_id_comp`: monoidality of
  `L(𝟙 X)^* ≅ 𝟭`.

## Implementation notes

Monoidality is deduced formally from the left unit law for `𝟙 X ≫ 𝟙 X`
(`AlgebraicGeometry.ProEtale.leftDerivedUpperStarComp_id_left_app`) and the monoidality of the
composition isomorphisms (`AlgebraicGeometry.ProEtale.leftDerivedUpperStarTensorComparison_comp`),
using that `L(𝟙 X)^*` is faithful, being isomorphic to the identity.
-/

@[expose] public section

universe u' u

open CategoryTheory Abelian Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

namespace ProEtale

open DerivedCategory

variable {X Y : Scheme.{u}} [ProEtale.UpperStarPreservesFlat A]

/-- The transport isomorphism `La^* ≅ Lb^*` along an equality `a = b` commutes with the tensor
comparisons of the derived pullbacks. -/
@[reassoc]
lemma leftDerivedUpperStarCongr_hom_tensor {a b : X ⟶ Y} (h : a = b)
    (x y : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) :
    ((leftDerivedUpperStarTensorComparison A a).app x).app y ≫
        ((leftDerivedUpperStarCongr A h).hom.app x ⊗ₘ (leftDerivedUpperStarCongr A h).hom.app y) =
      (leftDerivedUpperStarCongr A h).hom.app (x ⊗ y) ≫
        ((leftDerivedUpperStarTensorComparison A b).app x).app y := by
  subst h
  simp only [leftDerivedUpperStarCongr_rfl, Iso.refl_hom, NatTrans.id_app, id_tensorHom_id]
  erw [Category.comp_id, Category.id_comp]

/-- Monoidality of `L(𝟙 X)^* ≅ 𝟭` at objects in the image of `L(𝟙 X)^*`. -/
private lemma leftDerivedUpperStarTensorComparison_id_comp_aux
    (a b : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :
    (leftDerivedUpperStarId A X).inv.app (L((𝟙 X)^*[A]).obj a) ⊗ₘ
        (leftDerivedUpperStarId A X).inv.app (L((𝟙 X)^*[A]).obj b) =
      (leftDerivedUpperStarId A X).inv.app
          (L((𝟙 X)^*[A]).obj a ⊗ L((𝟙 X)^*[A]).obj b) ≫
        ((leftDerivedUpperStarTensorComparison A (𝟙 X)).app _).app _ := by
  have hκ (Z : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :
      (leftDerivedUpperStarComp A (𝟙 X) (𝟙 X)).hom.app Z =
        (leftDerivedUpperStarCongr A (Category.id_comp (𝟙 X))).hom.app Z ≫
          (leftDerivedUpperStarId A X).inv.app (L((𝟙 X)^*[A]).obj Z) := by
    rw [← leftDerivedUpperStarComp_id_left_app, Category.assoc,
      Iso.hom_inv_id_app]
    exact (Category.comp_id _).symm
  have h₁ := leftDerivedUpperStarTensorComparison_comp A (𝟙 X) (𝟙 X) a b
  have h₃ := leftDerivedUpperStarCongr_hom_tensor A (Category.id_comp (𝟙 X)) a b
  rw [hκ, hκ, hκ, ← tensorHom_comp_tensorHom, reassoc_of% h₃, Category.assoc,
    cancel_epi] at h₁
  have hn := (leftDerivedUpperStarId A X).inv.naturality
    (((leftDerivedUpperStarTensorComparison A (𝟙 X)).app a).app b)
  simp only [Functor.id_map] at hn
  erw [← reassoc_of% hn] at h₁
  rw [cancel_epi] at h₁
  exact h₁

/-- **The identity isomorphism `L(𝟙 X)^* ≅ 𝟭` is monoidal**: it commutes with the tensor
comparison of `L(𝟙 X)^*`,
```
  L(𝟙 X)^*(a ⊗ᴸ b) ──comparison──▶ L(𝟙 X)^*a ⊗ᴸ L(𝟙 X)^*b
            \                               │
             \                              │ λ_a ⊗ λ_b
              ────────λ_{a ⊗ b}──────▶  a ⊗ᴸ b
``` -/
@[reassoc]
lemma leftDerivedUpperStarTensorComparison_id_comp
    (a b : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :
    ((leftDerivedUpperStarTensorComparison A (𝟙 X)).app a).app b ≫
        ((leftDerivedUpperStarId A X).hom.app a ⊗ₘ (leftDerivedUpperStarId A X).hom.app b) =
      (leftDerivedUpperStarId A X).hom.app (a ⊗ b) := by
  -- first at `L(𝟙 X)^*a`, `L(𝟙 X)^*b`
  have key : ((leftDerivedUpperStarTensorComparison A (𝟙 X)).app (L((𝟙 X)^*[A]).obj a)).app
        (L((𝟙 X)^*[A]).obj b) ≫
        ((leftDerivedUpperStarId A X).hom.app _ ⊗ₘ (leftDerivedUpperStarId A X).hom.app _) =
      (leftDerivedUpperStarId A X).hom.app (L((𝟙 X)^*[A]).obj a ⊗ L((𝟙 X)^*[A]).obj b) := by
    rw [← cancel_epi ((leftDerivedUpperStarId A X).inv.app
      (L((𝟙 X)^*[A]).obj a ⊗ L((𝟙 X)^*[A]).obj b)), Iso.inv_hom_id_app,
      ← reassoc_of% (leftDerivedUpperStarTensorComparison_id_comp_aux A a b),
      tensorHom_comp_tensorHom, Iso.inv_hom_id_app, Iso.inv_hom_id_app]
    exact id_tensorHom_id _ _
  -- then transport along `λ⁻¹ : a ≅ L(𝟙 X)^*a`
  have hn := leftDerivedUpperStarTensorComparison_naturality A (𝟙 X)
    ((leftDerivedUpperStarId A X).inv.app a) ((leftDerivedUpperStarId A X).inv.app b)
  have hlam := (leftDerivedUpperStarId A X).hom.naturality
    ((leftDerivedUpperStarId A X).inv.app a ⊗ₘ (leftDerivedUpperStarId A X).inv.app b)
  simp only [Functor.id_map, Functor.id_obj] at hlam
  have e (z : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :
      L((𝟙 X)^*[A]).map ((leftDerivedUpperStarId A X).inv.app z) ≫
        (leftDerivedUpperStarId A X).hom.app (L((𝟙 X)^*[A]).obj z) = 𝟙 _ := by
    rw [(leftDerivedUpperStarId A X).hom.naturality]
    simp
  rw [← cancel_mono ((leftDerivedUpperStarId A X).inv.app a ⊗ₘ
    (leftDerivedUpperStarId A X).inv.app b), Category.assoc, tensorHom_comp_tensorHom,
    Iso.hom_inv_id_app, Iso.hom_inv_id_app]
  erw [id_tensorHom_id, Category.comp_id]
  rw [← hlam, ← key, ← reassoc_of% hn, tensorHom_comp_tensorHom]
  erw [e, e, id_tensorHom_id, Category.comp_id]

end ProEtale

end AlgebraicGeometry
