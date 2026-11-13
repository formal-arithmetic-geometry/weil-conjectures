/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FiniteAffineCechCoefficientComparisonMap
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.AlgebraicGeometry.CoefficientTargetTensorDecoder

/-! # Injective of the coefficient tensor map

Source: Stacks Project, Tags 02KG, 01I9, 01IA and 0097.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits Opposite
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

private theorem tensor_leftInverse_of_generators
    {A R N Q : Type u} [CommRing A] [CommRing R] [Algebra A R]
    [AddCommGroup N] [Module A N] [AddCommGroup Q] [Module R Q]
    (c : (R ⊗[A] N) →ₗ[R] Q) (l : Q →ₗ[R] (R ⊗[A] N))
    (h : ∀ s : N, l (c ((1 : R) ⊗ₜ[A] s)) = (1 : R) ⊗ₜ[A] s) :
    Function.LeftInverse l c := by
  intro t
  induction t using TensorProduct.inductionOn with
  | tmul r s =>
    have he : r ⊗ₜ[A] s = r • ((1 : R) ⊗ₜ[A] s) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [he, c.map_smul, l.map_smul, h]
  | add t t' ht ht' => rw [c.map_add, l.map_add, ht, ht']

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A tensor map with the supported pullback-unit formula is injective.
Only injectivity is asserted; no equivalence or inverse formula is assumed.
Source: Stacks Project, Tag 02KG (Lemma 30.5.1, affine tensor computation),
Tags 01I9 and 01IA (affine pullback), and Tag 0097 (restriction). -/
theorem coefficientTarget_tensor_injective
    {X T : Scheme.{u}} (f : X ⟶ T) [IsSeparated f]
    (F : X.Modules) [F.IsQuasicoherent]
    (U : T.Opens) (hU : IsAffineOpen U)
    (Z : (f ⁻¹ᵁ U).toScheme.Opens) (hZ : IsAffineOpen Z)
    {T' X' : Scheme.{u}} (g : T' ⟶ U.toScheme) (g' : X' ⟶ X) (f' : X' ⟶ T')
    (sq : IsPullback g' f' f (g ≫ U.ι))
    (W : X'.Opens) (hW : W = g' ⁻¹ᵁ ((f ⁻¹ᵁ U).ι ''ᵁ Z))
    (B : T'.Opens) (hB : IsAffineOpen B) :
    letI : Algebra Γ(U.toScheme, ⊤) Γ(T', B) :=
      (g.appLE ⊤ B (by simp)).hom.toAlgebra
    let N := (ModuleCat.restrictScalars
      (((Scheme.ΓSpecIso Γ(U.toScheme, ⊤)).inv ≫
        ((f ∣_ U) ≫ U.toScheme.toSpecΓ).appTop).hom)).obj
          ((F.restrict (f ⁻¹ᵁ U).ι).presheafModuleCat.obj (op Z))
    let M := (pullback g').obj F
    ∀ c : (Γ(T', B) ⊗[Γ(U.toScheme, ⊤)] N) →ₗ[Γ(T', B)]
        Γ((pushforward (W.ι ≫ f')).obj (M.restrict W.ι), B),
      (∀ s : N, c ((1 : Γ(T', B)) ⊗ₜ[Γ(U.toScheme, ⊤)] s) =
        (coefficientSupportIso f' M W B).inv
          (M.presheaf.map (homOfLE (inf_le_left : W ⊓ f' ⁻¹ᵁ B ≤ W)).op
            (coefficientPullbackGenerator F (f ⁻¹ᵁ U) Z g' W hW s))) →
        Function.Injective c := by
  classical
  dsimp only
  let : Algebra Γ(U.toScheme, ⊤) Γ(T', B) :=
    (g.appLE ⊤ B (by simp)).hom.toAlgebra
  let N := (ModuleCat.restrictScalars
    (((Scheme.ΓSpecIso Γ(U.toScheme, ⊤)).inv ≫
      ((f ∣_ U) ≫ U.toScheme.toSpecΓ).appTop).hom)).obj
        ((F.restrict (f ⁻¹ᵁ U).ι).presheafModuleCat.obj (op Z))
  let M := (pullback g').obj F
  intro c hc
  obtain ⟨l, hl⟩ := exists_coefficientTarget_tensor_decoder f F U hU Z hZ g g' f' sq W hW B hB
  apply (tensor_leftInverse_of_generators c l ?_).injective
  intro s
  rw [hc, hl]

end
end AlgebraicGeometry.Scheme.Modules
