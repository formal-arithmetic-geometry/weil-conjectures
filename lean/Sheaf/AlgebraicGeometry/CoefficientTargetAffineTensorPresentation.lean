/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M2
-/
module

public import Sheaf.AlgebraicGeometry.FiniteAffineCechCoefficientComparisonMap
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Sheaf.AlgebraicGeometry.ModulePullbackAffineSections
import Sheaf.AlgebraicGeometry.FiniteAffineCechIntersectionBaseChange

/-! # Tensor presentation of inverse-image coefficient sections

Source: Stacks Project, Tags 02KG, 01I9 and 01IA.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits Opposite
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

/-- Sections supported on the inverse image of an affine coefficient open have a
unit-compatible tensor presentation. This assertion only describes the target sections;
it does not mention an associated-module source or a comparison morphism.
Source: Stacks Project, Tag 02KG (Lemma 30.5.1), and Tags 01I9, 01IA and 0097.
(blueprint: lem-pc-coefficient-target-affine-tensor-presentation).

Proof: Write Y = f inverse image U, A = Gamma(U,O), D = Gamma(Z,O),
R = Gamma(B,O), and N = Gamma(Z,F|Y), regarded as an A-module using the scalar
map displayed below. The restricted cartesian square identifies
W intersect f' inverse image B with Z times_U B. The affine intersection
base-change theorem makes this open affine. Its ring is R tensor_A D. The
affine pullback section formula identifies its M-sections with
(R tensor_A D) tensor_D N. Transport tensorPullback to the standard pullback
by the unique unit-compatible isomorphism of left adjoints, and identify
open-immersion pullback with restriction. Tensor reassociation gives the
R-linear equivalence to R tensor_A N, sending (r tensor d) tensor n to
r tensor (d*n), with inverse r tensor n mapping to (r tensor 1) tensor n.
The GammaSpecIso and canonical chart identify the A-action with the displayed
restriction-of-scalars map. Pullback unit compatibility sends the restriction
of coefficientPullbackGenerator(s) to 1 tensor s. Finally use
coefficientSupportIso to pass from intersection sections to pushforward
sections. Empty Z or B gives zero modules and the same formulas; neither
flatness nor any covering hypothesis is needed. -/
theorem exists_coefficientTarget_affine_tensor_presentation
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
    ∃ e : Γ((pushforward (W.ι ≫ f')).obj (M.restrict W.ι), B) ≃ₗ[Γ(T', B)]
        (Γ(T', B) ⊗[Γ(U.toScheme, ⊤)] N),
      ∀ s : Γ(F.restrict (f ⁻¹ᵁ U).ι, Z),
        (coefficientSupportIso f' M W B).hom
          (e.symm ((1 : Γ(T', B)) ⊗ₜ[Γ(U.toScheme, ⊤)] (s : N))) =
        M.presheaf.map (homOfLE (inf_le_left : W ⊓ f' ⁻¹ᵁ B ≤ W)).op
          (coefficientPullbackGenerator F (f ⁻¹ᵁ U) Z g' W hW s) := by sorry

end
end AlgebraicGeometry.Scheme.Modules
