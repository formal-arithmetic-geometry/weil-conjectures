/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V3
-/
module

public import Sheaf.AlgebraicGeometry.FiniteAffineCechCoefficientComparisonMap
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Sheaf.AlgebraicGeometry.ModulePullbackAffineSections
import Sheaf.AlgebraicGeometry.FiniteAffineCechIntersectionBaseChange

/-! # Affine coefficient generators

Source: Stacks Project, Tags 02KG, 01I9, 01IA and 0097.
(blueprint: lem-pc-coefficient-target-section-generators).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits Opposite
open scoped TensorProduct BigOperators
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

/-- Affine pullback sections are finite sums of section-ring multiples of unit sections.
Source: Stacks Project, Tags 01I9 and 01IA (affine pullback), 0097 (restriction).
(blueprint: lem-pc-coefficient-target-section-generators).

Proof: Let I = W intersect fprime inverse image B and V be the image of Z in X.
The affine intersection base-change theorem makes I affine. The open V is affine
because it is isomorphic to Z. Its restricted module is quasi-coherent. Apply the
affine pullback sections theorem to I -> V: its tensor comparison is surjective,
so tensor induction writes each section as a finite sum of target-ring multiples
of the pullback unit of sections on V. Transport tensorPullback to pullback by
uniqueness of left adjoints, with the unit equation. The restriction isomorphism
identifies sections on V with sections on Z; naturality of the unit and composition
of restrictions give precisely the displayed generators. Empty opens give the
zero module, represented by a sum indexed by Fin 0. -/
theorem coefficientTarget_section_generators
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
    ∀ y : Γ(M, W ⊓ f' ⁻¹ᵁ B),
      ∃ (n : ℕ) (a : Fin n → Γ(X', W ⊓ f' ⁻¹ᵁ B)) (s : Fin n → N),
        y = ∑ i, a i •
          (M.presheaf.map (homOfLE (inf_le_left : W ⊓ f' ⁻¹ᵁ B ≤ W)).op
            (coefficientPullbackGenerator F (f ⁻¹ᵁ U) Z g' W hW (s i))) := by
  sorry

end
end AlgebraicGeometry.Scheme.Modules
