/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V3
-/
module

public import Sheaf.AlgebraicGeometry.FiniteAffineCechCoefficientComparisonMap
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Sheaf.AlgebraicGeometry.FiniteAffineCechIntersectionBaseChange

/-! # Scalar transport into the coefficient generator span

Source: Stacks Project, Tags 02KG, 01I9, 01IA and 0097.
(blueprint: lem-pc-coefficient-target-scalar-span).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits Opposite
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

/-- A section-ring multiple of a unit generator is in the base-ring span.
Source: Stacks Project, Tag 02KG, Lemma 30.5.1 (affine tensor computation),
Tags 01I9, 01IA and 0097 (unit and restriction formulas).
(blueprint: lem-pc-coefficient-target-scalar-span).

Proof: Put A = Gamma(U,O), D = Gamma(Z,O), R = Gamma(B,O), and
C = Gamma(I,O), where I = W intersect fprime inverse image B. The restricted
cartesian square identifies I with Z times_U B. The affine ring computation
identifies C with R tensor_A D. Every a in C is therefore a finite sum of
r tensor d. The pullback unit is D-linear via the structural D -> C map:
its restriction sends d*s to the image of d times the generator of s.
Thus (r tensor d) times the generator of s equals r times the generator
of d*s. Transport along coefficientSupportIso; its scalar formula identifies
the r action with the actual R action on the direct image. Additivity then
places each a times a generator in the R-span of unit generators. The A-action
used in N cancels GammaSpecIso against the canonical affine chart, so these
are the stated generators. The zero and empty-open cases follow from the same
ring and module formulas. -/
theorem coefficientTarget_scalar_span
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
    ∀ (a : Γ(X', W ⊓ f' ⁻¹ᵁ B)) (s : N),
      (coefficientSupportIso f' M W B).inv
        (a • (M.presheaf.map (homOfLE (inf_le_left : W ⊓ f' ⁻¹ᵁ B ≤ W)).op
            (coefficientPullbackGenerator F (f ⁻¹ᵁ U) Z g' W hW s))) ∈
      Submodule.span (Γ(T', B)) (Set.range (fun t : N ↦
        (coefficientSupportIso f' M W B).inv
          (M.presheaf.map (homOfLE (inf_le_left : W ⊓ f' ⁻¹ᵁ B ≤ W)).op
            (coefficientPullbackGenerator F (f ⁻¹ᵁ U) Z g' W hW t)))) := by
  sorry

end
end AlgebraicGeometry.Scheme.Modules
