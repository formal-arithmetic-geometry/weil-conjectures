/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q1
-/
module

public import Sheaf.AlgebraicGeometry.ModuleBaseChangeMapOpenRestriction
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.RingTheory.TensorProduct.Basic
import Sheaf.AlgebraicGeometry.AffineBaseChangeTensorComparisons

/-!
# Coordinates for base change on compatible affine charts

Source: Stacks Project, Tags 02KG and 01I9.
(blueprint: lem-weil-pbc-affine-base-change-chart-coordinates).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite TensorProduct
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
set_option autoImplicit false

/-- The two section modules on a compatible pair of affine charts have tensor coordinates,
and the canonical base change map sends `r ⊗ m` to `(r ⊗ 1) ⊗ m` in these coordinates.
Source: Stacks Project, Tag 02KG, proof's reduction to spectra; Tag 01I9 (1), (2).
(blueprint: lem-weil-pbc-affine-base-change-chart-coordinates)

Proof: Restrict the square over U and then W. The full inverse-image opens are
f⁻¹U and f'⁻¹W; affineness of f and its base change makes both affine. Identify
U, f⁻¹U and W with spectra of their section rings R, B and R'. The cartesian
square identifies f'⁻¹W with Spec(R' tensor_R B), respecting both projections.
Quasi-coherence identifies F on f⁻¹U with the tilde of M = Gamma(F,f⁻¹U).
The open-restriction base change comparison identifies the original map over W
with the map of this restricted square. Apply the unit-normalized comparisons
exists_affineBaseChange_tensorComparisons to obtain a and b, including the
canonical affine section-ring identifications. For the adjunction defining beta, the equality
homEquiv(homEquiv.symm(k)) = k says that the pushforward of beta composed with
the g-unit equals the pushforward of the g'-unit, followed by the canonical
pushforward composition identifications. On top sections of the restricted
square those identifications are the identity (with the square's equality used
to identify the inverse-image opens). Consequently beta sends the g-unit image
of m to the g'-unit image of m. The generator equations of the tensor comparisons
at m and at (z,m) = (1,m) give the displayed formula at r = 1. Since a.symm,
b and beta.app W are R'-linear and r tensor m = r smul (1 tensor m), the formula
holds for every r. No bijectivity of beta is used. Empty charts,
zero rings and the zero module satisfy the same tensor and tilde identifications. -/
theorem exists_affineBaseChange_chart_coordinates {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g) [IsAffineHom f]
    (F : X.Modules) [F.IsQuasicoherent]
    (U : S.Opens) (hU : IsAffineOpen U)
    (W : S'.Opens) (hW : IsAffineOpen W) (hWU : W ≤ g ⁻¹ᵁ U) :
    let R := Γ(S, U)
    let B := Γ(X, f ⁻¹ᵁ U)
    let R' := Γ(S', W)
    let M := Γ(F, f ⁻¹ᵁ U)
    letI : Algebra R B := (f.app U).hom.toAlgebra
    letI : Algebra R R' := (g.appLE U W hWU).hom.toAlgebra
    letI : Module R M := Module.compHom M (f.app U).hom
    letI : Algebra B (R' ⊗[R] B) := Algebra.TensorProduct.rightAlgebra
    ∃ (a : Γ((tensorPullback g).obj ((pushforward f).obj F), W) ≃ₗ[R'] R' ⊗[R] M)
      (b : Γ((pushforward f').obj ((tensorPullback g').obj F), W) ≃ₗ[R']
        (R' ⊗[R] B) ⊗[B] M),
      ∀ (r : R') (m : M),
        b ((moduleBaseChangeMap f f' g g' sq.w F).app W (a.symm (r ⊗ₜ[R] m))) =
          (r ⊗ₜ[R] (1 : B)) ⊗ₜ[B] m := by sorry

end
end AlgebraicGeometry.Scheme.Modules
