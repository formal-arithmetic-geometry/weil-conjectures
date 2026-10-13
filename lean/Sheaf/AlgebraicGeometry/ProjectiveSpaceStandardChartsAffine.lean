/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.OfSections
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Charts

/-!
# Standard charts and coordinate sections of projective space

Source: Stacks Project, Tags 01NG, 01MV, 01MS, 01ND, 01JR and 01I4
(blueprint: lem-weil-pbc-projective-space-standard-charts-part3).
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.ProjectiveSpace

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Over an affine base open, a standard chart has the polynomial coordinate ring,
with the indicated coefficient and coordinate maps.
Source: Stacks Project, Constructions, Tag 01NG; Schemes, Tags 01JR and 01I4.
(blueprint: lem-weil-pbc-projective-space-standard-charts-part3).

Proof: Put W = D_+(T_i)_S ∩ q⁻¹(V). Restrict the defining pullback square of projective
space to V and to the integral standard chart D_+(T_i). The open-fibre-product formula
identifies W with V ×_{Spec Z} D_+(T_i), with its maps to V and the integral chart.
The integral chart is Spec Z[U_j : j ≠ i], with U_j = T_j/T_i, by projIntBasicOpenIso.
Using eV and pullbackSpecIso identifies W with Spec (R ⊗_Z Z[U_j]). The polynomial
scalar-extension equivalence sends r ⊗ 1 to C r and 1 ⊗ U_j to X j and identifies this
ring with R[U_j]. Thus W is affine. Take h to be the projection of the restricted
pullback square to V, so h followed by V.ι is W.ι followed by q. Global sections of the
constructed scheme isomorphism give E. Compatibility of pullbackSpecIso with its two
projections, followed by the scalar-extension formulas, identifies E(C r) with the
map of h followed by eV.hom and E(X j) with the restriction of rho-sharp(T_j/T_i).
The topIso in the coefficient formula is exactly the identification of sections on W
with global sections of W.toScheme. This proves every displayed compatibility. -/
theorem projectiveSpace_standardCharts_part3 (n : Type u) (S : Scheme.{u})
    [Finite n] [Nonempty n] :
    ∀ (V : S.Opens) (R : CommRingCat.{u}) (eV : V.toScheme ≅ Spec R) (i : n),
      IsAffineOpen (standardOpen n S i ⊓ (ℙ(n; S) ↘ S) ⁻¹ᵁ V) ∧
      ∃ (h : (standardOpen n S i ⊓ (ℙ(n; S) ↘ S) ⁻¹ᵁ V).toScheme ⟶ V.toScheme)
        (E : MvPolynomial {j : n // j ≠ i} R ≃+*
          Γ(ℙ(n; S), standardOpen n S i ⊓ (ℙ(n; S) ↘ S) ⁻¹ᵁ V)),
        h ≫ V.ι = (standardOpen n S i ⊓ (ℙ(n; S) ↘ S) ⁻¹ᵁ V).ι ≫ (ℙ(n; S) ↘ S) ∧
        (∀ r : R, E (MvPolynomial.C r) =
          (standardOpen n S i ⊓ (ℙ(n; S) ↘ S) ⁻¹ᵁ V).topIso.hom
            ((h ≫ eV.hom).appTop ((Scheme.ΓSpecIso R).inv r))) ∧
        ∀ j : {j : n // j ≠ i}, E (MvPolynomial.X j) =
          (ℙ(n; S)).presheaf.map (homOfLE
            (inf_le_left : standardOpen n S i ⊓ (ℙ(n; S) ↘ S) ⁻¹ᵁ V ≤ standardOpen n S i)).op
          ((toProjInt n S).app
            (Proj.basicOpen (MvPolynomial.homogeneousSubmodule n (ULift.{u} ℤ)) (MvPolynomial.X i))
            (Proj.awayToSection _ _ (MvPolynomial.awayXRatio (ULift.{u} ℤ) i j.1))) := by
  sorry

end
end AlgebraicGeometry.ProjectiveSpace
