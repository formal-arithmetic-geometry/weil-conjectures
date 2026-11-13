/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DiagonalConormalDerivation
import WeilConjectures.AlgebraicGeometry.AffineConormalSections
import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
import WeilConjectures.AlgebraicGeometry.DiagonalConormal
import WeilConjectures.AlgebraicGeometry.DiagonalConormalAffineSectionsChosen

/-! # Affine sections of the diagonal conormal derivation

On affine opens `U` of `X` over `V` of `S`, the conormal sheaf of the diagonal is identified
with the module of Kähler differentials of `Γ(X, U)` over `Γ(S, V)`, together with the
formula for one normalized derivation (Stacks Project, Tags 01KJ, 01R3, 08S2, 00RW). -/

@[expose] public section

universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry
variable {X S : Scheme.{u}}

/-- The affine conormal equivalence and its formula for one normalized derivation.
Source: Stacks Project, Tags 01KJ, 01R3, 08S2 and 00RW. -/
theorem exists_diagonalConormal_affine_sections_base (f : X ⟶ S)
    (U : X.affineOpens) (V : S.affineOpens) (hUV : U.1 ≤ f ⁻¹ᵁ V.1)
    (D : (diagonalConormal f).val.Derivation' f.pullbackPresheafToPresheaf)
    (hD : IsDiagonalConormalDerivation f D) :
    ∃ e : CommRingCat.KaehlerDifferential (f.appLE V.1 U.1 hUV) ≃ₗ[Γ(X, U.1)]
          Γ(diagonalConormal f, U.1),
        ∀ a : Γ(X, U.1), e (CommRingCat.KaehlerDifferential.d a) =
          D.d (X := op U.1) a := by
  let D₀ := Classical.choose (exists_diagonalConormalDerivation f)
  have hD₀ : IsDiagonalConormalDerivation f D₀ :=
    Classical.choose_spec (exists_diagonalConormalDerivation f)
  obtain ⟨e, he⟩ := exists_affine_sections_for_chosen_derivation f U V hUV
  have hEq : D = D₀ := diagonalConormalDerivation_ext f hD hD₀
  refine ⟨e, ?_⟩
  intro a
  rw [he a]
  simp [D₀, hEq]

end AlgebraicGeometry
