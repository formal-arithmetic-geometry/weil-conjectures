module

public import Sheaf.AlgebraicGeometry.DiagonalConormalDerivation
public import Sheaf.AlgebraicGeometry.AffineConormalSections
public import Sheaf.AlgebraicGeometry.BaseChangeConventions
public import Sheaf.AlgebraicGeometry.DiagonalConormal

@[expose] public section

universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry
variable {X S : Scheme.{u}}

/-- The affine coordinate calculation for the canonical normalized derivation chosen by
`exists_diagonalConormalDerivation`.  This is the geometric affine calculation of Tags
01KJ, 01R3 and 08S2; the proof is intentionally isolated so the supplied-derivation
statement only performs transport along uniqueness. (blueprint: stage3-diagonal-conormal-chosen) -/
theorem exists_affine_sections_for_chosen_derivation (f : X ⟶ S)
    (U : X.affineOpens) (V : S.affineOpens) (hUV : U.1 ≤ f ⁻¹ᵁ V.1) :
    let D := Classical.choose (exists_diagonalConormalDerivation f)
    ∃ e : CommRingCat.KaehlerDifferential (f.appLE V.1 U.1 hUV) ≃ₗ[Γ(X, U.1)]
          Γ(diagonalConormal f, U.1),
        ∀ a : Γ(X, U.1), e (CommRingCat.KaehlerDifferential.d a) =
          D.d (X := op U.1) a := by sorry

/-- Normalization by the kernel class map determines a diagonal conormal derivation.
This is the uniqueness part of the difference-derivation construction in Tag 08S2.
(blueprint: stage3-diagonal-conormal-uniqueness) -/
theorem diagonalConormalDerivation_ext (f : X ⟶ S)
    {D₁ D₂ : (diagonalConormal f).val.Derivation' f.pullbackPresheafToPresheaf}
    (h₁ : IsDiagonalConormalDerivation f D₁)
    (h₂ : IsDiagonalConormalDerivation f D₂) : D₁ = D₂ := by sorry

end AlgebraicGeometry
