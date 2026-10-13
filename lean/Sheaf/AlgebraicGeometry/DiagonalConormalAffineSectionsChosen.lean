module

public import Sheaf.AlgebraicGeometry.DiagonalConormalDerivation
import Sheaf.AlgebraicGeometry.DiagonalConormalAffineSectionsUnique

@[expose] public section

universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry
variable {X S : Scheme.{u}}

/-- The affine coordinate calculation for the canonical normalized derivation chosen by
`exists_diagonalConormalDerivation`.  This is the geometric affine calculation of Tags
01KJ, 01R3 and 08S2; the proof is intentionally isolated so the supplied-derivation
statement only performs transport along uniqueness. (blueprint: stage3-diagonal-conormal-chosen).
Proof: write A = Γ(X,U) and R = Γ(S,V). On W = U ×_V U the diagonal is the
closed immersion Spec(A) → Spec(A ⊗[R] A) induced by multiplication μ. Restrict
its actual sheaf-module kernel to W, obtaining the ideal ker μ. Restriction and
tensor pullback identify the conormal sections over U with (ker μ)/(ker μ)²,
compatibly with the canonical tensor-pullback unit. The multiplication-ideal
construction of KaehlerDifferential gives an A-linear equivalence with this same
quotient. Compose the two equivalences. The class of 1 ⊗ a - a ⊗ 1 corresponds
to d a on the differential side and to the chosen derivation's value on the
conormal side, by Classical.choose_spec and its normalization formula. Thus the
composite has the required d-formula. W is affine without assuming f separated. -/
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
    (h₂ : IsDiagonalConormalDerivation f D₂) : D₁ = D₂ := by
  ext U a
  exact diagonalConormal_affine_sections_unique f U.unop D₁ D₂ h₁ h₂ a

end AlgebraicGeometry
