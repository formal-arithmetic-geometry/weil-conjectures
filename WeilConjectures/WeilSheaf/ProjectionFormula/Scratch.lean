module

public import WeilConjectures.WeilSheaf.ProjectionFormula.UpperStarTensor

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits Functor.LaxMonoidal

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime] {T₁ T₂ : Scheme.{u}}

lemma test1 (j : T₁ ⟶ T₂) (a : T₁ ≅ T₁) (M : AdicSheaf l T₂) :
    (upperStarIsoLowerStarInv (WeilCoefficients.{u} l) a).inv.app ((j)^*ᵃ[l].obj M).X =
    (upperStarIsoLowerStarInv (WeilCoefficients.{u} l) a).inv.app
      ((j)^*[WeilCoefficients.{u} l].obj M.X) := rfl

end AlgebraicGeometry.ProEtale
