/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.InternalHom
public import WeilConjectures.SixFunctors.ProEtale.Adic.OpenImmersion

/-!
# The projection formula for the extension by zero of `ℓ`-adic sheaves

For an open immersion `j : U ⟶ X` and sheaves `K` on `U` and `M` on `X` of `ℚ̄_ℓ`-modules,
`j_!(K ⊗ j^* M) ≅ j_! K ⊗ M`
(`AlgebraicGeometry.ProEtale.adicOpenImmersionLowerShriekTensorLeftIso`): the right adjoints
`j^* 𝓗om(M, -)` and `𝓗om(j^* M, j^* -)` agree, pullback along the weakly étale `j` commuting
with internal homs (`AlgebraicGeometry.ProEtale.adicUpperStarIhomIso`).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime] {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

variable (l) in
/-- **The projection formula for the extension by zero**: `j_!(K ⊗ j^* M) ≅ j_! K ⊗ M` for an
open immersion `j`, naturally in `K`. -/
noncomputable def adicOpenImmersionLowerShriekTensorLeftIso (M : AdicSheaf l X) :
    Mod.tensorLeft ((j)^*ᵃ[l].obj M) ⋙ (j)_!ᵃ[l] ≅ (j)_!ᵃ[l] ⋙ Mod.tensorLeft M :=
  ((conjugateIsoEquiv ((adicOpenImmersionLowerShriekAdjunction l j).comp (Mod.ihomAdjunction M))
    ((Mod.ihomAdjunction ((j)^*ᵃ[l].obj M)).comp (adicOpenImmersionLowerShriekAdjunction l j))).symm
    (adicUpperStarIhomIso l j M))

end AlgebraicGeometry.ProEtale
