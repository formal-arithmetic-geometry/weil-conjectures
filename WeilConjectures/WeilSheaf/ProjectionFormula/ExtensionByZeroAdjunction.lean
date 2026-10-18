/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraLeftAdjunction
public import WeilConjectures.SixFunctors.ProEtale.Adic.ExchangeMate
public import WeilConjectures.WeilSheaf.OpenImmersion
public import WeilConjectures.WeilSheaf.UpperStarLowerStarAdjunction

/-!
# The adjunction `j_! ⊣ j^*` of pro-étale Weil sheaves

For an open immersion `j : U ⟶ X` of `k₀`-schemes, the extension by zero `j_!` of pro-étale
Weil sheaves is left adjoint to the pullback `j^*`
(`AlgebraicGeometry.ProEtaleWeilSheaf.extensionByZeroUpperStarAdjunction`): the adjunction
`j̄_! ⊣ j̄^*` along the base change lifts, since its unit and counit are compatible with the Weil
structures. This follows from the compatibility of the comparison `j̄_! ⟶ j̄_*` with the Weil
structures and the adjunction `j^* ⊣ j_*` of pro-étale Weil sheaves
(`CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIsoLeftAdjunction`).
-/

@[expose] public section

universe u

open CategoryTheory Endofunctor

namespace AlgebraicGeometry

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
variable {U X : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
  [X.Over (Spec (CommRingCat.of k₀))]

variable (k₀ l) in
/-- **The adjunction `j_! ⊣ j^*` of pro-étale Weil sheaves** along an open immersion `j`. -/
noncomputable def ProEtaleWeilSheaf.extensionByZeroUpperStarAdjunction (j : U ⟶ X)
    [IsOpenImmersion j] [j.IsOver (Spec (CommRingCat.of k₀))] :
    ProEtaleWeilSheaf.extensionByZero k₀ l j ⊣ ProEtaleWeilSheaf.upperStar k₀ l j :=
  IsoAlgebra.mapOfNatIsoLeftAdjunction
    (adicOpenImmersionLowerShriekAdjunction l
      (Scheme.Hom.geometricFiberMap j (comp_over j (Spec (CommRingCat.of k₀)))))
    (adicUpperStarLowerStarAdjunction l
      (Scheme.Hom.geometricFiberMap j (comp_over j (Spec (CommRingCat.of k₀)))))
    _ _ _ (mateEquiv_adicUpperStarGeometricFiberMapCompFrobeniusIso_inv l j _) _
    (adicOpenImmersionLowerShriekToLowerStar_geometricFiberMapCompFrobeniusIso l j _)
    (adicOpenImmersionLowerShriekAdjunction_unit_app_comp_map_lowerShriekToLowerStar (l := l) _)

end AlgebraicGeometry
