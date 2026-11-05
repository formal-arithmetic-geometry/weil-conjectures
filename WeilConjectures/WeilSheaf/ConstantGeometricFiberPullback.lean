/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Constant
public import WeilConjectures.WeilSheaf.ConstantFieldPullback
public import WeilConjectures.WeilSheaf.ConstantTwistCohomology
public import WeilConjectures.WeilSheaf.GeometricFiberPullback
public import WeilConjectures.WeilSheaf.TateTwist
import WeilConjectures.WeilSheaf.FieldCoefficientTateTwist

/-!
# The constant Weil sheaf and its constant twists as pulled-back Weil sheaves

The constant Weil sheaf `ℚ̄_ℓ` on a `k₀`-scheme `X`
(`AlgebraicGeometry.ProEtaleWeilSheaf.adicConstant`) is the constant `ℓ`-adic sheaf on the
geometric fibre `X̄` with the Weil structure `(Fr_X⁻¹)_* ℚ̄_ℓ ≅ ℚ̄_ℓ` of the constant sheaf. It is
also the pullback `p^* ℚ̄_ℓ,X₀` of the constant sheaf of the model `X₀` along `p : X̄ ⟶ X₀`, with
the canonical Weil structure of pulled-back sheaves
(`AlgebraicGeometry.ProEtaleWeilSheaf.geometricFiberPullback`); the two Weil structures agree
under the identification `p^* ℚ̄_ℓ,X₀ ≅ ℚ̄_ℓ,X̄`
(`AlgebraicGeometry.ProEtaleWeilSheaf.adicConstantIsoGeometricFiberPullbackUnit`). Hence the
constant twist `ℚ̄_ℓ ⊗ 𝓑_b` is the pullback `p^* ℚ̄_ℓ,X₀` with its canonical Weil structure
multiplied by `b` (`AlgebraicGeometry.ProEtaleWeilSheaf.geometricFiberPullbackTwist`), and so is
the Tate sheaf `ℚ̄_ℓ(1)` with `b = χ_ℓ(σ)`
(`AlgebraicGeometry.WeilSheaf.tateTwistSheafOneObjIsoGeometricFiberPullbackTwist`).

This is the native half of the comparison of the Tate twist of Weil complexes with the
roots-of-unity Tate twist of the condensed model, needed by smooth purity
(`AlgebraicGeometry.WeilComplex.exists_natTrans_upperShriek_isIso_forget_of_smooth`): through
`AlgebraicGeometry.ProEtaleWeilSheaf.geometricFiberPullbackCompToCondensedIso`, the condensed
image of `ℚ̄_ℓ(1)` is the pullback of the condensed unit with its canonical Weil structure
multiplied by `χ_ℓ(σ)`.
-/

@[expose] public section

universe u

open CategoryTheory Endofunctor

namespace AlgebraicGeometry

namespace ProEtale

variable {l : ℕ} [Fact l.Prime]

end ProEtale

open ProEtale

namespace ProEtaleWeilSheaf

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

/-- The Weil structure of the constant Weil sheaf, unfolded. -/
lemma adicConstant_obj_str :
    (adicConstant k₀ l X).obj.str =
      (adicLowerStarUnitIso l (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.symm).hom :=
  rfl

end ProEtaleWeilSheaf

namespace WeilSheaf

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

end WeilSheaf

end AlgebraicGeometry
