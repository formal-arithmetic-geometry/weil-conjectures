/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromyPullback
public import WeilConjectures.WeilSheaf.GeometricFiberPullback
public import WeilConjectures.WeilSheaf.Tensor
public import WeilConjectures.WeilSheaf.WeilDescentFundamentalGroup

/-!
# Weil fundamental representations of pulled-back sheaves and of constant twists

Let `X₀` be a scheme over the finite field `K`, `π : X ⟶ X₀` the projection of its geometric
fibre and `B = (t, β)` base point data, with Weil group `W = π₁(X, t) ⋊ ℤ`, and monodromies `M₀`
on `X₀` and `M` on `X` compatible with `π` (`AlgebraicGeometry.ProEtale.LisseMonodromy.IsCompatible`).

* `AlgebraicGeometry.FrobeniusBasePoint.fundamentalRep_geometricFiberPullback`: for a lisse sheaf
  `H` on `X₀`, the Weil fundamental representation of the Weil sheaf `π^* H` (with its canonical
  Weil structure, `AlgebraicGeometry.WeilSheaf.geometricFiberPullback`) is, under the
  identification `H_{t ≫ π} ≅ (π^* H)_t`, the restriction of the monodromy representation of
  `π₁(X₀, t ≫ π)` on `H_{t ≫ π}` along `toArith : W → π₁(X₀, t ≫ π)`.
* `AlgebraicGeometry.FrobeniusBasePoint.WeilData.fundamentalRep_constantTwist`: the Weil
  fundamental representation of a constant twist `ℱ ⊗ 𝓑_b` is the twist `ρ_ℱ ⊗ b ^ deg`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.FrobeniusBasePoint

open ProEtale Scheme.FiniteEtale Representation

variable {K : Type u} [Field K] [Finite K] {X : Scheme.{u}} [X.Over (Spec (.of K))]
  {l : ℕ} [Fact l.Prime] [Fact (ringChar K ≠ l)]

/-- **The Weil fundamental representation of a constant twist** `ℱ ⊗ 𝓑_b` is the twist
`ρ_ℱ ⊗ b ^ deg` of that of `ℱ`: the twist multiplies the Weil structure, hence the Frobenius `Φ`
of the stalk, by `b`, and does not change the underlying sheaf. -/
theorem WeilData.fundamentalRep_constantTwist {B : FrobeniusBasePoint K X} {W : Type*} [Group W]
    (D : B.WeilData W) (M : LisseMonodromy l (X ↘ Spec (.of K)).geometricFiber K)
    (F : WeilSheaf K l X) (hF : F.IsLisse) (b : (PadicAlgCl l)ˣ) (w : W) :
    D.fundamentalRep M (F.constantTwist b) hF w =
      (D.fundamentalRep M F hF).twist (degreeCharacter D.deg b) w := by
  sorry

variable (B : FrobeniusBasePoint K X) (M₀ : LisseMonodromy l X K)
  (M : LisseMonodromy l (X ↘ Spec (.of K)).geometricFiber K)

/-- **The Weil fundamental representation of a pulled-back sheaf.** For monodromies `M₀` on
`X₀` and `M` on its geometric fibre compatible with the projection `π`, and a lisse sheaf `H`
on `X₀`, the identification `H_{t ≫ π} ≅ (π^* H)_t` intertwines the monodromy of `H` along the
image `toArith w ∈ π₁(X₀, t ≫ π)` of `w ∈ W` with the Weil fundamental representation of the
Weil sheaf `π^* H`. On `π₁(X, t)` this is the compatibility of the monodromies; at the lift of
the Frobenius it says that the Frobenius `Φ` of `π^* H`, built from `β` and the canonical Weil
structure `Fr^* π^* H ≅ (Fr ≫ π)^* H = π^* H`, is the monodromy of `H` along `π_* β`. -/
theorem fundamentalRep_geometricFiberPullback
    (hc : LisseMonodromy.IsCompatible (X ↘ Spec (.of K)).geometricFiberProj M₀ M)
    (H : LisseSheaf l X) (w : B.WeilGroup)
    (v : LisseMonodromy.StalkSpace (B.t ≫ (X ↘ Spec (.of K)).geometricFiberProj) H) :
    LisseMonodromy.upperStarStalkLinearEquiv (X ↘ Spec (.of K)).geometricFiberProj B.t H
        (M₀.rep (B.t ≫ (X ↘ Spec (.of K)).geometricFiberProj) H (B.toArith w) v) =
      B.weilData.fundamentalRep M (WeilSheaf.geometricFiberPullback (k₀ := K) H.property)
        (WeilSheaf.isLisse_geometricFiberPullback H.property) w
        (LisseMonodromy.upperStarStalkLinearEquiv (X ↘ Spec (.of K)).geometricFiberProj B.t H v) := by
  sorry

end AlgebraicGeometry.FrobeniusBasePoint
