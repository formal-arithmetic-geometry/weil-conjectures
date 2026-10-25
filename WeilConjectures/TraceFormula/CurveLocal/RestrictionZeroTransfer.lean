/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.CurveLocal.RestrictionZero
public import WeilConjectures.TraceFormula.CurveSupportedPairing

/-!

# From finite coefficients to `ℚ̄_ℓ`: the supported restriction is zero for Frobenius

Blueprint `sk-lem-tf-curve-restriction-zero` is proved on the classical étale models with finite
`ℓ`-primary coefficients
(`AlgebraicGeometry.Etale.CurveLocalModel.sectionsWithSupportRestriction_eq_zero`,
packaged for all models and coefficient rings as
`AlgebraicGeometry.Etale.CurveLocalModel.restrictionZero`). Its last step, as in the blueprint
proof ("the comparison theorems transport this identity back to the proétale formulation"),
transports this vanishing to the `ℚ̄_ℓ`-coefficient pro-étale supported restriction `ρ_P` of
`Correspondence.FixedLocus.supportedRestriction`: the stalk of `ρ_P` at the fixed point is the
supported restriction on the strict localization `T` of `X ×_k X` at `(x, x)`, the comparison
theorems identify it with the étale one, and the integral models of `sk-lem-tf-rational-model`
reduce `ℚ̄_ℓ` to the finite rings `𝒪_E / π_E^n`. This transport is stated as a compatibility
(`Correspondence.upperStar_map_supportedRestriction_frobeniusGraph_eq_zero_of_restrictionZero`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.Etale.CurveLocalModel

variable (k : Type u) [Field k] [IsAlgClosed k] (ℓ : ℕ)

/-- **The supported restriction is zero for Frobenius, for all models and coefficient rings**
(blueprint `sk-lem-tf-curve-restriction-zero`): for every strictly local model of a smooth curve
over `k`, every finite commutative `ℓ`-primary ring `Λ`, all `L, K ∈ D^b_{ctf}(X, Λ)` with
`K_ȳ = 0` and `P = (L ⊠ K)|_T`, the supported restriction `ρ_{a,b}` is zero. -/
def RestrictionZero : Prop :=
  ∀ (M : CurveLocalModel k) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ],
    (∃ n : ℕ, (ℓ : Λ) ^ n = 0) →
    ∀ (L K : DerivedCategory (Sheaf M.X.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      DerivedCategory.boundedConstructibleFiniteTor Λ M.X L →
      DerivedCategory.boundedConstructibleFiniteTor Λ M.X K →
      IsZero ((L((M.y)^*[ModuleCat.{u + 1} Λ])).obj K) →
      ∀ (P : DerivedCategory.Plus (Sheaf M.T.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
        (P.obj ≅ (L((M.τ)^*[ModuleCat.{u + 1} Λ])).obj
          (externalProduct (ModuleCat.{u + 1} Λ) M.f M.f L K)) →
        sectionsWithSupportRestriction (ModuleCat.{u + 1} Λ) M.b M.a M.yB
          M.openComplement_yB_le P = 0

variable {k ℓ}

/-- `RestrictionZero` holds for every prime `ℓ` invertible in `k` (blueprint
`sk-lem-tf-curve-restriction-zero`). -/
theorem restrictionZero [Fact ℓ.Prime] (hℓ : (ℓ : k) ≠ 0) : RestrictionZero k ℓ :=
  fun M _ _ _ hΛ L K hL hK hKy P eP ↦
    M.sectionsWithSupportRestriction_eq_zero ℓ hℓ hΛ L K hL hK hKy P eP

end AlgebraicGeometry.Etale.CurveLocalModel

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}

/-- A prime `ℓ` different from the characteristic of `k` is invertible in `k`. -/
lemma natCast_ne_zero_of_ringChar_ne : (ℓ : k) ≠ 0 := by
  intro h
  have h₁ := (ringChar.spec k ℓ).1 h
  have hp : (ringChar k).Prime := Fact.out
  have hℓ : ℓ.Prime := Fact.out
  exact (Fact.out : ringChar k ≠ ℓ) ((Nat.prime_dvd_prime_iff_eq hp hℓ).1 h₁)

namespace Correspondence

variable {k₀ : Type u} [Field k₀] [Finite k₀] [Algebra k₀ k] {X₀ : Scheme.{u}}
  {f₀ : X₀ ⟶ Spec (.of k₀)} {p : X.left ⟶ X₀} {Φ : X ⟶ X}

/-- Compatibility required from `sk-lem-tf-rational-model` and from the comparison theorems of the
six-functor formalism (`sk-thm-sf-package`: étale and pro-étale six operations, supports and
strict localizations) (to be proved there): **transport of the vanishing of the supported
restriction from finite coefficients to `ℚ̄_ℓ`**. If the supported restriction on the classical
strictly local models vanishes for all finite `ℓ`-primary coefficient rings
(`AlgebraicGeometry.Etale.CurveLocalModel.RestrictionZero`), then, for `X` smooth of relative
dimension one over the algebraically closed field `k` with the model Frobenius `Φ` of a model over
a finite field, `m ≥ 1`, `v : LΦ_m^* K ⟶ K`, and a point `z` of the fixed locus of `(𝟙, Φ_m)`
whose image `x` in `X` has `K_x = 0`, the stalk at `z` of the `ℚ̄_ℓ`-coefficient supported
restriction `ρ_P`, `P = K ⊠ D_X K`, vanishes. The stalk of `ρ_P` at `z` is the supported
restriction on the strict localization of `X × X` at `(x, x)` (blueprint
`det-tf-supported-restriction-local-term`); by `sk-lem-tf-rational-model` the complex `K` has an
integral model whose reductions `K_n` modulo `π_E^n` satisfy `(K_n)_x = 0`, the comparison
theorems identify the pro-étale supported restriction of `K_n ⊠ D_X K_n` with the étale one on the
classical model, and a morphism of perfect `𝒪_E`-complexes vanishing modulo every `π_E^n`
vanishes. -/
theorem upperStar_map_supportedRestriction_frobeniusGraph_eq_zero_of_restrictionZero
    [IsAlgClosed k] [SmoothOfRelativeDimension 1 X.hom] [LocallyOfFiniteType f₀]
    (hΦ : IsModelFrobenius Φ f₀ p) {m : ℕ} (hm : 1 ≤ m)
    (v : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (frobeniusIterate Φ m)).obj K ⟶ K)
    (F : (ofGraph K (frobeniusIterate Φ m) v).FixedLocus) (z : RationalPoint F.F)
    (hK : IsZero ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (z ≫ F.ι)).obj K))
    (_ : Etale.CurveLocalModel.RestrictionZero k ℓ) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ z).map
      (F.supportedRestriction (externalProduct ℓ K (verdierDual ℓ (toPoint X) K))) = 0 :=
  sorry

end Correspondence

end AlgebraicGeometry.ProEtale.CondensedRing
