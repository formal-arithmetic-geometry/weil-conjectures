/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.CurveLocal.IntegralModelPointStalk
public import WeilConjectures.TraceFormula.CurveLocal.ReductionTransfer
public import WeilConjectures.TraceFormula.PointFiberFunctorIntegralPerfect
public import WeilConjectures.TraceFormula.SupportedRestrictionIntegral

/-!

# The supported restriction is zero for Frobenius, with `ℚ̄_ℓ`-coefficients

This file proves the `ℚ̄_ℓ`-form of blueprint `sk-lem-tf-curve-restriction-zero`
(`ProEtale.CondensedRing.Correspondence.upperStar_map_supportedRestriction_frobeniusGraph_eq_zero`)
from the classical finite-coefficient computation
(`AlgebraicGeometry.Etale.CurveLocalModel.restrictionZero`):

* `K` has an integral model `M` over `𝒪_E` with `M_x = 0`
  (`ProEtale.CondensedRing.exists_integralModel_isZero_upperStar`), and
  `K ⊠ D_X K ≅ ℚ̄_ℓ ⊗ (M ⊠ D_X M)`
  (`ProEtale.CondensedRing.boundedConstructibleIntegersToPadicAlgClExternalProductVerdierDualIso`);
* the reductions modulo every `ℓⁿ` of the point fibre `f₀` of the integral supported restriction
  factor through classical supported restrictions
  (`ProEtale.CondensedRing.Correspondence.exists_reduction_pointIntegralSupportedRestriction`),
  which vanish; `f₀` is a morphism of perfect `𝒪_E`-complexes
  (`ProEtale.CondensedRing.isPerfect_pointFiberFunctorIntegral_obj`), so it vanishes by the Krull
  intersection theorem;
* the vanishing passes from `𝒪_E` to `E` to `ℚ̄_ℓ`
  (`ProEtale.CondensedRing.Correspondence.FixedLocus.map_supportedRestrictionIntegral_comp`,
  `ProEtale.CondensedRing.Correspondence.FixedLocus.upperStar_map_supportedRestriction_eq_zero_of_supportedRestrictionE`),
  the point fibre functor being faithful.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

attribute [local instance] boundedConstructibleBraiding

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}

namespace Correspondence

variable {k₀ : Type u} [Field k₀] [Finite k₀] [Algebra k₀ k] {X₀ : Scheme.{u}}
  {f₀ : X₀ ⟶ Spec (.of k₀)} {p : X.left ⟶ X₀} {Φ : X ⟶ X}

/-- **The supported restriction is zero for Frobenius** (SGA 5, III B, §§2–4). Let `X` be
smooth of relative dimension one over the algebraically closed field `k`, with the model
Frobenius `Φ` of a model over a finite field, `m ≥ 1`, `v : LΦ_m^* K ⟶ K` arbitrary, and let `z`
be a point of the fixed locus of the graph correspondence `(𝟙, Φ_m)` whose image `x` in `X`
has `K_x = 0`. Then the stalk at `z` of the supported restriction
`ρ_P : Lι^* Rc^! P ⟶ Rd^! LΔ^* P`, `P = K ⊠ D_X K`
(`Correspondence.FixedLocus.supportedRestriction`), vanishes.

This is the `ℚ̄_ℓ`-form of the blueprint statement: the stalk of `ρ_P` at `z` is the supported
restriction `ρ_{a,b} : RΓ_a(T, P) ⟶ RΓ_x(b, b^* P)` on the strict localization `T` of `X ⨯ X`
at `(x, x)`, from the Frobenius graph `a` to the diagonal `b`. The blueprint shows
`ρ_{a,b} = 0` in `D(A)` for every finite `ℓ`-primary ring `A` (localization to the punctured
diagonal, covers of degree prime to `ℓ`, and the blowup argument of
`sk-lem-tf-blowup-restriction`); the `ℚ̄_ℓ`-form follows by the integral models of
`sk-lem-tf-rational-model`. The coefficient map `v` plays no role: `ρ_P` only depends on the
correspondence and on `P`. -/
theorem upperStar_map_supportedRestriction_frobeniusGraph_eq_zero [IsAlgClosed k]
    [SmoothOfRelativeDimension 1 X.hom] [LocallyOfFiniteType f₀] (hΦ : IsModelFrobenius Φ f₀ p)
    {m : ℕ} (hm : 1 ≤ m)
    (v : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (frobeniusIterate Φ m)).obj K ⟶ K)
    (F : (ofGraph K (frobeniusIterate Φ m) v).FixedLocus) (z : RationalPoint F.F)
    (hK : IsZero ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (z ≫ F.ι)).obj K)) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ z).map
      (F.supportedRestriction (externalProduct ℓ K (verdierDual ℓ (toPoint X) K))) = 0 :=
  sorry

end Correspondence

end AlgebraicGeometry.ProEtale.CondensedRing
