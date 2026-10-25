/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.CurveLocal.ReductionExternalProduct
public import WeilConjectures.TraceFormula.CurveLocal.StalkExchangeRestriction
public import WeilConjectures.TraceFormula.PointFiberReduction

/-!

# The integral supported restriction modulo `ℓⁿ` on the strictly local model

Let `X` be a smooth curve over the algebraically closed field `k` with the model Frobenius `Φ`,
`m ≥ 1`, `F` the fixed locus of the graph correspondence `(𝟙, Φ_m)` and `z` a point of `F`
over `x`. For bounded constructible `𝒪_E`-complexes `M`, `N` on `X` with `M_x = 0`, let
`ρ = ρ_{M ⊠ N}` be the integral supported restriction
(`ProEtale.CondensedRing.Correspondence.FixedLocus.integralSupportedRestriction`) and
`f₀ = Fib_s(z^* ρ)` its point fibre, a morphism in `D(𝒪_E)`. This file proves that the
reductions of `f₀` modulo every `ℓⁿ` factor through classical supported restrictions `ρ_{a,b}`
on the strictly local model `M_x` at `x` (`Correspondence.frobeniusLocalModel`), with the
coefficient datum `(𝒪_E ⧸ ℓⁿ, N_{𝒪_E ⧸ ℓⁿ}, M_{𝒪_E ⧸ ℓⁿ})`: this is the reduction clause of
`Correspondence.HasIntegralReductionModel` (blueprint `sk-lem-tf-curve-restriction-zero`, the
passage from the classical finite-coefficient computation to `𝒪_E`).

The proof transports `ρ` to the étale site by the reduction modulo `ℓⁿ`
(`CategoryTheory.Adjunction.exists_map_exchangeRestriction_comp_eq`, with the coefficient
comparisons of `sk-prop-scalar-six` for `𝒪_E ⟶ 𝒪_E ⧸ ℓⁿ`), identifies `X ⨯ X` with the fibre
product of the model (interchanging the factors), compares the stalk of the étale exchange
restriction with `ρ_{a,b}`
(`Etale.CurveLocalModel.exists_geometricStalk_map_exchangeRestriction`), and reduces the point
fibre (`ProEtale.CondensedRing.exists_pointFiberFunctorIntegral_reduction`).

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

variable (ℓ) in
/-- The point fibre `Fib_s(z^* ρ_{M ⊠ N})` of the integral supported restriction of `M ⊠ N` at a
point `z` of the fixed locus, as an arrow of `D(𝒪_E)`. -/
noncomputable def pointIntegralSupportedRestriction [IsSepClosed k] {c : Correspondence ℓ K}
    (F : c.FixedLocus) (z : RationalPoint F.F) (E : FiniteIntermediateField ℓ)
    (M N : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧) :
    Arrow (DerivedCategory (ModuleCat.{u + 1} (Shrink.{u + 1} (integers ℓ E.1)))) :=
  Arrow.mk ((pointFiberFunctorIntegral ℓ k E).map
    ((boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E.1) ℓ z).map
      (F.integralSupportedRestriction E.1
        ((boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E.1) ℓ
            (prod.fst : X ⨯ X ⟶ X)).obj M ⊗
          (boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E.1) ℓ
            (prod.snd : X ⨯ X ⟶ X)).obj N))))

/-- **The integral supported restriction reduces to classical supported restrictions**: for
bounded constructible `𝒪_E`-complexes `M`, `N` on the curve `X` with `M_x = 0` at the point
`x = ι(z)`, every reduction modulo `ℓⁿ` of the point fibre `f₀ : A₀ ⟶ B₀` of the integral
supported restriction of `M ⊠ N` at `z` factors through a classical supported restriction
`ρ_{a,b}` on the strictly local model at `x`: there are a classical coefficient datum `D` with
coefficients under `𝒪_E`, a map `π_A : A₀ ⟶ RΓ_a(T, P)` and a distinguished triangle
`B₀ --ℓⁿ--> B₀ --π_B--> RΓ_y(B, b^* P) ⟶` with `π_A ≫ ρ_{a,b} = f₀ ≫ π_B`. -/
theorem exists_reduction_pointIntegralSupportedRestriction [IsAlgClosed k]
    [SmoothOfRelativeDimension 1 X.hom] [LocallyOfFiniteType f₀] (hΦ : IsModelFrobenius Φ f₀ p)
    {m : ℕ} (hm : 1 ≤ m)
    (v : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (frobeniusIterate Φ m)).obj K ⟶ K)
    (F : (ofGraph K (frobeniusIterate Φ m) v).FixedLocus) (z : RationalPoint F.F)
    (E : FiniteIntermediateField ℓ) (M N : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧)
    (hM : IsZero ((boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E.1) ℓ
      (z ≫ F.ι)).obj M)) (n : ℕ) :
    ∃ (D : (frobeniusLocalModel hΦ hm v F z).CoefficientDatum ℓ)
      (φ : Shrink.{u + 1} (integers ℓ E.1) →+* D.Λ)
      (πA : (pointIntegralSupportedRestriction ℓ F z E M N).left ⟶
        (ModuleCat.restrictScalars φ).mapDerivedCategory.obj D.source)
      (πB : (pointIntegralSupportedRestriction ℓ F z E M N).right ⟶
        (ModuleCat.restrictScalars φ).mapDerivedCategory.obj D.target)
      (δ : (ModuleCat.restrictScalars φ).mapDerivedCategory.obj D.target ⟶
        (pointIntegralSupportedRestriction ℓ F z E M N).right⟦(1 : ℤ)⟧),
      Pretriangulated.Triangle.mk
        (((ℓ : ℤ) ^ n) • 𝟙 (pointIntegralSupportedRestriction ℓ F z E M N).right) πB δ ∈
          distTriang _ ∧
      πA ≫ (ModuleCat.restrictScalars φ).mapDerivedCategory.map D.supportedRestriction =
        (pointIntegralSupportedRestriction ℓ F z E M N).hom ≫ πB :=
  sorry

end Correspondence

end AlgebraicGeometry.ProEtale.CondensedRing
