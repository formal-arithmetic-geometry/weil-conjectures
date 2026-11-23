/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.FrobeniusCorrespondenceOperator
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReduction
public import WeilConjectures.TraceFormula.IntegralCompactPullback
public import WeilConjectures.TraceFormula.IntegralPointUnitEnd

/-!

# Reduction of the integral traces modulo `ℓⁿ`

Let `E ⊆ ℚ̄_ℓ` be a finite extension of `ℚ_ℓ` with ring of integers `𝒪_E`, `K` a bounded
constructible `𝒪_E`-complex on `X` and `θ : LΦ^* K ⟶ K` an integral Frobenius correspondence
for a proper endomorphism `Φ`. Write `K_n` for the reduction of `K` modulo `ℓⁿ`, read on the
small étale site (`ProEtale.CondensedRing.etaleReduction`), and `θ̄_n : LΦ^* K_n ⟶ K_n` for the
reduction of `θ`. This file states that the traces of the operators of `θ` reduce modulo `ℓⁿ` to
the traces of the operators of `θ̄_n` with coefficients `𝒪_E ⧸ ℓⁿ`
(`ProEtale.CondensedRing.PadicIntegersRingObj.trace_reduction`): both for the operator
`T_{c_m}(θ_m)` on `RΓ_c(X, K)` and for the stalk maps `θ_{m,x}` at the fixed points of `Φ_m`.

## Main results

- `ProEtale.CondensedRing.PadicIntegersRingObj.etaleReductionFrobenius`: the reduction
  `θ̄_n : LΦ^* K_n ⟶ K_n`.
- `ProEtale.CondensedRing.PadicIntegersRingObj.trace_reduction`: the reductions of the integral
  traces.

## Implementation details

The integral traces are endomorphisms of the unit of `Dᵇc(Spec k)⟦𝒪_E⟧`, that is scalars of
`𝒪_E` (`ProEtale.CondensedRing.PadicIntegersRingObj.surjective_integersUnitEndRingHom`); the
traces with coefficients `𝒪_E ⧸ ℓⁿ` are endomorphisms of the unit of `D(𝒪_E ⧸ ℓⁿ)`, that is
scalars of `𝒪_E ⧸ ℓⁿ`. The reduction is taken modulo `ℓⁿ`, as for
`ProEtale.CondensedRing.etaleReduction`, rather than modulo `π_E^n`; the two families of ideals
are cofinal.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.PadicIntegersRingObj

open Scheme PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (E : PadicAlgCl.FiniteIntermediateField ℓ) (n : ℕ)
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

/-- The reduction `𝒪_E →+* 𝒪_E ⧸ ℓⁿ`, with values in the universe-lifted coefficient ring of the
étale reduction. -/
noncomputable def integersModPowCoeffMk : integers ℓ E.1 →+* integersModPowCoeff.{u} ℓ E.1 n :=
  ULift.ringEquiv.symm.toRingHom.comp (integersModPowMk ℓ E.1 n)

/-- The reduction `θ̄_n : LΦ^* K_n ⟶ K_n` modulo `ℓⁿ` of a morphism `θ : LΦ^* K ⟶ K` of bounded
constructible `𝒪_E`-complexes, read on the small étale site. -/
noncomputable def etaleReductionFrobenius {Φ : X ⟶ X}
    {K : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧}
    (θ : (boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E.1) ℓ Φ).obj K ⟶ K) :
    L(Etale.upperStar (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E.1 n)) Φ.left).obj
        ((etaleReduction ℓ E.1 n X).obj K) ⟶ (etaleReduction ℓ E.1 n X).obj K :=
  (etaleReductionUpperStarIso ℓ E.1 n Φ).inv.app K ≫ (etaleReduction ℓ E.1 n X).map θ

attribute [local instance] boundedConstructibleBraiding DerivedCategory.braidedCategory'

/-- **The integral traces reduce to the traces modulo `ℓⁿ`**: for a proper endomorphism `Φ`,
an integral Frobenius correspondence `θ : LΦ^* K ⟶ K` and `m, n ∈ ℕ`, the trace of the operator
`T_{c_m}(θ_m)` on `RΓ_c(X, K)` is a scalar `a ∈ 𝒪_E` whose reduction modulo `ℓⁿ` is the trace of
the operator `T_{c_m}((θ̄_n)_m)` on `RΓ_c(X, K_n)`, and the trace of each stalk map `θ_{m,x}` at a
rational point `x` fixed by `Φ_m` is a scalar whose reduction is the trace of `(θ̄_n)_{m,x}`. -/
theorem trace_reduction [IsSepClosed k] {Φ : X ⟶ X} [IsProper Φ.left]
    (K : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧)
    (θ : (boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E.1) ℓ Φ).obj K ⟶ K)
    (m : ℕ) [HasRightDual ((boundedConstructibleLowerShriek ℓ E.1 (toPoint X)).obj K)]
    [∀ x : RationalPoint X,
      HasRightDual
        ((boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E.1) ℓ x).obj K)]
    [HasRightDual ((Etale.compactlySupportedGlobalSections
      (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E.1 n)) X.hom).obj
        ((etaleReduction ℓ E.1 n X).obj K))]
    [∀ x : RationalPoint X, HasRightDual
      ((Etale.rightDerivedGlobalSections (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E.1 n))
        (point k).left).obj
          ((L(Etale.upperStar (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E.1 n)) x.left)).obj
            ((etaleReduction ℓ E.1 n X).obj K)))] :
    (∃ a : integers ℓ E.1,
      trace (frobeniusCompactOperator ℓ E.1 θ m) = (integersUnitEndRingHom ℓ k E a).asHom ∧
      trace (Etale.frobeniusCompactOperator (integersModPowCoeff.{u} ℓ E.1 n) Φ.left (Over.w Φ)
        (etaleReductionFrobenius ℓ E n θ) m) =
        (algebraMap (integersModPowCoeff.{u} ℓ E.1 n)
          (End (𝟙_ (DerivedCategory (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E.1 n)))))
          (integersModPowCoeffMk ℓ E n a)).asHom) ∧
    ∀ x : FixedPoint Φ m, ∃ a : integers ℓ E.1,
      trace (graphStalkMap K (frobeniusIterate Φ m) (frobeniusCoefficientIterate θ m) x.1
        x.2) = (integersUnitEndRingHom ℓ k E a).asHom ∧
      trace (Etale.frobeniusStalkMap (x := x.1.left) (h := ProEtale.iterateHom Φ.left m)
        (by rw [ProEtale.iterateHom, ← frobeniusIterate_left, ← Over.comp_left, x.2])
        (Etale.weilDatumIterate (etaleReductionFrobenius ℓ E n θ) m)) =
        (algebraMap (integersModPowCoeff.{u} ℓ E.1 n)
          (End (𝟙_ (DerivedCategory (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E.1 n)))))
          (integersModPowCoeffMk ℓ E n a)).asHom := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing.PadicIntegersRingObj
