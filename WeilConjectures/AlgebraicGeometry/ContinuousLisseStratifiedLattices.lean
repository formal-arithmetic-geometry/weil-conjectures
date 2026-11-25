/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficients
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.LocallyFree
import WeilConjectures.AlgebraicGeometry.ContinuousLissePullbackSystem
import WeilConjectures.AlgebraicGeometry.ContinuousLisseCoefficientDescent
import WeilConjectures.AlgebraicGeometry.ContinuousEtaleLocalLattices
import WeilConjectures.AlgebraicGeometry.EtaleStratifiedFinite

/-! # Lattices on finitely many strata of a continuous local system

## References

* Bhatt--Scholze, Lemma 6.8.13
-/

@[expose] public section

universe u

open CategoryTheory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

private theorem continuousLisse_stratified_lattices_of_system
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E]
    [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (D : PullbackSystem.{u} ℓ E)
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X))
    (hP : IsLocallyFree (condensedRingObj (Profinite.continuousMapRingObj E) X) P) :
    ∃ S : Scheme.Stratification X, ∀ s : Fin S.n,
      ∃ M : Mod (Sheaf (Scheme.ProEt.topology (S.domain s)) Ab.{u + 1})
          (condensedRingObj (integralCoeff ℓ E) (S.domain s)),
        IsLocallyFree (condensedRingObj (integralCoeff ℓ E) (S.domain s)) M ∧
        Nonempty ((Mod.extendScalars
          (coefficientMap (integralScalarMap ℓ E) (S.domain s))).obj M ≅
            (CondensedRing.upperStar (Profinite.continuousMapRingObj E)
              (S.immersion s)).obj P) := by
  obtain ⟨U, p, hp, hs, hc, hqs, M, hM, ⟨e⟩⟩ :=
    continuousLisse_etale_lattice ℓ E X P hP
  let : Etale p := hp
  let : Surjective p := hs
  let : CompactSpace U := hc
  let : QuasiSeparatedSpace U := hqs
  obtain ⟨T, _, hT⟩ := Scheme.exists_etale_stratified_finite p
  let S : Scheme.Stratification X := T
  refine ⟨S, fun s ↦ ?_⟩
  let j := S.immersion s
  let : IsImmersion j := S.isImmersion s
  let V := Limits.pullback p j
  let r : V ⟶ U := Limits.pullback.fst p j
  let q : V ⟶ S.domain s := Limits.pullback.snd p j
  let : IsFinite q := (hT s).1
  let : Etale q := (hT s).2
  let : Surjective q := inferInstanceAs (Surjective (Limits.pullback.snd p j))
  let : TopologicalSpace.NoetherianSpace (S.domain s) :=
    j.isEmbedding.isInducing.noetherianSpace
  exact continuousLisse_coefficient_lattice_on_stratum ℓ E D
    (X := X) (U := U) (V := V) (W := S.domain s) p j r q
    (Limits.pullback.condition (f := p) (g := j)) P hP M hM e

/-- A locally finite free rational sheaf admits locally free integral lattices after a finite
stratification. (Bhatt--Scholze, Lemma 6.8.13) -/
theorem continuousLisse_stratified_lattices
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E]
    [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X))
    (hP : IsLocallyFree (condensedRingObj (Profinite.continuousMapRingObj E) X) P) :
    ∃ S : Scheme.Stratification X, ∀ s : Fin S.n,
      ∃ M : Mod (Sheaf (Scheme.ProEt.topology (S.domain s)) Ab.{u + 1})
          (condensedRingObj (integralCoeff ℓ E) (S.domain s)),
        IsLocallyFree (condensedRingObj (integralCoeff ℓ E) (S.domain s)) M ∧
        Nonempty ((Mod.extendScalars
          (coefficientMap (integralScalarMap ℓ E) (S.domain s))).obj M ≅
            (CondensedRing.upperStar (Profinite.continuousMapRingObj E)
              (S.immersion s)).obj P) := by
  exact continuousLisse_stratified_lattices_of_system ℓ E
    (canonicalPullbackSystem ℓ E) X P hP

end AlgebraicGeometry.ProEtale.CondensedRing
