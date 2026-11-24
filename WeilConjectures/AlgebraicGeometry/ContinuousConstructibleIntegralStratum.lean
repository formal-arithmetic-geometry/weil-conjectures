/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LocallyFreeConstructible
import all WeilConjectures.AlgebraicGeometry.CondensedFieldLfpLocalTriviality
import all WeilConjectures.AlgebraicGeometry.ContinuousConstructibleIntegralTransport
import WeilConjectures.AlgebraicGeometry.ContinuousConstructibleIntegralGluing
import WeilConjectures.AlgebraicGeometry.ContinuousLisseStratifiedLattices
import Mathlib.Algebra.Field.ULift

/-! # Integral models on a locally finitely presented stratum

## References

* Bhatt--Scholze, Lemmas 6.8.12--6.8.13 and Proposition 6.8.14 (2)
-/

@[expose] public section

universe u

open CategoryTheory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
  [FiniteDimensional ℚ_[ℓ] E]

/-- A locally finitely presented rational module on one immersed stratum admits an
ordinary constructible integral model, with both coefficient rings pulled back from X.
No derived comparison or bounded-complex packaging is part of this statement.
(Hemo--Richarz--Scholbach, Example 3.1; Bhatt--Scholze, Lemmas 6.8.2 and 6.8.13) -/
theorem continuousConstructible_integral_stratum (X : Scheme.{u})
    [TopologicalSpace.NoetherianSpace X] {Y : Scheme.{u}} (i : Y ⟶ X) [IsImmersion i]
    (F : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      ((ProEtale.upperStar Ab.{u + 1} i).obj
        (condensedRingObj (Profinite.continuousMapRingObj E) X)))
    (hF : ProEtale.IsLocallyFinitelyPresented
      ((ProEtale.upperStar Ab.{u + 1} i).obj
        (condensedRingObj (Profinite.continuousMapRingObj E) X)) F) :
    ∃ N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        ((ProEtale.upperStar Ab.{u + 1} i).obj (condensedRingObj (integralCoeff ℓ E) X)),
      ProEtale.IsConstructibleModuleObject
        ((ProEtale.upperStar Ab.{u + 1} i).obj (condensedRingObj (integralCoeff ℓ E) X)) N ∧
      Nonempty ((Mod.extendScalars
        ((ProEtale.upperStar Ab.{u + 1} i).map
          (coefficientMap (integralScalarMap ℓ E) X))).obj N ≅ F) := by
  let : TopologicalSpace.NoetherianSpace Y := i.isEmbedding.isInducing.noetherianSpace
  obtain ⟨D⟩ : Nonempty (PullbackCoefficientData ℓ E i) :=
    ⟨pullbackCoefficientData ℓ E i⟩
  obtain ⟨ai, bi, hai, hbi, iai, ibi, wi, _⟩ := D
  let : IsMonHom ai := hai
  let : IsMonHom bi := hbi
  let : IsIso ai := iai
  let : IsIso bi := ibi
  obtain ⟨P, hP, ⟨eP⟩⟩ : ∃ P : Mod _
      (condensedRingObj (Profinite.continuousMapRingObj E) Y),
      ProEtale.IsLocallyFinitelyPresented _ P ∧
        Nonempty (P ≅ (Mod.comap (inv bi)).obj F) :=
    ⟨(Mod.comap (inv bi)).obj F, ProEtale.lfp_comap (inv bi) hF, ⟨Iso.refl _⟩⟩
  obtain ⟨C, hC⟩ := smallField_finiteFree_cover ℓ E Y P hP
  obtain ⟨S, hS⟩ := continuousLisse_stratified_lattices ℓ E Y P ⟨C, hC⟩
  have hmodels : ∀ s : Fin S.n,
      ∃ M : Mod (Sheaf (Scheme.ProEt.topology (S.domain s)) Ab.{u + 1})
          ((ProEtale.upperStar Ab.{u + 1} (S.immersion s)).obj
            (condensedRingObj (integralCoeff ℓ E) Y)),
        ProEtale.IsConstructibleModuleObject
          ((ProEtale.upperStar Ab.{u + 1} (S.immersion s)).obj
            (condensedRingObj (integralCoeff ℓ E) Y)) M ∧
        Nonempty ((Mod.extendScalars
          ((ProEtale.upperStar Ab.{u + 1} (S.immersion s)).map
            (coefficientMap (integralScalarMap ℓ E) Y))).obj M ≅
          ((ProEtale.upperStar Ab.{u + 1} (S.immersion s)).mapMod _).obj P) := fun s ↦ by
    obtain ⟨M, hM, ⟨e⟩⟩ := hS s
    exact pullbackCoefficient_model (integralCoeff ℓ E)
      (Profinite.continuousMapRingObj E) (integralScalarMap ℓ E)
      (X := Y) (Y := S.domain s) (S.immersion s) P M hM.isConstructibleModuleObject e
  obtain ⟨N, hN, ⟨e⟩⟩ := continuousConstructible_integral_gluing ℓ E Y P S hmodels
  exact model_transport (X := Y)
    (R := (ProEtale.upperStar Ab.{u + 1} i).obj (condensedRingObj (integralCoeff ℓ E) X))
    (S := (ProEtale.upperStar Ab.{u + 1} i).obj
      (condensedRingObj (Profinite.continuousMapRingObj E) X))
    (R' := condensedRingObj (integralCoeff ℓ E) Y)
    (S' := condensedRingObj (Profinite.continuousMapRingObj E) Y)
    ((ProEtale.upperStar Ab.{u + 1} i).map (coefficientMap (integralScalarMap ℓ E) X))
    (coefficientMap (integralScalarMap ℓ E) Y)
    ai bi wi F N hN (e ≪≫ eP)

end AlgebraicGeometry.ProEtale.CondensedRing
