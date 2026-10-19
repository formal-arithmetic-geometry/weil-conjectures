/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N9
-/
module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.Localization.AsSubring
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Ideal.Height
import WeilConjectures.RingTheory.LocalizationPrimeResidueFieldIso
import Sheaf.TraceFormula.NormalizationFinitePrimeFibres
import WeilConjectures.Mathlib.RingTheory.Ideal.HasGoingUp

@[expose] public section

set_option autoImplicit false

universe u v

/-- A finite type intermediate algebra isolates a prime of the normalization of a
Noetherian integral domain.

Source: Swanson--Huneke, *Integral Closure of Ideals, Rings, and Modules*,
Lemma 4.8.4, printed p. 85 (PDF p. 99), including the conclusions following
“In particular”. The localization, dimension, and height conventions are those
of the definitions cited by the corresponding blueprint node.

The proof is deferred. It follows the finite-fibre separation argument: choose
one element separating the given prime from the other primes over its
contraction, take the resulting monogenic intermediate algebra, and use
localization of integral closures and prime correspondence to identify the
localized normalization and its dimension.
(blueprint: lem-trf-normalization-finite-local-model)
-/
theorem exists_finiteType_intermediate_algebra_isolating_prime
    (R : Type u) (K : Type v) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (Q : Ideal (integralClosure R K)) [Q.IsPrime] :
    ∃ C : Subalgebra R (integralClosure R K),
      Algebra.FiniteType R C ∧
      let p : Ideal C := Ideal.comap (algebraMap C (integralClosure R K)) Q
      p.IsPrime ∧
      (∀ Q' : Ideal (integralClosure R K), Q'.IsPrime →
        Ideal.comap (algebraMap C (integralClosure R K)) Q' = p → Q' = Q) ∧
      IsDomain (Localization.AtPrime p) ∧
      IsNoetherianRing (Localization.AtPrime p) ∧
      ringKrullDim (Localization.AtPrime p) =
        ringKrullDim (Localization.AtPrime Q) ∧
      ringKrullDim (Localization.AtPrime Q) = (Q.height : WithBot ℕ∞) ∧
      (∃ jC : Localization.AtPrime p →+* K,
        ∃ jQ : Localization.AtPrime Q →+* K,
          jC.comp (algebraMap C (Localization.AtPrime p)) =
              (algebraMap (integralClosure R K) K).comp (algebraMap C (integralClosure R K)) ∧
          jQ.comp (algebraMap (integralClosure R K) (Localization.AtPrime Q)) =
              algebraMap (integralClosure R K) K ∧
          (letI : Algebra (Localization.AtPrime p) K := jC.toAlgebra
           letI : Algebra (Localization.AtPrime Q) K := jQ.toAlgebra
           IsIntegralClosure (Localization.AtPrime Q) (Localization.AtPrime p) K)) := by
  sorry

end
