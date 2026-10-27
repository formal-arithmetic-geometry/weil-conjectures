/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NQ
-/
module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Defs
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.Localization.Submodule
import WeilConjectures.RingTheory.AdicCompletionNoetherian

/-! # Completed-base tensor comparison at primes over the adic ideal

Source: Stacks Project, algebra.tex, Tag 05GG (lemma-hathat-finitely-generated),
with the balanced-tensor and localized finite-quotient consequence of the DAG proof
(blueprint: lem-trf-adic-base-tensor-local-comparison).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

universe u v

namespace RingTheory

/-- The tensor algebra with the completed base, in the factor order of the statement.
Source: Stacks Project, Tag 05GG, balanced-tensor consequence
(blueprint: lem-trf-adic-base-tensor-local-comparison). -/
abbrev AdicBaseTensor {R : Type u} [CommRing R] (I : Ideal R)
    (U : Type v) [CommRing U] [Algebra R U] :=
  TensorProduct R (AdicCompletion I R) U

/-- The canonical inclusion of the original algebra into the completed-base tensor algebra.
Source: Stacks Project, Tag 05GG, balanced-tensor consequence
(blueprint: lem-trf-adic-base-tensor-local-comparison). -/
noncomputable def adicBaseTensorInclusion {R : Type u} [CommRing R] (I : Ideal R)
    (U : Type v) [CommRing U] [Algebra R U] : U →+* AdicBaseTensor I U :=
  (Algebra.TensorProduct.includeRight (R := R) (A := AdicCompletion I R) (B := U)).toRingHom

/-- The canonical local map preserves all positive maximal-ideal quotients and their
inverse limits, including the inverse coefficient formula and both adic continuities.
The first quotient equivalence characterizes the prime in the completed-base tensor.
The equivalence at index zero is the canonical identification of residue fields.

Source: Stacks Project, algebra.tex, Tag 05GG (lemma-hathat-finitely-generated),
and the agent-supplied localized balanced-tensor consequence.

Proof:
1. The completion is Noetherian by lem-weil-pbc-adic-completion-noetherian.
   Finite algebra generators of U tensor to generators over the completion, so
   lem-weil-pbc-finite-type-algebra-noetherian makes the tensor algebra Noetherian.
   Its ring structure and interchange of factors are those of
   lem-weil-pbc-algebra-tensor-pushout-universal-property.
2. Noetherianity makes I finitely generated. The projections supplied by
   lem-weil-pbc-adic-completion-mod-power, followed by
   lem-trf-tensor-base-change-ideal-power-quotients, give the quotient comparison
   first modulo IU and then modulo every power of the prime. Its inverse replaces
   each completed coefficient by any representative of the corresponding coordinate.
3. Pull back the quotient prime to obtain n. Its contraction is r. Apply
   lem-trf-adic-quotient-isomorphisms-localize to get the local quotient equivalences
   and the equality of extended maximal ideals (def-weil-pbc-localization-at-prime).
4. For a denominator outside n, lift its class modulo the prime power to U. Its
   lift lies outside r, so its image in the local quotient is a unit. The inverse
   on a fraction is therefore the inverse on its numerator times that unit inverse.
5. The local quotient equivalences commute with reductions, as do their inverses.
   Exponent one identifies the residue fields by def-weil-pbc-localization-at-prime.
6. On the compatible sequences of def-weil-pbc-adic-completion, apply these
   equivalences coordinatewise and their inverses coordinatewise. These are inverse
   ring maps and commute with U in every coordinate, hence on the inverse limits.
7. The local rings are Noetherian by lem-weil-pbc-localization-noetherian and the
   finite-type theorem. By lem-weil-pbc-adic-completion-mod-power, their projection
   kernels are the extended maximal-ideal powers. The coordinatewise equivalence
   carries these kernels onto one another, proving continuity in both directions.
(blueprint: lem-trf-adic-base-tensor-local-comparison). -/
theorem adicBaseTensorLocalComparison
    {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    {U : Type v} [CommRing U] [Algebra R U]
    (hU : RingHom.FiniteType (algebraMap R U))
    (r : Ideal U) [r.IsPrime] (hIr : I.map (algebraMap R U) ≤ r) :
    IsNoetherianRing (AdicBaseTensor I U) ∧
    ∃ q : (AdicBaseTensor I U ⧸
        I.map (algebraMap R (AdicBaseTensor I U))) ≃+*
        (U ⧸ I.map (algebraMap R U)),
      (∀ (h : AdicCompletion I R) (a : U) (b : R),
        AdicCompletion.evalOneₐ I h = Ideal.Quotient.mk I b →
        q (Ideal.Quotient.mk _ (TensorProduct.tmul R h a)) =
          Ideal.Quotient.mk _ (algebraMap R U b * a)) ∧
      ∃ n : PrimeSpectrum (AdicBaseTensor I U),
        n.asIdeal = Ideal.comap
          (q.toRingHom.comp (Ideal.Quotient.mk _))
          (r.map (Ideal.Quotient.mk (I.map (algebraMap R U)))) ∧
        ∃ hnr : r = n.asIdeal.comap (adicBaseTensorInclusion I U),
          ∃ f : Localization.AtPrime r →+* Localization.AtPrime n.asIdeal,
            f = Localization.localRingHom r n.asIdeal (adicBaseTensorInclusion I U) hnr ∧
            Ideal.map f (IsLocalRing.maximalIdeal (Localization.AtPrime r)) =
              IsLocalRing.maximalIdeal (Localization.AtPrime n.asIdeal) ∧
            ∃ e : ∀ j : ℕ,
              (Localization.AtPrime r ⧸
                (IsLocalRing.maximalIdeal (Localization.AtPrime r)) ^ (j + 1)) ≃+*
              (Localization.AtPrime n.asIdeal ⧸
                (IsLocalRing.maximalIdeal (Localization.AtPrime n.asIdeal)) ^ (j + 1)),
              (∀ (j : ℕ) (z : Localization.AtPrime r),
                e j (Ideal.Quotient.mk _ z) = Ideal.Quotient.mk _ (f z)) ∧
              (∀ (j : ℕ) (h : AdicCompletion I R) (a : U) (b : R),
                AdicCompletion.evalₐ I (j + 1) h = Ideal.Quotient.mk _ b →
                (e j).symm (Ideal.Quotient.mk _
                  (algebraMap (AdicBaseTensor I U) (Localization.AtPrime n.asIdeal)
                    (TensorProduct.tmul R h a))) =
                  Ideal.Quotient.mk _ (algebraMap U (Localization.AtPrime r)
                    (algebraMap R U b * a))) ∧
              (∀ (j : ℕ) (w : AdicBaseTensor I U) (t : n.asIdeal.primeCompl),
                (e j).symm (Ideal.Quotient.mk _
                  (IsLocalization.mk' (Localization.AtPrime n.asIdeal) w t)) =
                  (e j).symm (Ideal.Quotient.mk _
                    (algebraMap _ (Localization.AtPrime n.asIdeal) w)) *
                  Ring.inverse ((e j).symm (Ideal.Quotient.mk _
                    (algebraMap (AdicBaseTensor I U) (Localization.AtPrime n.asIdeal)
                      (t : AdicBaseTensor I U))))) ∧
              (∀ (j k : ℕ) (hjk : j ≤ k),
                (Ideal.Quotient.factor (R := Localization.AtPrime n.asIdeal)
                  (Ideal.pow_le_pow_right (Nat.add_le_add_right hjk 1))).comp
                    (e k).toRingHom =
                (e j).toRingHom.comp (Ideal.Quotient.factor (R := Localization.AtPrime r)
                  (Ideal.pow_le_pow_right (Nat.add_le_add_right hjk 1)))) ∧
              ∃ E : AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime r))
                  (Localization.AtPrime r) ≃+*
                AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime n.asIdeal))
                  (Localization.AtPrime n.asIdeal),
                (∀ (j : ℕ) (z : AdicCompletion
                    (IsLocalRing.maximalIdeal (Localization.AtPrime r)) (Localization.AtPrime r)),
                  AdicCompletion.evalₐ
                    (IsLocalRing.maximalIdeal (Localization.AtPrime n.asIdeal)) (j + 1) (E z) =
                  e j (AdicCompletion.evalₐ
                    (IsLocalRing.maximalIdeal (Localization.AtPrime r)) (j + 1) z)) ∧
                (∀ a : U,
                  E (algebraMap _ (AdicCompletion
                    (IsLocalRing.maximalIdeal (Localization.AtPrime r)) (Localization.AtPrime r))
                    (algebraMap U (Localization.AtPrime r) a)) =
                  algebraMap _ (AdicCompletion
                    (IsLocalRing.maximalIdeal (Localization.AtPrime n.asIdeal))
                    (Localization.AtPrime n.asIdeal))
                    (algebraMap _ (Localization.AtPrime n.asIdeal)
                      (adicBaseTensorInclusion I U a))) ∧
                @Continuous _ _
                  ((IsLocalRing.maximalIdeal (Localization.AtPrime r)).adicModuleTopology
                    (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime r))
                      (Localization.AtPrime r)))
                  ((IsLocalRing.maximalIdeal (Localization.AtPrime n.asIdeal)).adicModuleTopology
                    (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime n.asIdeal))
                      (Localization.AtPrime n.asIdeal))) E ∧
                @Continuous _ _
                  ((IsLocalRing.maximalIdeal (Localization.AtPrime n.asIdeal)).adicModuleTopology
                    (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime n.asIdeal))
                      (Localization.AtPrime n.asIdeal)))
                  ((IsLocalRing.maximalIdeal (Localization.AtPrime r)).adicModuleTopology
                    (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime r))
                      (Localization.AtPrime r))) E.symm := by
  sorry

end RingTheory
