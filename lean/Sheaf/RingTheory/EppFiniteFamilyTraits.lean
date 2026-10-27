/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NN
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Sheaf.RingTheory.ExcellentRing

import Sheaf.RingTheory.CommonFiniteTraitExtension

/-!
# Simultaneous Epp base change for finitely many traits

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose IV, Theorem 3.1.2,
Remark 3.1.3 and §4.2.3 (blueprint: lem-per-epp-finite-family-traits).

## Main declarations

* `IsDiscreteValuationRing.eppTraitTensorMap`: the canonical map to the generic tensor product.
* `IsDiscreteValuationRing.eppNormalizedFactorSpecialFibre`: the normalized special fibre.
* `IsDiscreteValuationRing.exists_epp_finite_family_traits`: simultaneous finite base change.
-/

@[expose] public section

set_option autoImplicit false

universe u v w x t

open scoped TensorProduct

namespace IsDiscreteValuationRing

/-- The map from the tensor product of the two trait rings to that of their fraction fields.
It sends `a ⊗ b` to the tensor of their fraction-field images. Source: ILO, Expose IV,
Theorem 3.1.2 and Remark 3.1.3 (blueprint: lem-per-epp-finite-family-traits). -/
def eppTraitTensorMap
    (W0 : Type u) (K0 : Type v) (T : Type w) (F : Type x) (W K : Type u)
    [CommRing W0] [Field K0] [CommRing T] [Field F] [CommRing W] [Field K]
    [Algebra W0 K0] [Algebra W0 T] [Algebra T F] [Algebra K0 F]
    [Algebra W0 W] [Algebra W K] [Algebra K0 K]
    (hF : (algebraMap T F).comp (algebraMap W0 T) =
      (algebraMap K0 F).comp (algebraMap W0 K0))
    (hK : (algebraMap W K).comp (algebraMap W0 W) =
      (algebraMap K0 K).comp (algebraMap W0 K0)) :
    T ⊗[W0] W →+* F ⊗[K0] K :=
  Algebra.TensorProduct.mapRingHom (algebraMap W0 K0)
    (algebraMap T F) (algebraMap W K) hF hK

/-- For a specified map `f : A → E`, take the integral closure of its image in `E`, then
quotient by the image of `a`. Integrality over `A` equals integrality over its image by
lifting polynomial coefficients. For `A = T ⊗ W` and `a = 1 ⊗ π`, this is `B/πB`.
Source: ILO, Expose IV, Theorem 3.1.2, Remark 3.1.3 and §4.2.3
(blueprint: lem-per-epp-finite-family-traits). -/
noncomputable abbrev eppNormalizedFactorSpecialFibre
    {A : Type w} {E : Type x} [CommRing A] [CommRing E] (f : A →+* E) (a : A) :=
  letI := f.toAlgebra
  (integralClosure A E) ⧸ Ideal.span {algebraMap A (integralClosure A E) a}

/-- A finite family of excellent traits over a complete mixed-characteristic trait with
perfect residue field admits one finite base extension making all normalized special
fibres reduced. The upper traits need not be complete; the family may be empty.

Source: ILO, Expose IV, Theorem 3.1.2, Remark 3.1.3 and §4.2.3, the sentence beginning
"De tels ideaux p etant en nombre fini" (blueprint: lem-per-epp-finite-family-traits).

Proof:
1. Apply lem-per-epp-single-trait-base-change, clause (1), to each T_i, using the
   perfect-core algebraicity assumption, to obtain a good finite complete extension W_i.
2. Apply lem-per-epp-common-finite-trait-extension to the finite family W_i to obtain
   a common finite complete extension W. Its residue field is finite over the perfect
   base residue field, hence perfect. Choose a uniformizer of W.
3. For the empty family take W = W0. Otherwise apply clause (3), stability under further
   finite base change, of lem-per-epp-single-trait-base-change along each local W_i → W.
   Unwinding goodness gives reducedness of B/πB for every maximal-ideal field factor
   and every uniformizer. In characteristic zero the generic tensor is a finite product
   of fields, as in Remark 3.1.3. -/
theorem exists_epp_finite_family_traits
    (p : ℕ) (hp : p.Prime)
    (W0 : Type u) [CommRing W0] [IsDomain W0] [IsDiscreteValuationRing W0]
    [IsAdicComplete (IsLocalRing.maximalIdeal W0) W0]
    (K0 : Type v) [Field K0] [Algebra W0 K0] [IsFractionRing W0 K0] [CharZero K0]
    [CharP (IsLocalRing.ResidueField W0) p] [PerfectField (IsLocalRing.ResidueField W0)]
    (I : Type t) [Finite I] (T : I → Type w) (F : I → Type x)
    [∀ i : I, CommRing (T i)] [∀ i : I, IsDomain (T i)]
    [∀ i : I, IsDiscreteValuationRing (T i)]
    [∀ i : I, Algebra W0 (T i)] [∀ i : I, IsLocalHom (algebraMap W0 (T i))]
    (hinj : ∀ i : I, Function.Injective (algebraMap W0 (T i)))
    (hexc : ∀ i : I, IsExcellent (T i))
    [∀ i : I, Field (F i)] [∀ i : I, Algebra (T i) (F i)]
    [∀ i : I, IsFractionRing (T i) (F i)] [∀ i : I, Algebra K0 (F i)]
    (hF : ∀ i : I, (algebraMap (T i) (F i)).comp (algebraMap W0 (T i)) =
      (algebraMap K0 (F i)).comp (algebraMap W0 K0))
    (hcore : ∀ (i : I) (a : IsLocalRing.ResidueField (T i)),
      (∀ n : ℕ, ∃ b : IsLocalRing.ResidueField (T i), b ^ (p ^ n) = a) →
      @IsAlgebraic (IsLocalRing.ResidueField W0) (IsLocalRing.ResidueField (T i))
        _ _ (IsLocalRing.ResidueField.map (algebraMap W0 (T i))).toAlgebra a) :
    ∃ (W : Type u) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W)
      (_ : Algebra W0 W) (_ : IsLocalHom (algebraMap W0 W)),
      IsAdicComplete (IsLocalRing.maximalIdeal W) W ∧
      Function.Injective (algebraMap W0 W) ∧ Module.Finite W0 W ∧
      RingHom.Finite (IsLocalRing.ResidueField.map (algebraMap W0 W)) ∧
      CharP (IsLocalRing.ResidueField W) p ∧ PerfectField (IsLocalRing.ResidueField W) ∧
      ∃ (K : Type u) (_ : Field K) (_ : Algebra W K) (_ : IsFractionRing W K)
        (_ : CharZero K) (_ : Algebra K0 K),
        ∃ hK : (algebraMap W K).comp (algebraMap W0 W) =
          (algebraMap K0 K).comp (algebraMap W0 K0),
          (∀ i : I, ∃ (n : ℕ) (E : Fin n → Type (max x u))
            (_ : ∀ j : Fin n, Field (E j)),
            Nonempty ((F i ⊗[K0] K) ≃+* (∀ j : Fin n, E j))) ∧
          ∀ (π : W), IsLocalRing.maximalIdeal W = Ideal.span {π} →
            ∀ (i : I) (m : Ideal (F i ⊗[K0] K)), m.IsMaximal →
              IsReduced (eppNormalizedFactorSpecialFibre
                ((Ideal.Quotient.mk m).comp
                  (eppTraitTensorMap W0 K0 (T i) (F i) W K (hF i) hK))
                ((1 : T i) ⊗ₜ[W0] π)) := by
  sorry

end IsDiscreteValuationRing
