/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q125
-/
module

public import Sheaf.RingTheory.ExcellentRing
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.RingHom.Finite
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.FieldTheory.Perfect
import Sheaf.RingTheory.CommonFiniteTraitExtension

/-!
# Simultaneous Epp base change for finitely many traits

Source: Illusie–Laszlo–Orgogozo, Travaux de Gabber, Exposé IV, Theorem 3.1.2,
Remark 3.1.3 and §4.2.3 (blueprint: lem-per-epp-finite-family-traits).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open scoped TensorProduct
open IsLocalRing

namespace IsDiscreteValuationRing

/-- The canonical map from the integral tensor product to the fraction-field tensor
product. The two equalities express compatibility of the fraction-field embeddings.
Source: ILO, Exposé IV, 3.1.2–3.1.3
(blueprint: lem-per-epp-finite-family-traits). -/
def eppTraitTensorMap
    (R : Type u) (S : Type v) (W K₀ : Type u) (F : Type v) (K : Type u)
    [CommRing R] [CommRing S] [CommRing W] [CommRing K₀] [CommRing F] [CommRing K]
    [Algebra R S] [Algebra R W] [Algebra R K₀]
    [Algebra S F] [Algebra K₀ F] [Algebra W K] [Algebra K₀ K]
    (hF : (algebraMap S F).comp (algebraMap R S) =
      (algebraMap K₀ F).comp (algebraMap R K₀))
    (hK : (algebraMap W K).comp (algebraMap R W) =
      (algebraMap K₀ K).comp (algebraMap R K₀)) :
    S ⊗[R] W →+* F ⊗[K₀] K :=
  Algebra.TensorProduct.mapRingHom (algebraMap R K₀) (algebraMap S F) (algebraMap W K)
    hF hK

/-- The special fibre of the integral closure in the quotient by `m` of the image
of the integral tensor product. Integral closure over the tensor product means
integral closure over its image: the same monic equations define both. The image
of `1 ⊗ π` belongs canonically to this closure via its algebra structure.
Source: ILO, Exposé IV, 3.1.2–3.1.3 and §4.2.3
(blueprint: lem-per-epp-finite-family-traits). -/
noncomputable abbrev eppNormalizedFactorSpecialFibre
    (R : Type u) (S : Type v) (W K₀ : Type u) (F : Type v) (K : Type u)
    [CommRing R] [CommRing S] [CommRing W] [CommRing K₀] [CommRing F] [CommRing K]
    [Algebra R S] [Algebra R W] [Algebra R K₀]
    [Algebra S F] [Algebra K₀ F] [Algebra W K] [Algebra K₀ K]
    (hF : (algebraMap S F).comp (algebraMap R S) =
      (algebraMap K₀ F).comp (algebraMap R K₀))
    (hK : (algebraMap W K).comp (algebraMap R W) =
      (algebraMap K₀ K).comp (algebraMap R K₀))
    (m : Ideal (F ⊗[K₀] K)) (π : W) : Type (max u v) :=
  let E := (F ⊗[K₀] K) ⧸ m
  let g := (Ideal.Quotient.mk m).comp (eppTraitTensorMap R S W K₀ F K hF hK)
  letI : Algebra (S ⊗[R] W) E := g.toAlgebra
  let B := integralClosure (S ⊗[R] W) E
  B ⧸ Ideal.span {algebraMap (S ⊗[R] W) B (1 ⊗ₜ[R] π)}

/-- Simultaneous Epp base change, including the empty family and noncomplete upper
traits. Fraction fields are given with their embeddings, and `hF` requires that
these embeddings extend the specified base maps. Field factors are the quotients
by maximal ideals. The finite-product assertion is included explicitly.

Source: ILO, Travaux de Gabber, Exposé IV, Theorem 3.1.2, Remark 3.1.3 and §4.2.3.
(blueprint: lem-per-epp-finite-family-traits).

Proof:
1. Apply lem-per-epp-single-trait-base-change, clause (1), to each excellent
   trait Tᵢ, using the given perfect-core algebraicity hypothesis, to obtain a
   finite complete DVR extension Wᵢ of W₀ good for Tᵢ.
2. Apply lem-per-epp-common-finite-trait-extension to this finite family to
   obtain one finite complete DVR extension W receiving all Wᵢ. Its residue
   extension is finite, hence perfect. Put K = Frac(W).
3. If the family is empty, take W = W₀ and K = K₀. Otherwise clause (3) of
   lem-per-epp-single-trait-base-change makes W good for every Tᵢ, by stability
   under further finite base change. The generic tensor products are finite
   products of fields (finite separable base extension in characteristic zero).
   Unwind goodness for every maximal-ideal field factor and every uniformizer
   π: its normalized special fibre B/πB is reduced. -/
theorem exists_epp_finite_family_traits
    (p : ℕ) (hp : p.Prime)
    (W₀ K₀ : Type u) [CommRing W₀] [IsDomain W₀] [IsDiscreteValuationRing W₀]
    [IsAdicComplete (maximalIdeal W₀) W₀]
    [Field K₀] [Algebra W₀ K₀] [IsFractionRing W₀ K₀] [CharZero K₀]
    [CharP (ResidueField W₀) p] [PerfectField (ResidueField W₀)]
    (I : Type w) [Finite I] (T F : I → Type v)
    [∀ i : I, CommRing (T i)] [∀ i : I, IsDomain (T i)]
    [∀ i : I, IsDiscreteValuationRing (T i)]
    [∀ i : I, Algebra W₀ (T i)] [∀ i : I, IsLocalHom (algebraMap W₀ (T i))]
    (hinj : ∀ i : I, Function.Injective (algebraMap W₀ (T i)))
    (hexc : ∀ i : I, IsExcellent (T i))
    [∀ i : I, Field (F i)] [∀ i : I, Algebra (T i) (F i)]
    [∀ i : I, IsFractionRing (T i) (F i)] [∀ i : I, Algebra K₀ (F i)]
    (hF : ∀ i : I, (algebraMap (T i) (F i)).comp (algebraMap W₀ (T i)) =
      (algebraMap K₀ (F i)).comp (algebraMap W₀ K₀))
    (hcore : ∀ (i : I) (x : ResidueField (T i)),
      (∀ n : ℕ, ∃ y : ResidueField (T i), y ^ (p ^ n) = x) →
      @IsAlgebraic (ResidueField W₀) (ResidueField (T i)) _ _
        (ResidueField.map (algebraMap W₀ (T i))).toAlgebra x) :
    ∃ (W : Type u) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W)
      (_ : IsAdicComplete (maximalIdeal W) W) (_ : Algebra W₀ W)
      (_ : IsLocalHom (algebraMap W₀ W)),
      Function.Injective (algebraMap W₀ W) ∧ Module.Finite W₀ W ∧
      (ResidueField.map (algebraMap W₀ W)).Finite ∧
      CharP (ResidueField W) p ∧ PerfectField (ResidueField W) ∧
      ∃ (K : Type u) (_ : Field K) (_ : Algebra W K) (_ : IsFractionRing W K)
        (_ : Algebra K₀ K) (_ : CharZero K)
        (hK : (algebraMap W K).comp (algebraMap W₀ W) =
          (algebraMap K₀ K).comp (algebraMap W₀ K₀)),
        ∀ i : I,
          (∃ (n : ℕ) (E : Fin n → Type (max u v)) (_ : ∀ j : Fin n, Field (E j)),
            Nonempty ((F i ⊗[K₀] K) ≃+* (∀ j : Fin n, E j))) ∧
          ∀ (π : W), maximalIdeal W = Ideal.span {π} →
            ∀ (m : Ideal (F i ⊗[K₀] K)) (_ : m.IsMaximal),
              IsReduced (eppNormalizedFactorSpecialFibre W₀ (T i) W K₀ (F i) K
                (hF i) hK m π) := by
  sorry

end IsDiscreteValuationRing
