/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q08
-/
module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import WeilConjectures.RingTheory.FiniteModuleComplete
import WeilConjectures.RingTheory.FiniteOverCompleteRing
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.KrullDimension.Zero
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Finite completed differentials and the completed conormal sequence

Source: EGA IV, première partie, 0_IV 20.7.14, 20.7.15, 20.7.20 and 21.9.1
(blueprint: lem-per-completed-differential-finite-conormal).

The completed module is Mathlib's `AdicCompletion` applied to ordinary differentials.
The induced differential is `AdicCompletion.of` composed with `KaehlerDifferential.D`.
Maps in the conormal sequence and the generic comparison are specified on these generators.
Tensor factors are written with the coefficient algebra first, using the canonical symmetry
of tensor products to express the sequence and comparison from the source.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open scoped TensorProduct
open IsLocalRing

namespace KaehlerDifferential

/-- Completed differentials over a subfield with finite residue extension are finite, generated
by exact differentials, and represent derivations to finite complete modules. Quotients have
an exact completed conormal sequence, and the comparison at a reduced minimal prime is an
isomorphism. All arrows are specified by their values on the displayed generators; thus the
existentially supplied arrows are the canonical arrows, rather than arbitrary maps.

Source: EGA IV-1, 0_IV 20.7.14, 20.7.15, 20.7.20 and 21.9.1
(blueprint: lem-per-completed-differential-finite-conormal).

Proof:
1. Choose generators of the maximal ideal and lift an F-basis of the residue field. The
ordinary Jacobi--Zariski conormal sequence shows that their differentials generate the
reduction of the ordinary differential module modulo the maximal ideal
[lem-weil-pbc-jacobi-zariski-differential-maps].
2. Completion preserves these reductions and is complete and separated
[lem-weil-pbc-module-completion-complete]. Apply the lifting-of-generators theorem
[lem-weil-pbc-finite-over-complete-ring] to obtain finite generation by these exact
 differential lifts, without assuming ordinary differentials are finite.
3. An F-derivation to N corresponds to an A-linear map from ordinary differentials. Its
reductions modulo every power give compatible maps, hence a map of completions. Completeness
of N gives the required extension. Generation by exact differentials gives uniqueness.
This includes every derivation, without an additional continuity assumption.
4. Every proper quotient C is finite over A and complete
[lem-weil-pbc-finite-module-complete-over-complete-noetherian]. It is Noetherian local with
the same residue field; the subfield injects into C. Apply the preceding arguments to C.
5. Identify C tensor M with M/IM. Leibniz shows that a mod I squared maps well-definedly to
1 tensor da. Its image H has finite quotient Q, which is complete by the finite-module
completion theorem. The induced derivation C to Q extends uniquely from completed
C-differentials. Conversely the derivation A to completed C-differentials extends uniquely
from M and factors through Q. The two maps are inverse on exact differential generators.
Thus the map onto completed C-differentials is surjective with kernel H.
6. At a reduced minimal prime q the localization is a field and q localizes to zero
[lem-weil-pbc-minimal-prime-reduced-localization-field]. It identifies canonically with
Frac(A/q). Hence the conormal term vanishes after tensoring with this field. Tensor right
exactness [lem-weil-pbc-tensor-right-exact] gives the last isomorphism, with the stated
formula on exact differentials. -/
theorem completed_finite_conormal
    (F : Type u) (A : Type v) [Field F] [CommRing A] [Algebra F A]
    [IsLocalRing A] [IsNoetherianRing A] [IsAdicComplete (maximalIdeal A) A]
    [Module.Finite F (ResidueField A)] :
    Module.Finite A (AdicCompletion (maximalIdeal A) (KaehlerDifferential F A)) ∧
    Submodule.span A (Set.range (fun a : A ↦
      AdicCompletion.of (maximalIdeal A) (KaehlerDifferential F A) (D F A a))) = ⊤ ∧
    (∀ (N : Type (max v w)) [AddCommGroup N] [Module A N] [Module F N]
      [IsScalarTower F A N] [Module.Finite A N] [IsAdicComplete (maximalIdeal A) N],
      Function.Bijective (fun h :
        AdicCompletion (maximalIdeal A) (KaehlerDifferential F A) →ₗ[A] N ↦
        h.compDer ((AdicCompletion.of (maximalIdeal A)
          (KaehlerDifferential F A)).compDer (D F A)))) ∧
    (∀ (I : Ideal A), I ≠ ⊤ →
      IsAdicComplete ((maximalIdeal A).map (Ideal.Quotient.mk I)) (A ⧸ I) ∧
      ∃ δ : I.Cotangent →ₗ[A ⧸ I]
          (A ⧸ I) ⊗[A] AdicCompletion (maximalIdeal A) (KaehlerDifferential F A),
      ∃ π : ((A ⧸ I) ⊗[A]
          AdicCompletion (maximalIdeal A) (KaehlerDifferential F A)) →ₗ[A ⧸ I]
          AdicCompletion ((maximalIdeal A).map (Ideal.Quotient.mk I))
            (KaehlerDifferential F (A ⧸ I)),
        (∀ a : I, δ (I.toCotangent a) = (1 : A ⧸ I) ⊗ₜ[A]
          AdicCompletion.of (maximalIdeal A) (KaehlerDifferential F A) (D F A a)) ∧
        (∀ (c : A ⧸ I) (a : A), π (c ⊗ₜ[A]
          AdicCompletion.of (maximalIdeal A) (KaehlerDifferential F A) (D F A a)) =
          c • AdicCompletion.of ((maximalIdeal A).map (Ideal.Quotient.mk I))
            (KaehlerDifferential F (A ⧸ I)) (D F (A ⧸ I) (Ideal.Quotient.mk I a))) ∧
        Function.Exact δ π ∧ Function.Surjective π) ∧
    (IsReduced A → ∀ (q : Ideal A), q ∈ minimalPrimes A →
      ∀ (L : Type (max v w)) [Field L] [Algebra (A ⧸ q) L] [IsFractionRing (A ⧸ q) L]
        [Algebra A L] [IsScalarTower A (A ⧸ q) L],
        ∃ e : (L ⊗[A] AdicCompletion (maximalIdeal A) (KaehlerDifferential F A)) ≃ₗ[L]
            L ⊗[A ⧸ q] AdicCompletion ((maximalIdeal A).map (Ideal.Quotient.mk q))
              (KaehlerDifferential F (A ⧸ q)),
          ∀ (l : L) (a : A),
            e (l ⊗ₜ[A] AdicCompletion.of (maximalIdeal A)
              (KaehlerDifferential F A) (D F A a)) =
            l ⊗ₜ[A ⧸ q] AdicCompletion.of ((maximalIdeal A).map (Ideal.Quotient.mk q))
              (KaehlerDifferential F (A ⧸ q)) (D F (A ⧸ q) (Ideal.Quotient.mk q a))) := by
  sorry

end KaehlerDifferential
