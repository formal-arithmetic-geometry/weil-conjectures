/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# N-1, N-2 (Japanese) and Nagata rings

Following [Stacks, Tag 032E] and [Stacks, Tag 032R], for a domain `R` with fraction field `K`:

* `R` is *N-1* (`Ring.IsN1`) if the integral closure of `R` in `K` is a finite `R`-module;
* `R` is *N-2* or *Japanese* (`Ring.IsJapanese`) if for every finite extension `L / K` the
  integral closure of `R` in `L` is a finite `R`-module.

A ring `R` is *Nagata* (`IsNagataRing`) if it is Noetherian and `R / 𝔭` is N-2 for every prime
`𝔭` of `R` ([Stacks, Tag 032R]). In particular the normalization of every `R / 𝔭` is finite
(`IsNagataRing.finite_integralClosure_quotient`); this is the only consequence of excellence used
in the blueprint (excellent rings are Nagata, [Stacks, Tag 07QV]).

Fields are Nagata (`IsNagataRing.of_field`).
-/

@[expose] public section

universe u

namespace Ring

variable (R : Type u) [CommRing R] [IsDomain R]

/-- A domain `R` is *N-1* if the integral closure of `R` in its fraction field is a finite
`R`-module ([Stacks, Tag 032E]). -/
def IsN1 : Prop :=
  Module.Finite R (integralClosure R (FractionRing R))

/-- A domain `R` is *N-2*, or *Japanese*, if for every finite extension `L` of its fraction field
the integral closure of `R` in `L` is a finite `R`-module ([Stacks, Tag 032E]). -/
def IsJapanese : Prop :=
  ∀ (L : Type u) [Field L] [Algebra (FractionRing R) L] [Algebra R L]
    [IsScalarTower R (FractionRing R) L] [FiniteDimensional (FractionRing R) L],
    Module.Finite R (integralClosure R L)

variable {R}

/-- A Japanese domain is N-1 ([Stacks, Tag 032E]). -/
lemma IsJapanese.isN1 (h : IsJapanese R) : IsN1 R :=
  h (FractionRing R)

/-- A domain which is a field is Japanese: every finite extension of its fraction field is a
finite module, and the integral closure is a submodule of it. -/
lemma isJapanese_of_isField (h : IsField R) : IsJapanese R := by
  intro L _ _ _ _ _
  have hbij : Function.Bijective (algebraMap R (FractionRing R)) := by
    refine ⟨IsFractionRing.injective R (FractionRing R), fun x ↦ ?_⟩
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) x
    obtain ⟨c, hc⟩ := h.mul_inv_cancel (nonZeroDivisors.ne_zero hb)
    refine ⟨a * c, ?_⟩
    have hb' : algebraMap R (FractionRing R) b ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    rw [eq_div_iff hb', map_mul, mul_assoc, ← map_mul, mul_comm c, hc, map_one, mul_one]
  let e : R ≃ₐ[R] FractionRing R := AlgEquiv.ofBijective (Algebra.ofId _ _) hbij
  have : Module.Finite R (FractionRing R) := Module.Finite.equiv e.toLinearEquiv
  have : Module.Finite R L := Module.Finite.trans (FractionRing R) L
  have : IsNoetherianRing R := by
    let := h.toField
    infer_instance
  exact Module.Finite.of_injective (Subalgebra.val (integralClosure R L)).toLinearMap
    Subtype.val_injective

end Ring

/-- A ring `R` is *Nagata* if it is Noetherian and `R / 𝔭` is N-2 (Japanese) for every prime
ideal `𝔭` of `R` ([Stacks, Tag 032R]). -/
class IsNagataRing (R : Type u) [CommRing R] : Prop extends IsNoetherianRing R where
  isJapanese_quotient (p : Ideal R) [p.IsPrime] : Ring.IsJapanese (R ⧸ p)

namespace IsNagataRing

variable {R : Type u} [CommRing R] [IsNagataRing R]

/-- In a Nagata ring `R`, the normalization of `R / 𝔭` (its integral closure in its fraction
field) is a finite `R / 𝔭`-module for every prime `𝔭` ([Stacks, Tag 032R]). -/
theorem finite_integralClosure_quotient (p : Ideal R) [p.IsPrime] :
    Module.Finite (R ⧸ p) (integralClosure (R ⧸ p) (FractionRing (R ⧸ p))) :=
  (isJapanese_quotient p).isN1

/-- A field is a Nagata ring. -/
instance of_field (K : Type u) [Field K] : IsNagataRing K where
  isJapanese_quotient p _ := by
    refine Ring.isJapanese_of_isField ?_
    have hp : p = ⊥ := (Ideal.eq_bot_or_top p).resolve_right (Ideal.IsPrime.ne_top ‹_›)
    subst hp
    exact (RingEquiv.quotientBot K).toMulEquiv.isField (Field.toIsField K)

end IsNagataRing
