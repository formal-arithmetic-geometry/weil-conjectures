/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.IsSepClosed
public import Submission.WeilConjectures.Mathlib.RingTheory.Etale.QuasiFinite
public import Submission.WeilConjectures.Mathlib.RingTheory.Henselian
public import Submission.WeilConjectures.Mathlib.RingTheory.Invariant.Profinite

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Normal local domains with separably closed fraction field are strictly henselian

Let `A` be an integrally closed local domain whose fraction field `Ω` is separably closed (for
instance the localization at a maximal ideal of the integral closure of a domain in a separable
closure of its fraction field). Then `A` is strictly henselian
(`IsStrictlyHenselianLocalRing.of_isFractionRing_of_isSepClosed`).

This is `HenselianLocalRing.of_isSepClosed_fractionRing` together with
`IsLocalRing.isSepClosed_residueField_of_isSepClosed_fractionRing`.
-/

@[expose] public section

open IsLocalRing

namespace IsStrictlyHenselianLocalRing

variable {A : Type*} [CommRing A] [IsLocalRing A] [IsIntegrallyClosed A]

/-- An integrally closed local domain whose fraction field is separably closed is strictly
henselian. -/
theorem of_isFractionRing_of_isSepClosed (Ω : Type*) [Field Ω] [IsSepClosed Ω] [Algebra A Ω]
    [IsFractionRing A Ω] : IsStrictlyHenselianLocalRing A :=
  have := HenselianLocalRing.of_isSepClosed_fractionRing (A := A) Ω
  ⟨IsLocalRing.isSepClosed_residueField_of_isSepClosed_fractionRing Ω⟩

end IsStrictlyHenselianLocalRing

namespace Ideal

variable {R Ω : Type*} [CommRing R] [Field Ω] [Algebra R Ω]
  (Q : Ideal (integralClosure R Ω)) [Q.IsPrime]

/-- The localization at a prime `Q` of the integral closure of `R` in a field `Ω` maps to `Ω`. -/
noncomputable def atPrimeToField : Localization.AtPrime Q →+* Ω :=
  IsLocalization.lift (M := Q.primeCompl) (g := (integralClosure R Ω).val.toRingHom) fun s ↦
    IsUnit.mk0 _ fun h ↦ s.2 (by
      have : s.1 = 0 := Subtype.ext h
      rw [this]
      exact Q.zero_mem)

@[simp]
lemma atPrimeToField_algebraMap (b : integralClosure R Ω) :
    atPrimeToField Q (algebraMap _ (Localization.AtPrime Q) b) = b :=
  IsLocalization.lift_eq _ _


section StrictlyHenselian

variable [IsSepClosed Ω] [Algebra.IsAlgebraic R Ω]


end StrictlyHenselian

section Action

open scoped Pointwise

variable {G : Type*} [Group G] [MulSemiringAction G Ω] [SMulCommClass G R Ω]

omit [Q.IsPrime] in
lemma comap_toRingHom_eq_of_mem_stabilizer {g : G} (hg : g ∈ MulAction.stabilizer G Q) :
    Q = Q.comap (MulSemiringAction.toRingHom G (integralClosure R Ω) g) := by
  ext x
  rw [Ideal.mem_comap, MulSemiringAction.toRingHom_apply]
  conv_rhs => rw [← (MulAction.mem_stabilizer_iff.1 hg : g • Q = Q)]
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, inv_smul_smul]

/-- The automorphism of `B_Q` induced by an element `g` of the stabiliser of `Q`. -/
noncomputable def atPrimeMap (g : G) (hg : g ∈ MulAction.stabilizer G Q) :
    Localization.AtPrime Q →+* Localization.AtPrime Q :=
  Localization.localRingHom Q Q (MulSemiringAction.toRingHom G (integralClosure R Ω) g)
    (comap_toRingHom_eq_of_mem_stabilizer Q hg)

instance (g : G) (hg : g ∈ MulAction.stabilizer G Q) : IsLocalHom (atPrimeMap Q g hg) :=
  Localization.isLocalHom_localRingHom _ _ _ _


end Action

section Galois

open scoped Pointwise

variable {K : Type*} [Field K] [Algebra R K] [Algebra K Ω] [IsScalarTower R K Ω] [IsGalois K Ω]
  [IsIntegrallyClosedIn R K] (P : Ideal R) [Q.IsMaximal] [Q.LiesOver P]


end Galois

end Ideal
