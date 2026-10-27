/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# Normality descent through a module-split principal quotient

Source: the agent-formulated local-algebra lemma attached to Stacks Tag 0309
(`definition-domain-normal`), adapting the fractional-ideal argument of Tag 033G
(`lemma-descent-normal`) to a linear retraction
(blueprint: lem-trf-split-principal-quotient-normality).

## Main statements

* `RingHom.split_principal_quotient_normality`: contraction of a principal ideal,
  its quotient injection and additive linear retraction, and descent of normality.
-/

@[expose] public section

universe u v

namespace RingHom

private theorem normality_of_linear_retraction
    {R : Type u} {A : Type v} [CommRing R] [CommRing A]
    (ι : R →+* A) (hι : Function.Injective ι) (ρ : A →+ R)
    (hlinear : ∀ (r : R) (a : A), ρ (ι r * a) = r * ρ a)
    (hretract : ∀ r : R, ρ (ι r) = r)
    (hA : IsDomain A ∧ IsIntegrallyClosed A) : IsDomain R ∧ IsIntegrallyClosed R := by
  have : IsDomain A := hA.1
  have : IsIntegrallyClosed A := hA.2
  have : IsDomain R := Function.Injective.isDomain ι hι
  refine ⟨inferInstance, (isIntegrallyClosed_iff (FractionRing R)).mpr ?_⟩
  intro x hx
  let g : R →+* FractionRing A := (algebraMap A (FractionRing A)).comp ι
  have hg : Function.Injective g := (IsFractionRing.injective A (FractionRing A)).comp hι
  let f : FractionRing R →+* FractionRing A := IsFractionRing.lift hg
  have hf (r : R) : f (algebraMap R (FractionRing R) r) =
      algebraMap A (FractionRing A) (ι r) := IsFractionRing.lift_algebraMap hg r
  have hxA : _root_.IsIntegral A (f x) := _root_.IsIntegral.map_of_comp_eq ι f
    (by ext r; exact (hf r).symm) hx
  obtain ⟨c, hc⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hxA
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective R x
  have hbR : algebraMap R (FractionRing R) b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).mpr
      (mem_nonZeroDivisors_iff_ne_zero.mp hb)
  have hmul : algebraMap R (FractionRing R) a =
      algebraMap R (FractionRing R) b * x := by
    rw [← hab, mul_div_cancel₀ _ hbR]
  have hmulA : ι a = ι b * c := by
    apply IsFractionRing.injective A (FractionRing A)
    rw [map_mul, hc]
    simpa only [map_mul, hf] using congrArg f hmul
  have hmulR : a = b * ρ c := by
    simpa only [hretract, hlinear] using congrArg ρ hmulA
  refine ⟨ρ c, ?_⟩
  apply mul_left_cancel₀ hbR
  calc
    algebraMap R (FractionRing R) b * algebraMap R (FractionRing R) (ρ c) =
        algebraMap R (FractionRing R) a := by rw [← map_mul, ← hmulR]
    _ = algebraMap R (FractionRing R) b * x := hmul

/-- A module-split ring inclusion contracts principal ideals, induces a split quotient
inclusion, and descends normal domains. The quotient maps are specified on every
representative, so these are the induced maps, not arbitrary maps with a splitting.

Source: the agent-formulated lemma using Stacks Tag 0309 (`definition-domain-normal`),
adapting the fractional-ideal argument in Tag 033G (`lemma-descent-normal`)
(blueprint: lem-trf-split-principal-quotient-normality).

Proof:
1. If `ι r = ι θ * a`, applying `ρ` gives `r = θ * ρ a`. The reverse inclusion
   follows by applying `ι` to a multiple of `θ`. This proves ideal contraction.
2. Define `j [r] = [ι r]` and `p [a] = [ρ a]`. The contraction proves that `j` is
   injective. Linearity of `ρ` takes multiples of `ι θ` to multiples of `θ`, so `p`
   is well defined and additive. The same linearity gives `p (j b * c) = b * p c`,
   and the retraction identity gives `p (j b) = b`.
3. If the larger quotient `C` is a normal domain, the unital injection makes the
   smaller quotient `B` a nonzero domain. By `lem-weil-pbc-fraction-field-lift`,
   extend `B → C → FractionRing C` to an embedding of `FractionRing B`.
4. For a fraction `a / b` integral over `B`, apply this embedding to its monic
   equation. Normality of `C` gives an element `c : C` representing that fraction,
   hence `j a = j b * c` in `C`.
5. Applying `p` gives `a = b * p c`, so the fraction belongs to `B`. This proves
   that `B` is integrally closed, using `def-weil-pbc-normal-ring`. Apply the same fractional
   argument directly to the original inclusion and retraction to obtain the
   final normal-domain descent assertion. -/
theorem split_principal_quotient_normality
    {R : Type u} {A : Type v} [CommRing R] [CommRing A]
    (ι : R →+* A) (hι : Function.Injective ι) (ρ : A →+ R)
    (hlinear : ∀ (r : R) (a : A), ρ (ι r * a) = r * ρ a)
    (hretract : ∀ r : R, ρ (ι r) = r) (θ : R) :
    Ideal.comap ι (Ideal.span ({ι θ} : Set A)) = Ideal.span ({θ} : Set R) ∧
      (∃ (j : (R ⧸ Ideal.span ({θ} : Set R)) →+*
          (A ⧸ Ideal.span ({ι θ} : Set A)))
        (p : (A ⧸ Ideal.span ({ι θ} : Set A)) →+
          (R ⧸ Ideal.span ({θ} : Set R))),
        (∀ r : R, j (Ideal.Quotient.mk _ r) = Ideal.Quotient.mk _ (ι r)) ∧
        Function.Injective j ∧
        (∀ a : A, p (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ (ρ a)) ∧
        Function.LeftInverse p j ∧
        (∀ (b : R ⧸ Ideal.span ({θ} : Set R))
          (c : A ⧸ Ideal.span ({ι θ} : Set A)), p (j b * c) = b * p c)) ∧
      ((IsDomain (A ⧸ Ideal.span ({ι θ} : Set A)) ∧
          IsIntegrallyClosed (A ⧸ Ideal.span ({ι θ} : Set A))) →
        IsDomain (R ⧸ Ideal.span ({θ} : Set R)) ∧
          IsIntegrallyClosed (R ⧸ Ideal.span ({θ} : Set R))) ∧
      ((IsDomain A ∧ IsIntegrallyClosed A) → IsDomain R ∧ IsIntegrallyClosed R) := by
  have hcontract : Ideal.comap ι (Ideal.span ({ι θ} : Set A)) =
      Ideal.span ({θ} : Set R) := by
    ext r
    change ι r ∈ Ideal.span ({ι θ} : Set A) ↔ r ∈ Ideal.span ({θ} : Set R)
    simp only [Ideal.mem_span_singleton]
    constructor
    · rintro ⟨a, ha⟩
      exact ⟨ρ a, by simpa only [hretract, hlinear] using congrArg ρ ha⟩
    · rintro ⟨a, rfl⟩
      exact ⟨ι a, map_mul ι θ a⟩
  let I : Ideal R := Ideal.span ({θ} : Set R)
  let J : Ideal A := Ideal.span ({ι θ} : Set A)
  let j : (R ⧸ I) →+* (A ⧸ J) := Ideal.quotientMap J ι hcontract.ge
  have hj (r : R) : j (Ideal.Quotient.mk I r) = Ideal.Quotient.mk J (ι r) := rfl
  have hjinj : Function.Injective j := Ideal.quotientMap_injective' hcontract.le
  let q : A →+ R ⧸ I := (Ideal.Quotient.mk I).toAddMonoidHom.comp ρ
  have hq : J.toAddSubgroup ≤ q.ker := by
    intro a ha
    change Ideal.Quotient.mk I (ρ a) = 0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton.mp ha
    exact Ideal.mem_span_singleton.mpr ⟨ρ b, hlinear θ b⟩
  let p : (A ⧸ J) →+ (R ⧸ I) := QuotientAddGroup.lift J.toAddSubgroup q hq
  have hp (a : A) : p (Ideal.Quotient.mk J a) = Ideal.Quotient.mk I (ρ a) := rfl
  have hret : Function.LeftInverse p j := by
    intro b
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [hj, hp, hretract]
  have hlin (b : R ⧸ I) (c : A ⧸ J) : p (j b * c) = b * p c := by
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective b
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
    rw [hj, ← map_mul, hp, hp, hlinear, map_mul]
  refine ⟨hcontract, ⟨j, p, hj, hjinj, hp, hret, hlin⟩, ?_, ?_⟩
  · exact normality_of_linear_retraction j hjinj p hlin hret
  · exact normality_of_linear_retraction ι hι ρ hlinear hretract

end RingHom
