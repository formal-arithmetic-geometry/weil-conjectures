/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M3
-/
module

public import Sheaf.RingTheory.PopescuLiftPartialChart

/-! # Comparing the partial chart with the full Popescu lifting algebra

Source: Stacks Project, Tag 07CP, the final local kernel calculation.
(blueprint: lem-weil-pbc-popescu-lift-chart-relations).
-/

@[expose] public section

universe a c

namespace Algebra.PopescuLiftPresentation

/-- Other charts' equations are pi-divisible in the partial chart local ring.

Source: Stacks Project, Tag 07CP (lemma-lifting), final three paragraphs.
(blueprint: lem-weil-pbc-popescu-lift-chart-relations).

Proof: Write u_l=f_l-pi*z_l and p_kl for the chart relations. The identity
pi*p_kl=-a_k*u_l+sum(h_klj*u_j) and invertibility of a_k show that every u_l
vanishes in the chart local ring (chart_original_equation_eq_zero). Compare the
conormal expressions for charts k and k': independence of the prepared conormal
basis makes b_j=a_k'*h_klj-sum(h_k'lj'*h_kj'j) vanish in Cbar localized at a_k.
Clear finitely many denominators to obtain a_k^N*b_j in I+pi^2*P. Multiplying
once more by a_k and using the cleared f-relations puts it in I_Ek+pi^2*P.
The exact expansion is
 a_k*p_k'l-a_k'*p_kl+sum(h_k'lj'*p_kj')=sum(b_j*z_j)+pi*delta,
where delta=-a_k*g_k'l+a_k'*g_kl-sum(h_k'lj'*g_kj'). Multiply by a_k^N.
The b_j terms now belong to I_Ek+pi^2*P, hence their multiples by z_j belong
to pi*D_k, since f_j=pi*z_j for j in E_k. The p_kl and p_kj' terms vanish
in D_k (normalization handles indices in E_k). Thus a_k^(N+1)*p_k'l is
in pi*D_k. Invert the unit a_k^(N+1) in the local ring and use membership
in the principal ideal (pi) to obtain p_k'l=pi*y. This gives the asserted divisibility, without
any flatness or equality-of-annihilators hypothesis. The separate, proved key
identity gives pi-torsion (chart_other_equation_pi_mul_eq_zero), which is not
part of this remaining statement. -/
theorem chart_relations_pi_divisible {R : Type a} {Cbar : Type c}
    [CommRing R] [CommRing Cbar] [Algebra R Cbar] (π : R)
    [Algebra (R ⧸ Ideal.span ({π ^ 2} : Set R)) Cbar]
    [IsScalarTower R (R ⧸ Ideal.span ({π ^ 2} : Set R)) Cbar]
    (d : PopescuLiftPresentation R Cbar π) (hd : d.Prepared)
    (k : Fin d.r) (q : PrimeSpectrum d.liftingAlgebra)
    (hk : ULift.up (Ideal.Quotient.mk d.definingIdeal (d.includeX (d.a k))) ∉ q.asIdeal)
    : ∀ (k' : Fin d.r) (l : Fin d.m),
      ∃ y : d.chartLocal k q,
        algebraMap (d.chartAlgebra k) (d.chartLocal k q)
          (ULift.up (Ideal.Quotient.mk (d.chartIdeal k) (d.equation (.inr (k', l))))) =
            algebraMap R (d.chartLocal k q) π * y := by sorry

private theorem localRingHom_bijective_of_kernel_vanishes
    {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : Function.Surjective f) (q : PrimeSpectrum B)
    (hker : ∀ x : A, f x = 0 →
      algebraMap A (Localization.AtPrime (PrimeSpectrum.comap f q).asIdeal) x = 0) :
    Function.Bijective (Localization.localRingHom (PrimeSpectrum.comap f q).asIdeal
      q.asIdeal f rfl) := by
  let p := PrimeSpectrum.comap f q
  let F := Localization.localRingHom p.asIdeal q.asIdeal f rfl
  constructor
  · apply (injective_iff_map_eq_zero F).mpr
    intro x hx
    obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq p.asIdeal.primeCompl x
    rw [Localization.localRingHom_mk', IsLocalization.mk'_eq_zero_iff] at hx
    obtain ⟨u, hu⟩ := hx
    obtain ⟨b, hb⟩ := hf u
    have hbunit : IsUnit (algebraMap A (Localization.AtPrime p.asIdeal) b) :=
      IsLocalization.map_units _ (⟨b, by
        change f b ∉ q.asIdeal
        simpa only [hb] using (Ideal.mem_primeCompl_iff.mp u.property)⟩ : p.asIdeal.primeCompl)
    have hba : algebraMap A (Localization.AtPrime p.asIdeal) (b * a) = 0 :=
      hker _ (by simpa only [map_mul, hb] using hu)
    rw [map_mul] at hba
    have ha : algebraMap A (Localization.AtPrime p.asIdeal) a = 0 :=
      hbunit.mul_right_eq_zero.mp hba
    rw [IsLocalization.mk'_eq_mul_mk'_one, ha, zero_mul]
  · intro z
    obtain ⟨b, t, rfl⟩ := IsLocalization.exists_mk'_eq q.asIdeal.primeCompl z
    obtain ⟨a, ha⟩ := hf b
    obtain ⟨s, hs⟩ := hf t
    let s' : p.asIdeal.primeCompl := ⟨s, by
      change f s ∉ q.asIdeal
      simpa only [hs] using (Ideal.mem_primeCompl_iff.mp t.property)⟩
    refine ⟨IsLocalization.mk' (Localization.AtPrime p.asIdeal) a s', ?_⟩
    change F (IsLocalization.mk' (Localization.AtPrime p.asIdeal) a s') = _
    dsimp only [F]
    rw [Localization.localRingHom_mk', ha]
    congr 1
    exact Subtype.ext hs

/-- Kill the extra equations using the chart's annihilator equality, then localize.

Source: Stacks Project, Tag 07CP, the final annihilator argument.
(blueprint: lem-weil-pbc-popescu-lift-chart-relations). -/
theorem chart_comparison_bijective {R : Type a} {Cbar : Type c}
    [CommRing R] [CommRing Cbar] [Algebra R Cbar] (π : R)
    [Algebra (R ⧸ Ideal.span ({π ^ 2} : Set R)) Cbar]
    [IsScalarTower R (R ⧸ Ideal.span ({π ^ 2} : Set R)) Cbar]
    (d : PopescuLiftPresentation R Cbar π) (hd : d.Prepared)
    (k : Fin d.r) (q : PrimeSpectrum d.liftingAlgebra)
    (hk : ULift.up (Ideal.Quotient.mk d.definingIdeal (d.includeX (d.a k))) ∉ q.asIdeal)
    (hAnn : Module.annihilator (d.chartLocal k q)
        (Ideal.span ({algebraMap R (d.chartLocal k q) π} : Set (d.chartLocal k q))) =
      Module.annihilator (d.chartLocal k q)
        (Ideal.span ({(algebraMap R (d.chartLocal k q) π) ^ 2} :
          Set (d.chartLocal k q)))) :
    Function.Bijective (Localization.localRingHom (d.chartPrime k q).asIdeal q.asIdeal
      (d.chartMap k).toRingHom rfl) := by
  classical
  let T := d.chartLocal k q
  let πT := algebraMap R T π
  let ev : d.polynomial →+* T :=
    (algebraMap (d.chartAlgebra k) T).comp
      ((ULift.algEquiv (R := R)).symm.toRingHom.comp (Ideal.Quotient.mk (d.chartIdeal k)))
  have hzero (t : Fin d.m ⊕ (Fin d.r × Fin d.m)) : ev (d.equation t) = 0 := by
    cases t with
    | inl l => exact d.chart_original_equation_eq_zero hd k q hk l
    | inr kl =>
      rcases kl with ⟨k', l⟩
      obtain ⟨y, hy⟩ := d.chart_relations_pi_divisible π hd k q hk k' l
      have hkill := d.chart_other_equation_pi_mul_eq_zero hd k q hk k' l
      change ev (d.equation (.inr (k', l))) = πT * y at hy
      change πT * ev (d.equation (.inr (k', l))) = 0 at hkill
      rw [hy] at hkill
      have hy2 : y ∈ Module.annihilator T (Ideal.span ({πT ^ 2} : Set T)) := by
        change y ∈ (Submodule.span T ({πT ^ 2} : Set T)).annihilator
        rw [Submodule.mem_annihilator_span_singleton, smul_eq_mul]
        calc
          y * πT ^ 2 = (πT * y) * πT := by
            rw [pow_two, ← mul_assoc, mul_comm y πT]
          _ = πT * (πT * y) := mul_comm _ _
          _ = 0 := hkill
      have hy1 : y ∈ Module.annihilator T (Ideal.span ({πT} : Set T)) := hAnn.symm ▸ hy2
      have hyπ : y * πT = 0 := by
        change y ∈ (Submodule.span T ({πT} : Set T)).annihilator at hy1
        rw [Submodule.mem_annihilator_span_singleton, smul_eq_mul] at hy1
        exact hy1
      rw [hy, mul_comm, hyπ]
  have hI : d.definingIdeal ≤ RingHom.ker ev := by
    apply Ideal.span_le.mpr
    rintro _ ⟨t, rfl⟩
    exact hzero t
  have hsurj : Function.Surjective (d.chartMap k) := by
    rintro ⟨b⟩
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective b
    exact ⟨ULift.up (Ideal.Quotient.mk (d.chartIdeal k) p), rfl⟩
  apply localRingHom_bijective_of_kernel_vanishes (d.chartMap k).toRingHom hsurj q
  rintro ⟨b⟩ hb
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective b
  have hp : p ∈ d.definingIdeal := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    exact congrArg ULift.down hb
  exact hI hp

end Algebra.PopescuLiftPresentation
