/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.Nakayama
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.RingTheory.Polynomial.UniversalFactorizationRing
public import Mathlib.RingTheory.Unramified.LocalStructure
public import WeilConjectures.Mathlib.RingTheory.Ideal.GoingUp
public import WeilConjectures.Mathlib.RingTheory.Idempotents
public import WeilConjectures.Mathlib.RingTheory.Jacobson.Ideal
public import WeilConjectures.Mathlib.RingTheory.Jacobson.Radical
public import WeilConjectures.Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import WeilConjectures.Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Finite algebras over Henselian local rings

A finite algebra `S` over a Henselian local ring `R` is a finite product of local rings, each
of which is again Henselian and finite over `R`, and strictly Henselian if `R` is.

## Main results

* `HenselianLocalRing.exists_monic_mul_of_map_eq_mul`: **Hensel's lemma for coprime
  factorizations**: over a Henselian local ring, a factorization of a monic polynomial into
  coprime monic factors over the residue field lifts.
* `HenselianLocalRing.liftsIdempotents_of_isIntegral`: an integral algebra over a Henselian
  local ring lifts idempotents.
* `HenselianLocalRing.exists_pi_isLocalRing_of_finite`: a finite algebra over a Henselian local
  ring is a finite product of local rings, each finite over the base.
* `HenselianLocalRing.of_finite`: a local ring finite over a Henselian local ring is Henselian.
* `HenselianLocalRing.exists_pi_of_finite` and
  `HenselianLocalRing.exists_pi_of_finite_of_isSepClosed`: the two previous results combined,
  [Stacks 04GH (1)](https://stacks.math.columbia.edu/tag/04GH).

## Implementation notes

The proofs of `HenselianLocalRing.exists_hasMap_of_hasMap_residueField`,
`HenselianLocalRing.exists_algHom_section` and
`HenselianLocalRing.exists_monic_mul_of_map_eq_mul` are the ones of the `proetale` project
(`Proetale/Algebra/IntegralLocal.lean`); they only use `Mathlib` and are reproved here since
the `proetale` files cannot be imported from a Lean module.
-/

@[expose] public section

universe u

open Polynomial IsLocalRing

/-- A commutative ring is local if it is local modulo an ideal contained in the Jacobson
radical. -/
theorem IsLocalRing.of_quotient_of_le_jacobson {A : Type*} [CommRing A] (I : Ideal A)
    (hI : I ≤ Ring.jacobson A) [IsLocalRing (A ⧸ I)] : IsLocalRing A := by
  have : Nontrivial A := (Ideal.Quotient.mk I).domain_nontrivial
  have hlh : IsLocalHom (Ideal.Quotient.mk I) :=
    isLocalHom_of_le_jacobson_bot I (by rwa [Ideal.jacobson_bot])
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a ↦ ?_
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (Ideal.Quotient.mk I a) with h | h
  · exact .inl (IsUnit.of_map _ a h)
  · refine .inr (IsUnit.of_map (Ideal.Quotient.mk I) (1 - a) ?_)
    simpa using h

namespace HenselianLocalRing

section Factorization

variable {R : Type u} [CommRing R] [HenselianLocalRing R]

/-- A point of a standard étale pair over a Henselian local ring `R` with values in the
residue field lifts to a point with values in `R`. -/
theorem exists_hasMap_of_hasMap_residueField (P : StandardEtalePair R)
    {x : (IsLocalRing.maximalIdeal R).ResidueField} (hx : P.HasMap x) :
    ∃ a : R, P.HasMap a ∧ algebraMap R (IsLocalRing.maximalIdeal R).ResidueField a = x := by
  obtain ⟨a₀, rfl⟩ := Ideal.algebraMap_residueField_surjective (IsLocalRing.maximalIdeal R) x
  have key : ∀ q : R[X],
      Polynomial.aeval (algebraMap R (IsLocalRing.maximalIdeal R).ResidueField a₀) q
        = algebraMap R (IsLocalRing.maximalIdeal R).ResidueField (q.eval a₀) := fun q ↦
    Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval a₀ q
  have hf0 : P.f.eval a₀ ∈ IsLocalRing.maximalIdeal R := by
    rw [← Ideal.algebraMap_residueField_eq_zero (I := IsLocalRing.maximalIdeal R), ← key]
    exact hx.1
  have hf' : IsUnit (P.f.derivative.eval a₀) := by
    have hd := hx.isUnit_derivative_f
    rw [key] at hd
    by_contra hcon
    have hmem : P.f.derivative.eval a₀ ∈ IsLocalRing.maximalIdeal R :=
      (IsLocalRing.mem_maximalIdeal _).mpr hcon
    rw [Ideal.algebraMap_residueField_eq_zero.mpr hmem] at hd
    exact not_isUnit_zero hd
  obtain ⟨a, hroot, hsub⟩ := HenselianLocalRing.is_henselian P.f P.monic_f a₀ hf0 hf'
  have hres : algebraMap R (IsLocalRing.maximalIdeal R).ResidueField a
      = algebraMap R (IsLocalRing.maximalIdeal R).ResidueField a₀ := by
    rw [← sub_eq_zero, ← map_sub, Ideal.algebraMap_residueField_eq_zero]
    exact hsub
  refine ⟨a, ⟨?_, ?_⟩, hres⟩
  · rw [show Polynomial.aeval a P.f = P.f.eval a from congrFun (Polynomial.coe_aeval_eq_eval a) _]
    exact hroot
  · rw [show Polynomial.aeval a P.g = P.g.eval a from congrFun (Polynomial.coe_aeval_eq_eval a) _]
    by_contra hcon
    have hmem : P.g.eval a ∈ IsLocalRing.maximalIdeal R :=
      (IsLocalRing.mem_maximalIdeal _).mpr hcon
    have h2 : algebraMap R (IsLocalRing.maximalIdeal R).ResidueField (P.g.eval a) = 0 :=
      Ideal.algebraMap_residueField_eq_zero.mpr hmem
    have h3 := hx.2
    rw [key] at h3
    have h4 : algebraMap R (IsLocalRing.maximalIdeal R).ResidueField (P.g.eval a)
        = algebraMap R (IsLocalRing.maximalIdeal R).ResidueField (P.g.eval a₀) := by
      rw [← Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval,
        ← Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval, hres]
    rw [← h4, h2] at h3
    exact not_isUnit_zero h3

/-- A Henselian local ring admits sections of étale algebras pointed over the residue
field. This is one implication of [Stacks 04GG (7)]
(https://stacks.math.columbia.edu/tag/04GG). -/
@[stacks 04GG "(7)"]
theorem exists_algHom_section {R' : Type u} [CommRing R'] [Algebra R R'] [Algebra.Etale R R']
    (χ : R' →ₐ[R] (IsLocalRing.maximalIdeal R).ResidueField) :
    ∃ σ : R' →ₐ[R] R,
      ∀ y, algebraMap R (IsLocalRing.maximalIdeal R).ResidueField (σ y) = χ y := by
  classical
  have hQp : (RingHom.ker χ.toRingHom).IsPrime := RingHom.ker_isPrime _
  have hFE : Algebra.FormallyEtale R (Localization.AtPrime (RingHom.ker χ.toRingHom)) :=
    inferInstanceAs (Algebra.FormallyEtale R (Localization (RingHom.ker χ.toRingHom).primeCompl))
  have hEt : Algebra.IsEtaleAt R (RingHom.ker χ.toRingHom) := hFE
  obtain ⟨h, hhQ, hstd⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := R)
    (RingHom.ker χ.toRingHom)
  have hu : ∀ y : Submonoid.powers h, IsUnit (χ y) := by
    rintro ⟨y, n, rfl⟩
    rw [map_pow]
    refine IsUnit.pow _ ?_
    rw [isUnit_iff_ne_zero]
    exact fun e ↦ hhQ (RingHom.mem_ker.mpr e)
  let χₗ : Localization.Away h →ₐ[R] (IsLocalRing.maximalIdeal R).ResidueField :=
    IsLocalization.liftAlgHom (M := Submonoid.powers h) (f := χ) hu
  have hχₗ : ∀ y : R', χₗ (algebraMap R' (Localization.Away h) y) = χ y := fun y ↦
    IsLocalization.lift_eq hu y
  obtain ⟨Pres⟩ := hstd.nonempty_standardEtalePresentation
  obtain ⟨a, ha, hares⟩ := exists_hasMap_of_hasMap_residueField Pres.P (Pres.hasMap.map χₗ)
  let σ₀ : Localization.Away h →ₐ[R] R := (Pres.P.lift a ha).comp Pres.equivRing.toAlgHom
  have key : (IsScalarTower.toAlgHom R R (IsLocalRing.maximalIdeal R).ResidueField).comp σ₀
      = χₗ := by
    refine Pres.hom_ext ?_
    change algebraMap R (IsLocalRing.maximalIdeal R).ResidueField (σ₀ Pres.x) = χₗ Pres.x
    have hx : σ₀ Pres.x = a := by
      change (Pres.P.lift a ha) (Pres.equivRing Pres.x) = a
      rw [Pres.equivRing_x, Pres.P.lift_X]
    rw [hx, hares]
  refine ⟨σ₀.comp (IsScalarTower.toAlgHom R R' (Localization.Away h)), fun y ↦ ?_⟩
  calc algebraMap R (IsLocalRing.maximalIdeal R).ResidueField
        (σ₀ (algebraMap R' (Localization.Away h) y))
      = ((IsScalarTower.toAlgHom R R (IsLocalRing.maximalIdeal R).ResidueField).comp σ₀)
          (algebraMap R' (Localization.Away h) y) := rfl
    _ = χₗ (algebraMap R' (Localization.Away h) y) := by rw [key]
    _ = χ y := hχₗ y

/-- **Hensel's lemma for coprime factorizations.**  Over a Henselian local ring, a
factorization of a monic polynomial into coprime monic factors over the residue field
lifts to a factorization into monic factors.

This is one implication of [Stacks 04GG (3)](https://stacks.math.columbia.edu/tag/04GG). -/
@[stacks 04GG "(3)"]
theorem exists_monic_mul_of_map_eq_mul
    {p : R[X]} (hp : p.Monic)
    {f g : Polynomial (IsLocalRing.maximalIdeal R).ResidueField}
    (hf : f.Monic) (hg : g.Monic)
    (H : p.map (algebraMap R (IsLocalRing.maximalIdeal R).ResidueField) = f * g)
    (hco : IsCoprime f g) :
    ∃ p₁ p₂ : R[X], p₁.Monic ∧ p₂.Monic ∧ p = p₁ * p₂ ∧
      p₁.map (algebraMap R (IsLocalRing.maximalIdeal R).ResidueField) = f ∧
      p₂.map (algebraMap R (IsLocalRing.maximalIdeal R).ResidueField) = g := by
  obtain ⟨R', _, _, _, Q, _, _, f', g', hbij, hf'm, hg'm, hmul, -, hfres, hgres⟩ :=
    Algebra.exists_etale_bijective_residueFieldMap_and_map_eq_mul_and_isCoprime
      (IsLocalRing.maximalIdeal R) p f g hp hf hg H hco
  let e : (IsLocalRing.maximalIdeal R).ResidueField ≃ₐ[R] Q.ResidueField :=
    AlgEquiv.ofBijective _ hbij
  let χ : R' →ₐ[R] (IsLocalRing.maximalIdeal R).ResidueField :=
    e.symm.toAlgHom.comp (IsScalarTower.toAlgHom R R' Q.ResidueField)
  obtain ⟨σ, hσ⟩ := exists_algHom_section χ
  have hσ' : (algebraMap R (IsLocalRing.maximalIdeal R).ResidueField).comp σ.toRingHom
      = χ.toRingHom := RingHom.ext hσ
  have hid : (e.symm.toAlgHom.toRingHom).comp
      (Ideal.ResidueField.mapₐ (IsLocalRing.maximalIdeal R) Q (Algebra.ofId R R')
        (Ideal.over_def Q (IsLocalRing.maximalIdeal R))).toRingHom = RingHom.id _ := by
    have hcoe : (Ideal.ResidueField.mapₐ (IsLocalRing.maximalIdeal R) Q (Algebra.ofId R R')
        (Ideal.over_def Q (IsLocalRing.maximalIdeal R))).toRingHom = e.toAlgHom.toRingHom := rfl
    rw [hcoe]
    ext z
    simp
  have hχ : χ.toRingHom = (e.symm.toAlgHom.toRingHom).comp (algebraMap R' Q.ResidueField) := rfl
  refine ⟨f'.map σ.toRingHom, g'.map σ.toRingHom, hf'm.map _, hg'm.map _, ?_, ?_, ?_⟩
  · have hcomp : σ.toRingHom.comp (algebraMap R R') = RingHom.id R := by
      ext r
      simp
    have hh := congrArg (Polynomial.map σ.toRingHom) hmul
    rwa [Polynomial.map_map, hcomp, Polynomial.map_id, Polynomial.map_mul] at hh
  · rw [Polynomial.map_map, hσ', hχ, ← Polynomial.map_map, ← hfres, Polynomial.map_map, hid,
      Polynomial.map_id]
  · rw [Polynomial.map_map, hσ', hχ, ← Polynomial.map_map, ← hgres, Polynomial.map_map, hid,
      Polynomial.map_id]

/-- **Hensel's lemma for coprime factorizations**, in terms of the quotient by the maximal
ideal: over a Henselian local ring, a factorization of a monic polynomial into coprime monic
factors modulo the maximal ideal lifts to a factorization into monic factors.

This is one implication of [Stacks 04GG (3)](https://stacks.math.columbia.edu/tag/04GG). -/
@[stacks 04GG "(3)"]
theorem exists_monic_mul_of_map_mk_eq_mul {p : R[X]} (hp : p.Monic)
    {f g : Polynomial (R ⧸ maximalIdeal R)} (hf : f.Monic) (hg : g.Monic)
    (H : p.map (Ideal.Quotient.mk (maximalIdeal R)) = f * g) (hco : IsCoprime f g) :
    ∃ p₁ p₂ : R[X], p₁.Monic ∧ p₂.Monic ∧ p = p₁ * p₂ ∧
      p₁.map (Ideal.Quotient.mk (maximalIdeal R)) = f ∧
      p₂.map (Ideal.Quotient.mk (maximalIdeal R)) = g := by
  set φ := Ideal.Quotient.mk (maximalIdeal R)
  set ε := algebraMap (R ⧸ maximalIdeal R) (maximalIdeal R).ResidueField
  have hεinj : Function.Injective ε := Ideal.injective_algebraMap_quotient_residueField _
  have hcomp : (algebraMap R (maximalIdeal R).ResidueField) = ε.comp φ :=
    IsScalarTower.algebraMap_eq R (R ⧸ maximalIdeal R) _
  have H' : p.map (algebraMap R (maximalIdeal R).ResidueField) = f.map ε * g.map ε := by
    rw [hcomp, ← Polynomial.map_map, H, Polynomial.map_mul]
  obtain ⟨p₁, p₂, hp₁, hp₂, hmul, h₁, h₂⟩ :=
    exists_monic_mul_of_map_eq_mul hp (hf.map ε) (hg.map ε) H' (hco.map (Polynomial.mapRingHom ε))
  refine ⟨p₁, p₂, hp₁, hp₂, hmul, ?_, ?_⟩
  · refine Polynomial.map_injective ε hεinj ?_
    rw [Polynomial.map_map, ← hcomp, h₁]
  · refine Polynomial.map_injective ε hεinj ?_
    rw [Polynomial.map_map, ← hcomp, h₂]

end Factorization

section LiftIdempotents

variable {R : Type u} [CommRing R] [HenselianLocalRing R]

/-- Monogenic finite algebras over a Henselian local ring lift idempotents.

The proof is an induction on the degree: if the reduction of `f` modulo the maximal ideal is a
power of an irreducible polynomial, then `AdjoinRoot f` is local, and otherwise Hensel's lemma
for coprime factorizations splits `AdjoinRoot f` as a product of two algebras of smaller
degree. -/
private theorem liftsIdempotents_adjoinRoot_aux (n : ℕ) :
    ∀ f : R[X], f.Monic → f.natDegree ≤ n → Ring.LiftsIdempotents (AdjoinRoot f) := by
  classical
  let _ : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _
  have hsub : ∀ f : R[X], f.Monic → f.natDegree = 0 → Ring.LiftsIdempotents (AdjoinRoot f) := by
    intro f hf h0
    have h1 : f = 1 := hf.natDegree_eq_zero.mp h0
    have : Subsingleton (AdjoinRoot f) := by
      refine Ideal.Quotient.subsingleton_iff.mpr ?_
      rw [h1, Ideal.span_singleton_eq_top]
      exact isUnit_one
    exact Ring.liftsIdempotents_of_subsingleton
  induction n with
  | zero => exact fun f hf hfd ↦ hsub f hf (Nat.le_zero.mp hfd)
  | succ n ih =>
    intro f hf hfd
    rcases Nat.eq_zero_or_pos f.natDegree with h0 | hpos
    · exact hsub f hf h0
    have : Module.Finite R (AdjoinRoot f) := hf.finite_adjoinRoot
    have : Algebra.IsIntegral R (AdjoinRoot f) := Algebra.IsIntegral.of_finite R _
    have hjac : (maximalIdeal R).map (AdjoinRoot.of f) ≤ Ring.jacobson (AdjoinRoot f) := by
      rw [show AdjoinRoot.of f = algebraMap R (AdjoinRoot f) from rfl]
      exact IsLocalRing.map_maximalIdeal_le_jacobson R (AdjoinRoot f)
    set φ := Ideal.Quotient.mk (maximalIdeal R) with hφ
    set q := f.map φ
    have hq : q.Monic := hf.map φ
    have hqd : q.natDegree = f.natDegree := hf.natDegree_map φ
    obtain ⟨p, hpm, hp, hpdvd⟩ := Polynomial.exists_monic_irreducible_factor q (by
      intro hu
      have h0 : q.natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit (p := q) hu
      omega)
    have hpdeg : 0 < p.natDegree := hp.natDegree_pos
    set k := Nat.findGreatest (fun m ↦ p ^ m ∣ q) q.natDegree
    have hk1 : 1 ≤ k := Nat.le_findGreatest (P := fun m ↦ p ^ m ∣ q) (by rw [hqd]; omega)
      (by simpa using hpdvd)
    have hpk : p ^ k ∣ q :=
      Nat.findGreatest_spec (P := fun m ↦ p ^ m ∣ q) (m := 1) (by omega) (by simpa using hpdvd)
    have hnot : ¬ p ^ (k + 1) ∣ q := by
      intro hdvd
      have hle : (k + 1) * p.natDegree ≤ q.natDegree := by
        have := Polynomial.natDegree_le_of_dvd hdvd hq.ne_zero
        rwa [Polynomial.natDegree_pow] at this
      have : k + 1 ≤ q.natDegree := le_trans (by nlinarith) hle
      exact Nat.findGreatest_is_greatest (P := fun m ↦ p ^ m ∣ q) (by omega) this hdvd
    obtain ⟨r, hrq⟩ := hpk
    have hrm : r.Monic := ((hpm.pow k).of_mul_monic_left (hrq ▸ hq))
    have hpr : ¬ p ∣ r := by
      intro ⟨c, hc⟩
      exact hnot ⟨c, by rw [hrq, hc, pow_succ, mul_assoc]⟩
    have hcop : IsCoprime (p ^ k) r := ((hp.isCoprime_or_dvd r).resolve_right hpr).pow_left
    rcases Nat.eq_zero_or_pos r.natDegree with hr0 | hrpos
    · -- `q` is a power of an irreducible, hence `AdjoinRoot f` is local
      have hr1 : r = 1 := hrm.natDegree_eq_zero.mp hr0
      have hqp : q = p ^ k := by rw [hrq, hr1, mul_one]
      have : IsLocalRing (Polynomial (R ⧸ maximalIdeal R) ⧸ Ideal.span {q}) := by
        rw [hqp]
        exact isLocalRing_quotient_span_singleton_pow hp (by omega)
      have : IsLocalRing (AdjoinRoot f ⧸ (maximalIdeal R).map (AdjoinRoot.of f)) :=
        (AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot (maximalIdeal R) f).symm.isLocalRing
      have : IsLocalRing (AdjoinRoot f) :=
        IsLocalRing.of_quotient_of_le_jacobson _ hjac
      exact Ring.liftsIdempotents_of_isLocalRing
    · -- `q` splits into coprime factors, so `AdjoinRoot f` splits
      obtain ⟨f₁, f₂, hf₁, hf₂, hfmul, hf₁map, hf₂map⟩ :=
        exists_monic_mul_of_map_mk_eq_mul hf (hpm.pow k) hrm hrq hcop
      have hd₁ : f₁.natDegree = k * p.natDegree := by
        rw [← hf₁.natDegree_map φ, hf₁map, Polynomial.natDegree_pow]
      have hd₂ : f₂.natDegree = r.natDegree := by rw [← hf₂.natDegree_map φ, hf₂map]
      have hdsum : f.natDegree = f₁.natDegree + f₂.natDegree := by
        rw [hfmul, hf₁.natDegree_mul hf₂]
      have hle₁ : f₁.natDegree ≤ n := by nlinarith [hd₁, hd₂, hdsum, hfd]
      have hle₂ : f₂.natDegree ≤ n := by nlinarith [hd₁, hd₂, hdsum, hfd]
      have hdvd₁ : f₁ ∣ f := ⟨f₂, hfmul⟩
      have hdvd₂ : f₂ ∣ f := ⟨f₁, by rw [hfmul]; ring⟩
      have hsup : Ideal.span {AdjoinRoot.mk f f₁} ⊔ Ideal.span {AdjoinRoot.mk f f₂} = ⊤ := by
        refine Ideal.eq_top_of_sup_eq_top_of_le_jacobson hjac ?_
        rw [Ideal.eq_top_iff_one]
        obtain ⟨u, v, huv⟩ := hcop
        obtain ⟨U, hU⟩ := Polynomial.map_surjective φ Ideal.Quotient.mk_surjective u
        obtain ⟨V, hV⟩ := Polynomial.map_surjective φ Ideal.Quotient.mk_surjective v
        have hw : (U * f₁ + V * f₂ - 1).map φ = 0 := by
          rw [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul,
            hU, hV, hf₁map, hf₂map, Polynomial.map_one, huv, sub_self]
        have hwmem : (U * f₁ + V * f₂ - 1) ∈ (maximalIdeal R).map (Polynomial.C) := by
          rw [Ideal.mem_map_C_iff]
          intro i
          have h := congrArg (fun g ↦ Polynomial.coeff g i) hw
          simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at h
          rwa [hφ, Ideal.Quotient.eq_zero_iff_mem] at h
        have hmapeq : (maximalIdeal R).map (AdjoinRoot.of f)
            = ((maximalIdeal R).map (Polynomial.C)).map (AdjoinRoot.mk f) := by
          rw [Ideal.map_map]; rfl
        have hmem : AdjoinRoot.mk f (U * f₁ + V * f₂ - 1)
            ∈ (maximalIdeal R).map (AdjoinRoot.of f) := by
          rw [hmapeq]; exact Ideal.mem_map_of_mem _ hwmem
        have key : (1 : AdjoinRoot f) = (AdjoinRoot.mk f U * AdjoinRoot.mk f f₁
            + AdjoinRoot.mk f V * AdjoinRoot.mk f f₂)
            - AdjoinRoot.mk f (U * f₁ + V * f₂ - 1) := by
          simp only [map_sub, map_add, map_mul, map_one]
          ring
        rw [key]
        refine sub_mem (Ideal.add_mem _ ?_ ?_) (Ideal.mem_sup_right hmem)
        · exact Ideal.mem_sup_left (Ideal.mem_sup_left
            (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)))
        · exact Ideal.mem_sup_left (Ideal.mem_sup_right
            (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)))
      have hcopJ : IsCoprime (Ideal.span {AdjoinRoot.mk f f₁}) (Ideal.span {AdjoinRoot.mk f f₂}) :=
        Ideal.isCoprime_iff_sup_eq.mpr hsup
      have hinf : Ideal.span {AdjoinRoot.mk f f₁} ⊓ Ideal.span {AdjoinRoot.mk f f₂} = ⊥ := by
        rw [← Ideal.mul_eq_inf_of_isCoprime hcopJ, Ideal.span_singleton_mul_span_singleton,
          ← map_mul, ← hfmul, AdjoinRoot.mk_self]
        exact Ideal.span_singleton_eq_bot.mpr rfl
      refine Ring.LiftsIdempotents.of_isCoprime hcopJ hinf ?_ ?_
      · refine (ih f₁ hf₁ hle₁).of_ringEquiv ?_
        have hspan : Ideal.span {f} ⊔ Ideal.span {f₁} = Ideal.span {f₁} :=
          sup_eq_right.mpr (Ideal.span_singleton_le_span_singleton.mpr hdvd₁)
        have hJeq : Ideal.span {AdjoinRoot.mk f f₁} = (Ideal.span {f₁}).map (AdjoinRoot.mk f) := by
          rw [Ideal.map_span, Set.image_singleton]
        exact (((Ideal.quotEquivOfEq hJeq).trans
          (DoubleQuot.quotQuotEquivQuotSup (Ideal.span {f}) (Ideal.span {f₁}))).trans
          (Ideal.quotEquivOfEq hspan)).symm
      · refine (ih f₂ hf₂ hle₂).of_ringEquiv ?_
        have hspan : Ideal.span {f} ⊔ Ideal.span {f₂} = Ideal.span {f₂} :=
          sup_eq_right.mpr (Ideal.span_singleton_le_span_singleton.mpr hdvd₂)
        have hJeq : Ideal.span {AdjoinRoot.mk f f₂} = (Ideal.span {f₂}).map (AdjoinRoot.mk f) := by
          rw [Ideal.map_span, Set.image_singleton]
        exact (((Ideal.quotEquivOfEq hJeq).trans
          (DoubleQuot.quotQuotEquivQuotSup (Ideal.span {f}) (Ideal.span {f₂}))).trans
          (Ideal.quotEquivOfEq hspan)).symm


/-- An integral algebra over a Henselian local ring lifts idempotents:
if `x` is idempotent modulo an ideal `I`, there is an idempotent congruent to `x` modulo `I`.

The key input is Hensel's lemma for coprime factorizations, applied to a monic polynomial
annihilating `x`. -/
theorem liftsIdempotents_of_isIntegral (S : Type*) [CommRing S] [Algebra R S]
    [Algebra.IsIntegral R S] : Ring.LiftsIdempotents S := by
  intro I x hx
  obtain ⟨f, hf, hfx⟩ := Algebra.IsIntegral.isIntegral (R := R) x
  have hroot : f.eval₂ (algebraMap R S) x = 0 := hfx
  set ψ : AdjoinRoot f →+* S := AdjoinRoot.lift (algebraMap R S) x hroot
  have hψroot : ψ (AdjoinRoot.root f) = x := AdjoinRoot.lift_root hroot
  obtain ⟨e, he, hex⟩ := liftsIdempotents_adjoinRoot_aux f.natDegree f hf le_rfl
    (I.comap ψ) (AdjoinRoot.root f) (by
      rw [Ideal.mem_comap, map_sub, map_mul, hψroot]
      exact hx)
  refine ⟨ψ e, he.map ψ, ?_⟩
  have h := hex
  rw [Ideal.mem_comap, map_sub, hψroot] at h
  exact h

end LiftIdempotents

section Decomposition

variable (R : Type u) [CommRing R] [IsLocalRing R]
variable (S : Type u) [CommRing S] [Algebra R S]

private theorem finite_quotient [Module.Finite R S] : Module.Finite (R ⧸ maximalIdeal R)
    (S ⧸ (maximalIdeal R).map (algebraMap R S)) := by
  have : Module.Finite R (S ⧸ (maximalIdeal R).map (algebraMap R S)) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ R _).toLinearMap Ideal.Quotient.mk_surjective
  exact Module.Finite.of_restrictScalars_finite R _ _

/-- The image in `S ⧸ m_R S` of the ideal generated by `ε`, viewed as a vector space over the
residue field of `R`. Its dimension is the induction measure for the decomposition of a finite
algebra into local factors. -/
private noncomputable def idemSubmodule (ε : S) :
    Submodule (R ⧸ maximalIdeal R) (S ⧸ (maximalIdeal R).map (algebraMap R S)) :=
  ((Ideal.span {ε}).map
    (Ideal.Quotient.mk ((maximalIdeal R).map (algebraMap R S)))).restrictScalars _

variable [Module.Finite R S]

private theorem eq_zero_of_finrank_idemSubmodule_eq_zero {ε : S} (hε : IsIdempotentElem ε)
    (h : Module.finrank (R ⧸ maximalIdeal R) (idemSubmodule R S ε) = 0) : ε = 0 := by
  let _ : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _
  have := finite_quotient R S
  have hbot : idemSubmodule R S ε = ⊥ := Submodule.finrank_eq_zero.mp h
  have hmem : Ideal.Quotient.mk ((maximalIdeal R).map (algebraMap R S)) ε ∈ idemSubmodule R S ε :=
    Ideal.mem_map_of_mem _ (Ideal.mem_span_singleton_self _)
  rw [hbot, Submodule.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at hmem
  exact hε.eq_zero_of_mem_jacobson
    (IsLocalRing.map_maximalIdeal_le_jacobson R S hmem)

private theorem finrank_idemSubmodule_lt {ε ε₁ ε₂ : S} (hε₂ : IsIdempotentElem ε₂)
    (h₁ : ε₁ * ε = ε₁) (h₂ : ε₂ * ε = ε₂) (horth : ε₁ * ε₂ = 0) (hne : ε₂ ≠ 0) :
    Module.finrank (R ⧸ maximalIdeal R) (idemSubmodule R S ε₁) <
      Module.finrank (R ⧸ maximalIdeal R) (idemSubmodule R S ε) := by
  let _ : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _
  have := finite_quotient R S
  refine Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne ?_ ?_)
  · rw [idemSubmodule, idemSubmodule, Submodule.restrictScalars_le]
    exact Ideal.map_mono (Ideal.span_singleton_le_span_singleton.mpr
      ⟨ε₁, by rw [mul_comm]; exact h₁.symm⟩)
  · intro heq
    have hmem : Ideal.Quotient.mk ((maximalIdeal R).map (algebraMap R S)) ε₂
        ∈ idemSubmodule R S ε₁ := by
      rw [heq]
      exact Ideal.mem_map_of_mem _
        (Ideal.mem_span_singleton.mpr ⟨ε₂, by rw [mul_comm]; exact h₂.symm⟩)
    rw [idemSubmodule, Submodule.restrictScalars_mem, Ideal.map_span, Set.image_singleton,
      Ideal.mem_span_singleton'] at hmem
    obtain ⟨v, hv⟩ := hmem
    have hz : Ideal.Quotient.mk ((maximalIdeal R).map (algebraMap R S)) ε₂ = 0 := by
      calc Ideal.Quotient.mk ((maximalIdeal R).map (algebraMap R S)) ε₂
          = Ideal.Quotient.mk _ ε₂ * Ideal.Quotient.mk _ ε₂ := by
            rw [← map_mul, hε₂.eq]
        _ = v * (Ideal.Quotient.mk _ ε₁ * Ideal.Quotient.mk _ ε₂) := by rw [← hv]; ring
        _ = 0 := by rw [← map_mul, horth, map_zero, mul_zero]
    rw [Ideal.Quotient.eq_zero_iff_mem] at hz
    exact hne (hε₂.eq_zero_of_mem_jacobson (IsLocalRing.map_maximalIdeal_le_jacobson R S hz))

end Decomposition

section Sum

variable (R : Type u) [CommRing R] [HenselianLocalRing R]
variable (S : Type u) [CommRing S] [Algebra R S] [Module.Finite R S]

/-- `ε` is a sum of finitely many pairwise orthogonal idempotents below `ε` whose associated
factor rings are local. -/
private def IsSumOfLocalIdempotents (ε : S) : Prop :=
  ∃ (ι : Type u) (_ : Fintype ι) (e : ι → S), (∀ i, IsIdempotentElem (e i)) ∧
    (∀ i j, i ≠ j → e i * e j = 0) ∧ (∀ i, e i * ε = e i) ∧ (∑ i, e i = ε) ∧
    ∀ i, IsLocalRing (S ⧸ Ideal.span {1 - e i})

private theorem isSumOfLocalIdempotents_zero : IsSumOfLocalIdempotents S (0 : S) :=
  ⟨PEmpty, inferInstance, PEmpty.elim, (fun i ↦ i.elim), (fun i ↦ i.elim), (fun i ↦ i.elim),
    by simp, fun i ↦ i.elim⟩

private theorem isSumOfLocalIdempotents_aux (n : ℕ) :
    ∀ ε : S, IsIdempotentElem ε →
      Module.finrank (R ⧸ maximalIdeal R) (idemSubmodule R S ε) ≤ n →
      IsSumOfLocalIdempotents S ε := by
  induction n with
  | zero =>
    intro ε hε hrk
    have h0 : ε = 0 := eq_zero_of_finrank_idemSubmodule_eq_zero R S hε (Nat.le_zero.mp hrk)
    exact h0 ▸ isSumOfLocalIdempotents_zero S
  | succ n ih =>
    intro ε hε hrk
    rcases eq_or_ne ε 0 with rfl | hε0
    · exact isSumOfLocalIdempotents_zero S
    have hntop : Ideal.span {1 - ε} ≠ ⊤ := by
      intro htop
      have hu : IsUnit (1 - ε) := Ideal.span_singleton_eq_top.mp htop
      have h1 : (1 : S) - ε = 1 := hε.one_sub.eq_one_of_isUnit hu
      exact hε0 (by linear_combination -h1)
    have hnt : Nontrivial (S ⧸ Ideal.span {1 - ε}) := Ideal.Quotient.nontrivial_iff.mpr hntop
    by_cases hloc : IsLocalRing (S ⧸ Ideal.span {1 - ε})
    · exact ⟨PUnit, inferInstance, fun _ ↦ ε, fun _ ↦ hε,
        (fun i j hij ↦ absurd (Subsingleton.elim i j) hij), fun _ ↦ hε.eq, by simp, fun _ ↦ hloc⟩
    -- `S ⧸ ⟨1 - ε⟩` is not local, so it has two distinct maximal ideals
    obtain ⟨N₁, hN₁⟩ := Ideal.exists_maximal (S ⧸ Ideal.span {1 - ε})
    obtain ⟨N₂, hN₂, hNne⟩ : ∃ N₂ : Ideal (S ⧸ Ideal.span {1 - ε}), N₂.IsMaximal ∧ N₂ ≠ N₁ := by
      by_contra hcon
      push Not at hcon
      exact hloc (IsLocalRing.of_unique_max_ideal ⟨N₁, hN₁, fun J hJ ↦ hcon J hJ⟩)
    have hsurj := Ideal.Quotient.mk_surjective (I := Ideal.span {(1 : S) - ε})
    have hM₁ : (N₁.comap (Ideal.Quotient.mk (Ideal.span {(1 : S) - ε}))).IsMaximal :=
      Ideal.comap_isMaximal_of_surjective _ hsurj
    have hM₂ : (N₂.comap (Ideal.Quotient.mk (Ideal.span {(1 : S) - ε}))).IsMaximal :=
      Ideal.comap_isMaximal_of_surjective _ hsurj
    set M₁ := N₁.comap (Ideal.Quotient.mk (Ideal.span {(1 : S) - ε})) with hM₁def
    set M₂ := N₂.comap (Ideal.Quotient.mk (Ideal.span {(1 : S) - ε})) with hM₂def
    have hMne : M₁ ≠ M₂ := by
      intro h
      refine hNne ?_
      rw [← Ideal.map_comap_of_surjective _ hsurj N₂, ← Ideal.map_comap_of_surjective _ hsurj N₁,
        ← hM₁def, ← hM₂def, h]
    have hmemgen : ∀ M : Ideal (S ⧸ Ideal.span {(1 : S) - ε}),
        (1 : S) - ε ∈ M.comap (Ideal.Quotient.mk (Ideal.span {(1 : S) - ε})) := by
      intro M
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)]
      exact M.zero_mem
    have hεM₁ : (1 : S) - ε ∈ M₁ := hmemgen N₁
    have hεM₂ : (1 : S) - ε ∈ M₂ := hmemgen N₂
    have hcopM : M₁ ⊔ M₂ = ⊤ := hM₁.coprime_of_ne hM₂ hMne
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp
      (show (1 : S) ∈ M₁ ⊔ M₂ from hcopM ▸ Submodule.mem_top)
    have hbb : b * b - b ∈ M₁ ⊓ M₂ := by
      refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
      · have h : b * b - b = -(b * a) := by linear_combination b * hab
        rw [h]
        exact neg_mem (Ideal.mul_mem_left M₁ b ha)
      · exact Ideal.sub_mem M₂ (Ideal.mul_mem_left M₂ b hb) hb
    obtain ⟨d, hd, hdb⟩ := liftsIdempotents_of_isIntegral (R := R) S (M₁ ⊓ M₂) b hbb
    obtain ⟨hdb₁, hdb₂⟩ := Submodule.mem_inf.mp hdb
    have hdM₂ : d ∈ M₂ := by
      have h : d = (d - b) + b := by ring
      rw [h]
      exact Ideal.add_mem M₂ hdb₂ hb
    have hdM₁ : d ∉ M₁ := by
      intro hcon
      have hd1 : (1 : S) - d ∈ M₁ := by
        have h : (1 : S) - d = a - (d - b) := by linear_combination -hab
        rw [h]
        exact Ideal.sub_mem M₁ ha hdb₁
      refine hM₁.ne_top ((Ideal.eq_top_iff_one M₁).mpr ?_)
      have h2 := Ideal.add_mem M₁ hd1 hcon
      simpa using h2
    have hεu : ε * (d * ε) = d * ε := by
      calc ε * (d * ε) = d * (ε * ε) := by ring
        _ = d * ε := by rw [hε.eq]
    have hδ : IsIdempotentElem (d * ε) := by
      change d * ε * (d * ε) = d * ε
      calc d * ε * (d * ε) = d * d * (ε * ε) := by ring
        _ = d * ε := by rw [hd.eq, hε.eq]
    have hδε : d * ε * ε = d * ε := by rw [mul_assoc, hε.eq]
    have hδ0 : d * ε ≠ 0 := by
      intro hcon
      refine hdM₁ ?_
      have h : d = d * ε + d * (1 - ε) := by ring
      rw [h, hcon, zero_add]
      exact Ideal.mul_mem_left M₁ d hεM₁
    have hε₂ : IsIdempotentElem (ε - d * ε) := by
      change (ε - d * ε) * (ε - d * ε) = ε - d * ε
      linear_combination hε.eq - 2 * hεu + hδ.eq
    have hε₂ε : (ε - d * ε) * ε = ε - d * ε := by linear_combination hε.eq - hεu
    have horth : d * ε * (ε - d * ε) = 0 := by linear_combination hεu - hδ.eq
    have hε₂0 : ε - d * ε ≠ 0 := by
      intro hcon
      refine hM₂.ne_top ((Ideal.eq_top_iff_one M₂).mpr ?_)
      have h : (1 : S) = (1 - ε) + d * ε := by linear_combination hcon
      rw [h]
      exact Ideal.add_mem M₂ hεM₂ (Ideal.mul_mem_right ε M₂ hdM₂)
    have hlt₁ : Module.finrank (R ⧸ maximalIdeal R) (idemSubmodule R S (d * ε)) ≤ n := by
      have := finrank_idemSubmodule_lt R S hε₂ hδε hε₂ε horth hε₂0
      omega
    have hlt₂ : Module.finrank (R ⧸ maximalIdeal R) (idemSubmodule R S (ε - d * ε)) ≤ n := by
      have := finrank_idemSubmodule_lt R S hδ hε₂ε hδε (by linear_combination horth) hδ0
      omega
    obtain ⟨ι₁, _, e₁, hidem₁, horth₁, hsub₁, hsum₁, hlocal₁⟩ := ih (d * ε) hδ hlt₁
    obtain ⟨ι₂, _, e₂, hidem₂, horth₂, hsub₂, hsum₂, hlocal₂⟩ := ih (ε - d * ε) hε₂ hlt₂
    refine ⟨ι₁ ⊕ ι₂, inferInstance, Sum.elim e₁ e₂, ?_, ?_, ?_, ?_, ?_⟩
    · rintro (i | i)
      · exact hidem₁ i
      · exact hidem₂ i
    · rintro (i | i) (j | j) hij
      · exact horth₁ i j (by simpa using hij)
      · change e₁ i * e₂ j = 0
        linear_combination (-(e₂ j * (ε - d * ε))) * hsub₁ i - e₁ i * hsub₂ j +
          e₁ i * e₂ j * horth
      · change e₂ i * e₁ j = 0
        linear_combination (-(e₁ j * (d * ε))) * hsub₂ i - e₂ i * hsub₁ j +
          e₂ i * e₁ j * horth
      · exact horth₂ i j (by simpa using hij)
    · rintro (i | i)
      · change e₁ i * ε = e₁ i
        linear_combination (-ε) * hsub₁ i + hsub₁ i + e₁ i * hδε
      · change e₂ i * ε = e₂ i
        linear_combination (-ε) * hsub₂ i + hsub₂ i + e₂ i * hε₂ε
    · rw [Fintype.sum_sum_type]
      change (∑ i, e₁ i) + (∑ i, e₂ i) = ε
      rw [hsum₁, hsum₂]
      ring
    · rintro (i | i)
      · exact hlocal₁ i
      · exact hlocal₂ i

/-- **A finite algebra over a Henselian local ring is a finite product of local rings**, each
finite over the base.

This is the ring-theoretic content of [Stacks 04GH (1)]
(https://stacks.math.columbia.edu/tag/04GH); see `exists_pi_of_finite` for the refinement
saying that the factors are again Henselian. -/
@[stacks 04GH "(1)"]
theorem exists_pi_isLocalRing_of_finite :
    ∃ (ι : Type u) (_ : Fintype ι) (B : ι → Type u) (_ : ∀ i, CommRing (B i))
      (_ : ∀ i, IsLocalRing (B i)) (_ : ∀ i, Algebra R (B i)) (_ : ∀ i, Module.Finite R (B i)),
        Nonempty (S ≃ₐ[R] (Π i, B i)) := by
  obtain ⟨ι, hι, e, hidem, horth, -, hsum, hlocal⟩ :=
    isSumOfLocalIdempotents_aux R S
      (Module.finrank (R ⧸ maximalIdeal R) (idemSubmodule R S 1)) 1
      (by change (1 : S) * 1 = 1; ring) le_rfl
  have hcoi : CompleteOrthogonalIdempotents e :=
    ⟨⟨hidem, fun i j hij ↦ horth i j hij⟩, hsum⟩
  refine ⟨ι, hι, fun i ↦ S ⧸ Ideal.span {1 - e i}, fun i ↦ inferInstance, hlocal,
    fun i ↦ inferInstance, fun i ↦ ?_, ⟨?_⟩⟩
  · exact Module.Finite.of_surjective (Ideal.Quotient.mkₐ R _).toLinearMap
      Ideal.Quotient.mk_surjective
  · exact AlgEquiv.ofBijective
      (AlgHom.pi fun i ↦ Ideal.Quotient.mkₐ R (Ideal.span {1 - e i})) hcoi.bijective_pi

end Sum

section Local

/-- Let `B` be a local ring and `C` a nonzero finite free `B`-algebra generated by a single
element `α` which is congruent to an element of `B` modulo `m_B C`. Then `B → C` is an
isomorphism. -/
private theorem bijective_algebraMap_of_adjoin_eq_top {B C : Type u} [CommRing B] [IsLocalRing B]
    [CommRing C] [Nontrivial C] [Algebra B C] [Module.Finite B C] [Module.Free B C]
    {α : C} {b₀ : B} (hadj : Algebra.adjoin B {α} = ⊤)
    (hα : α - algebraMap B C b₀ ∈ (maximalIdeal B).map (algebraMap B C)) :
    Function.Bijective (algebraMap B C) := by
  set J := (maximalIdeal B).map (algebraMap B C)
  -- every element of `C` is congruent to an element of `B` modulo `J`
  have key : ∀ x : C, ∃ b : B, x - algebraMap B C b ∈ J := by
    intro x
    have hx : x ∈ Algebra.adjoin B ({α} : Set C) := by rw [hadj]; trivial
    induction hx using Algebra.adjoin_induction with
    | mem y hy =>
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact ⟨b₀, hα⟩
    | algebraMap b => exact ⟨b, by simp⟩
    | add y z hy hz ihy ihz =>
      obtain ⟨b, hb⟩ := ihy
      obtain ⟨c, hc⟩ := ihz
      refine ⟨b + c, ?_⟩
      have h : y + z - algebraMap B C (b + c)
          = (y - algebraMap B C b) + (z - algebraMap B C c) := by
        rw [map_add]; ring
      rw [h]
      exact Ideal.add_mem J hb hc
    | mul y z hy hz ihy ihz =>
      obtain ⟨b, hb⟩ := ihy
      obtain ⟨c, hc⟩ := ihz
      refine ⟨b * c, ?_⟩
      have h : y * z - algebraMap B C (b * c)
          = y * (z - algebraMap B C c) + algebraMap B C c * (y - algebraMap B C b) := by
        rw [map_mul]; ring
      rw [h]
      exact Ideal.add_mem J (Ideal.mul_mem_left J y hc) (Ideal.mul_mem_left J _ hb)
  -- Nakayama gives surjectivity
  have hsurj : Function.Surjective (algebraMap B C) := by
    have hfg : (⊤ : Submodule B C).FG := Module.Finite.iff_fg.mp inferInstance
    have hNN : (⊤ : Submodule B C) ≤ LinearMap.range (Algebra.linearMap B C)
        ⊔ (maximalIdeal B) • (⊤ : Submodule B C) := by
      intro x _
      obtain ⟨b, hb⟩ := key x
      have hmem : x - algebraMap B C b ∈ (maximalIdeal B) • (⊤ : Submodule B C) := by
        rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem]
        exact hb
      have h : x = algebraMap B C b + (x - algebraMap B C b) := by ring
      rw [h]
      exact Submodule.add_mem_sup ⟨b, rfl⟩ hmem
    have hnak := Submodule.sup_eq_sup_smul_of_le_smul_of_le_jacobson (J := ⊥) hfg
      (IsLocalRing.maximalIdeal_le_jacobson ⊥) hNN
    rw [Submodule.bot_smul, sup_bot_eq, sup_top_eq] at hnak
    intro x
    have : x ∈ LinearMap.range (Algebra.linearMap B C) := hnak ▸ Submodule.mem_top
    exact this
  refine ⟨?_, hsurj⟩
  -- freeness gives injectivity
  intro b b' hbb
  obtain ⟨i⟩ : Nonempty (Module.Free.ChooseBasisIndex B C) := by
    rw [← not_isEmpty_iff]
    intro hempty
    have : Subsingleton C := by
      have := (Module.Free.chooseBasis B C).repr
      exact Function.Injective.subsingleton (α := C) (β := _) this.injective
    exact (not_subsingleton C) this
  have hz : (b - b') • (Module.Free.chooseBasis B C) i = 0 := by
    rw [Algebra.smul_def, map_sub, hbb, sub_self, zero_mul]
  have h2 := congrArg (Module.Free.chooseBasis B C).repr hz
  rw [map_smul, (Module.Free.chooseBasis B C).repr_self, map_zero] at h2
  have h3 := congrArg (fun f : Module.Free.ChooseBasisIndex B C →₀ B ↦ f i) h2
  simp only [Finsupp.smul_apply, Finsupp.single_eq_same, Finsupp.coe_zero,
    Pi.zero_apply, smul_eq_mul, mul_one] at h3
  linear_combination h3

/-- **A local ring finite over a Henselian local ring is Henselian.**

This is the second half of [Stacks 04GH (1)](https://stacks.math.columbia.edu/tag/04GH):
given a monic `g` over `B` with a simple root over the residue field, the algebra `B[X]/(g)`
is finite over `R`, hence a product of local rings; the factor singled out by the root is free
of rank one over `B`, and the root lives in it. -/
@[stacks 04GH "(1)"]
theorem of_finite (R : Type u) [CommRing R] [HenselianLocalRing R]
    (B : Type u) [CommRing B] [IsLocalRing B] [Algebra R B] [Module.Finite R B] :
    HenselianLocalRing B := by
  refine { is_henselian := fun g hg a₀ ha₀ hunit ↦ ?_ }
  classical
  have hCfin : Module.Finite B (AdjoinRoot g) := hg.finite_adjoinRoot
  have hCfree : Module.Free B (AdjoinRoot g) := hg.free_adjoinRoot
  have hCfinR : Module.Finite R (AdjoinRoot g) := Module.Finite.trans B _
  -- the `κ(B)`-point of `AdjoinRoot g` determined by `a₀`
  have hev : g.eval₂ (IsLocalRing.residue B) (IsLocalRing.residue B a₀) = 0 := by
    rw [Polynomial.eval₂_at_apply, IsLocalRing.residue_eq_zero_iff]
    exact ha₀
  set χ : AdjoinRoot g →+* IsLocalRing.ResidueField B :=
    AdjoinRoot.lift (IsLocalRing.residue B) (IsLocalRing.residue B a₀) hev with hχdef
  -- decompose `AdjoinRoot g` into local factors over `R`
  obtain ⟨ι, hι, e, hidem, horth, -, hsum, hlocal⟩ :=
    isSumOfLocalIdempotents_aux R (AdjoinRoot g)
      (Module.finrank (R ⧸ maximalIdeal R) (idemSubmodule R (AdjoinRoot g) 1)) 1
      (by change (1 : AdjoinRoot g) * 1 = 1; ring) le_rfl
  obtain ⟨i₀, hi₀⟩ : ∃ i, χ (e i) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have h1 : χ 1 = 0 := by rw [← hsum, map_sum]; simp [hcon]
    rw [map_one] at h1
    exact one_ne_zero h1
  have hε : IsIdempotentElem (e i₀) := hidem i₀
  have hχε : χ (e i₀) = 1 :=
    (IsIdempotentElem.iff_eq_zero_or_one.mp (hε.map χ)).resolve_left hi₀
  -- the local factor cut out by `e i₀`
  have hC₁loc : IsLocalRing (AdjoinRoot g ⧸ Ideal.span {1 - e i₀}) := hlocal i₀
  have hC₁fin : Module.Finite B (AdjoinRoot g ⧸ Ideal.span {1 - e i₀}) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ B _).toLinearMap Ideal.Quotient.mk_surjective
  -- it is a direct factor of `AdjoinRoot g`, hence free over `B`
  have hC₁free : Module.Free B (AdjoinRoot g ⧸ Ideal.span {1 - e i₀}) := by
    have hsplit : AdjoinRoot g ≃ₐ[B]
        (AdjoinRoot g ⧸ Ideal.span {1 - e i₀}) × (AdjoinRoot g ⧸ Ideal.span {e i₀}) :=
      AlgEquiv.prodQuotientOfIsIdempotentElem B hε.one_sub hε (by ring)
        (by linear_combination -hε.eq)
    have hproj : Module.Projective B
        ((AdjoinRoot g ⧸ Ideal.span {1 - e i₀}) × (AdjoinRoot g ⧸ Ideal.span {e i₀})) :=
      Module.Projective.of_equiv' hsplit.toLinearEquiv
    have hprojC₁ : Module.Projective B (AdjoinRoot g ⧸ Ideal.span {1 - e i₀}) :=
      Module.Projective.of_split
        (LinearMap.inl B (AdjoinRoot g ⧸ Ideal.span {1 - e i₀})
          (AdjoinRoot g ⧸ Ideal.span {e i₀}))
        (LinearMap.fst B (AdjoinRoot g ⧸ Ideal.span {1 - e i₀})
          (AdjoinRoot g ⧸ Ideal.span {e i₀}))
        (LinearMap.ext fun x ↦ rfl)
    have : Module.Flat B (AdjoinRoot g ⧸ Ideal.span {1 - e i₀}) := Module.Flat.of_projective
    exact Module.free_of_flat_of_isLocalRing
  -- the root and its approximation
  set q : AdjoinRoot g →+* AdjoinRoot g ⧸ Ideal.span {1 - e i₀} := Ideal.Quotient.mk _
  set α := q (AdjoinRoot.root g) with hαdef
  set β := algebraMap B (AdjoinRoot g ⧸ Ideal.span {1 - e i₀}) a₀ with hβdef
  have hroot : Polynomial.aeval α g = 0 := by
    rw [Polynomial.aeval_def, hαdef,
      show algebraMap B (AdjoinRoot g ⧸ Ideal.span {1 - e i₀}) = q.comp (AdjoinRoot.of g) from rfl,
      ← Polynomial.hom_eval₂, AdjoinRoot.eval₂_root, map_zero]
  -- `α` generates
  have hadj : Algebra.adjoin B ({α} : Set (AdjoinRoot g ⧸ Ideal.span {1 - e i₀})) = ⊤ := by
    have h1 := Algebra.adjoin_image (R := B) (Ideal.Quotient.mkₐ B (Ideal.span {1 - e i₀}))
      ({AdjoinRoot.root g} : Set (AdjoinRoot g))
    rw [Set.image_singleton, AdjoinRoot.adjoinRoot_eq_top, Algebra.map_top] at h1
    rw [show α = (Ideal.Quotient.mkₐ B (Ideal.span {1 - e i₀})) (AdjoinRoot.root g) from rfl, h1,
      AlgHom.range_eq_top]
    exact Ideal.Quotient.mk_surjective
  -- `χ` descends to the local factor and identifies its residue field with `κ(B)`
  have hkerle : ∀ x ∈ Ideal.span {1 - e i₀}, χ x = 0 := by
    intro x hx
    obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.mp hx
    rw [map_mul, map_sub, map_one, hχε, sub_self, mul_zero]
  set χ₁ : (AdjoinRoot g ⧸ Ideal.span {1 - e i₀}) →+* IsLocalRing.ResidueField B :=
    Ideal.Quotient.lift _ χ hkerle
  have hχ₁q : ∀ x, χ₁ (q x) = χ x := fun x ↦ rfl
  have hsurjχ₁ : Function.Surjective χ₁ := by
    intro y
    obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective y
    refine ⟨algebraMap B _ b, ?_⟩
    rw [show algebraMap B (AdjoinRoot g ⧸ Ideal.span {1 - e i₀}) b = q (AdjoinRoot.of g b) from rfl,
      hχ₁q, hχdef, AdjoinRoot.lift_of]
  have hker : RingHom.ker χ₁ = maximalIdeal (AdjoinRoot g ⧸ Ideal.span {1 - e i₀}) :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective χ₁ hsurjχ₁)
  have hαβmax : α - β ∈ maximalIdeal (AdjoinRoot g ⧸ Ideal.span {1 - e i₀}) := by
    rw [← hker, RingHom.mem_ker, map_sub, hαdef, hβdef,
      show algebraMap B (AdjoinRoot g ⧸ Ideal.span {1 - e i₀}) a₀ = q (AdjoinRoot.of g a₀) from rfl,
      hχ₁q, hχ₁q, hχdef, AdjoinRoot.lift_root, AdjoinRoot.lift_of, sub_self]
  -- Newton's estimate: `α - β` lies in `m_B` times the local factor
  have hαβ : α - β ∈ (maximalIdeal B).map
      (algebraMap B (AdjoinRoot g ⧸ Ideal.span {1 - e i₀})) := by
    obtain ⟨c, hc⟩ := Polynomial.exists_mul_sq_add_linear_part_eq_eval_add
      (g.map (algebraMap B (AdjoinRoot g ⧸ Ideal.span {1 - e i₀}))) β (α - β)
    have hGα : (g.map (algebraMap B (AdjoinRoot g ⧸ Ideal.span {1 - e i₀}))).eval α = 0 := by
      rw [Polynomial.eval_map, ← Polynomial.aeval_def]
      exact hroot
    have hGβ : (g.map (algebraMap B (AdjoinRoot g ⧸ Ideal.span {1 - e i₀}))).eval β
        = algebraMap B (AdjoinRoot g ⧸ Ideal.span {1 - e i₀}) (g.eval a₀) := by
      rw [Polynomial.eval_map, hβdef, Polynomial.eval₂_at_apply]
    have hGd : (g.map (algebraMap B (AdjoinRoot g ⧸ Ideal.span {1 - e i₀}))).derivative.eval β
        = algebraMap B (AdjoinRoot g ⧸ Ideal.span {1 - e i₀}) (g.derivative.eval a₀) := by
      rw [Polynomial.derivative_map, Polynomial.eval_map, hβdef, Polynomial.eval₂_at_apply]
    rw [show β + (α - β) = α from by ring, hGα, hGβ, hGd] at hc
    have hunit' : IsUnit (algebraMap B (AdjoinRoot g ⧸ Ideal.span {1 - e i₀})
        (g.derivative.eval a₀) + c * (α - β)) := by
      rw [← IsLocalRing.notMem_maximalIdeal]
      intro hmem
      have h2 : algebraMap B (AdjoinRoot g ⧸ Ideal.span {1 - e i₀}) (g.derivative.eval a₀)
          ∈ maximalIdeal (AdjoinRoot g ⧸ Ideal.span {1 - e i₀}) := by
        have h3 := Ideal.sub_mem _ hmem (Ideal.mul_mem_left _ c hαβmax)
        simpa using h3
      exact (IsLocalRing.mem_maximalIdeal _).mp h2 (hunit.map _)
    obtain ⟨w, hw⟩ := hunit'.exists_right_inv
    have hkey : α - β = (-algebraMap B (AdjoinRoot g ⧸ Ideal.span {1 - e i₀}) (g.eval a₀)) * w := by
      calc α - β = (α - β) * ((algebraMap B _ (g.derivative.eval a₀) + c * (α - β)) * w) := by
            rw [hw, mul_one]
        _ = ((α - β) * (algebraMap B _ (g.derivative.eval a₀) + c * (α - β))) * w := by ring
        _ = (-algebraMap B _ (g.eval a₀)) * w := by rw [show (α - β) *
              (algebraMap B _ (g.derivative.eval a₀) + c * (α - β))
              = -algebraMap B _ (g.eval a₀) from by linear_combination hc]
    rw [hkey]
    exact Ideal.mul_mem_right _ _ (neg_mem (Ideal.mem_map_of_mem _ ha₀))
  -- so `B` is the local factor, and the root of `g` lives in `B`
  have hbij := bijective_algebraMap_of_adjoin_eq_top hadj hαβ
  obtain ⟨a, ha⟩ := hbij.surjective α
  refine ⟨a, ?_, ?_⟩
  · refine hbij.injective ?_
    rw [map_zero, ← Polynomial.eval₂_at_apply (f := algebraMap B _), ha,
      ← Polynomial.aeval_def, hroot]
  · by_contra hcon
    have hu : IsUnit (a - a₀) := IsLocalRing.notMem_maximalIdeal.mp hcon
    have hu' : IsUnit (α - β) := by
      rw [← ha, hβdef, ← map_sub]
      exact hu.map _
    exact (IsLocalRing.mem_maximalIdeal _).mp hαβmax hu'

end Local

section Pi

variable (R : Type u) [CommRing R] [HenselianLocalRing R]
variable (S : Type u) [CommRing S] [Algebra R S] [Module.Finite R S]

/-- **A finite algebra over a Henselian local ring is a finite product of Henselian local
rings**, each finite over the base.

[Stacks 04GH (1)](https://stacks.math.columbia.edu/tag/04GH). -/
@[stacks 04GH "(1)"]
theorem exists_pi_of_finite :
    ∃ (ι : Type u) (_ : Fintype ι) (B : ι → Type u) (_ : ∀ i, CommRing (B i))
      (_ : ∀ i, IsLocalRing (B i)) (_ : ∀ i, HenselianLocalRing (B i))
      (_ : ∀ i, Algebra R (B i)) (_ : ∀ i, Module.Finite R (B i)),
        Nonempty (S ≃ₐ[R] (Π i, B i)) := by
  obtain ⟨ι, hι, B, hcomm, hloc, halg, hfin, he⟩ := exists_pi_isLocalRing_of_finite R S
  refine ⟨ι, hι, B, hcomm, hloc, fun i ↦ ?_, halg, hfin, he⟩
  let _ := hcomm i
  let _ := hloc i
  let _ := halg i
  let _ := hfin i
  exact of_finite R (B i)

/-- **A finite algebra over a strictly Henselian local ring is a finite product of strictly
Henselian local rings**: in addition to `HenselianLocalRing.exists_pi_of_finite`, the residue
field of every factor is separably closed.

[Stacks 04GH (1)](https://stacks.math.columbia.edu/tag/04GH). -/
@[stacks 04GH "(1)"]
theorem exists_pi_of_finite_of_isSepClosed [IsSepClosed (IsLocalRing.ResidueField R)] :
    ∃ (ι : Type u) (_ : Fintype ι) (B : ι → Type u) (_ : ∀ i, CommRing (B i))
      (_ : ∀ i, IsLocalRing (B i)) (_ : ∀ i, HenselianLocalRing (B i))
      (_ : ∀ i, Algebra R (B i)) (_ : ∀ i, Module.Finite R (B i))
      (_ : ∀ i, IsSepClosed (IsLocalRing.ResidueField (B i))),
        Nonempty (S ≃ₐ[R] (Π i, B i)) := by
  obtain ⟨ι, hι, B, hcomm, hloc, hhens, halg, hfin, he⟩ := exists_pi_of_finite R S
  refine ⟨ι, hι, B, hcomm, hloc, hhens, halg, hfin, fun i ↦ ?_, he⟩
  let _ := hcomm i
  let _ := hloc i
  let _ := halg i
  let _ := hfin i
  exact IsLocalRing.isSepClosed_residueField_of_finite R (B i)

end Pi

end HenselianLocalRing
