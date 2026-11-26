/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.RingHom.Flat
public import WeilConjectures.RingTheory.CompleteIntersectionOverField
public import WeilConjectures.AlgebraicGeometry.RelativeGlobalCompleteIntersectionPresentation
import WeilConjectures.RingTheory.EquationCountLocalizeRelativeGlobalCompleteIntersection
import WeilConjectures.RingTheory.RelativeGlobalCompleteIntersectionPrincipalLocalization
import WeilConjectures.RingTheory.SyntomicPrincipalLocalizationHypotheses
import WeilConjectures.RingTheory.SyntomicEquationCountComparison
public import Mathlib.RingTheory.Flat.Localization

/-!
# Syntomic at a prime: a relative global complete intersection neighbourhood

If `R → S` is finitely presented near a prime `q` of `S`, flat on the local rings at `q`, and has
a global complete intersection fibre near the fibre prime of `q`, then some principal localization
`S_g` with `g ∉ q` is a relative global complete intersection over `R`.

## Implementation details

The algebra structure represents the arbitrary ring map. The fibre is Mathlib's `κ(p) ⊗[R] S`,
identified by tensor symmetry with `S ⊗[R] κ(p)`. `PrimeSpectrum.preimageEquivFiber` constructs
precisely the kernel of the natural map from this fibre to `κ(q)`.

The proof first reduces to `S` finitely presented by a principal localization. It then chooses a
presentation `S = R[x_1, …, x_n] / I` and elements `f_1, …, f_c ∈ I` whose images generate the
localized conormal module of the fibre, compares `S` with `S' = R[x_1, …, x_n] / (f_1, …, f_c)`
near `q` using flatness and Nakayama's lemma, and finally localizes `S'` to a relative global
complete intersection.

## References

* [Stacks, Tag 00SY], implication (3) ⇒ (2)
* [Stacks, Tag 00SG]
-/

@[expose] public section

universe u v

namespace Algebra

private noncomputable def awayEquiv {R A B : Type*}
    [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (e : A ≃ₐ[R] B) (a : A) :
    Localization.Away a ≃ₐ[R] Localization.Away (e a) :=
  IsLocalization.algEquivOfAlgEquiv (M := Submonoid.powers a)
    (T := Submonoid.powers (e a)) _ _ e (by simp)

private noncomputable def doubleAwayEquiv {R A : Type*}
    [CommRing R] [CommRing A] [Algebra R A] (x y : A) :
    Localization.Away (algebraMap A (Localization.Away x) y) ≃ₐ[R]
      Localization.Away (x * y) :=
  (IsLocalization.algEquiv (Submonoid.powers (x * y)) _ _).restrictScalars R

private theorem presentation_away {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (hA : IsRelativeGlobalCompleteIntersection (algebraMap R A)) (a : A) :
    ∃ (n c : ℕ) (f : Fin c → MvPolynomial (Fin n) R),
      IsRelativeGlobalCompleteIntersectionPresentation f ∧
      Nonempty (Localization.Away a ≃ₐ[R]
        (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))) := by
  rw [IsRelativeGlobalCompleteIntersection, toAlgebra_algebraMap] at hA
  obtain ⟨n, c, f, e, hf⟩ := hA
  have hpres : IsRelativeGlobalCompleteIntersectionPresentation f := by
    intro p hp
    exact hf p hp
  obtain ⟨h, hh⟩ := Ideal.Quotient.mk_surjective (e.symm a)
  obtain ⟨hrel, e', _⟩ :=
    relativeGlobalCompleteIntersection_principalLocalization R n c f hpres h
  refine ⟨n + 1, c + 1, _, hrel, ⟨?_⟩⟩
  have he : e (Ideal.Quotient.mk _ h) = a := by rw [hh, e.apply_symm_apply]
  exact (he ▸ awayEquiv e (Ideal.Quotient.mk _ h)).symm.trans e'.symm

private theorem presentation_of_comparison {R S : Type*}
    [CommRing R] [CommRing S] [Algebra R S] (q : PrimeSpectrum S)
    (hfp : FinitePresentation R S)
    (hflat : (Localization.localRingHom (q.asIdeal.comap (algebraMap R S)) q.asIdeal
      (algebraMap R S) rfl).Flat)
    (hci : ∃ h : (q.asIdeal.comap (algebraMap R S)).Fiber S,
      h ∉ (PrimeSpectrum.preimageEquivFiber R S (q.comap (algebraMap R S))
        ⟨q, rfl⟩).asIdeal ∧
      IsGlobalCompleteIntersection (q.asIdeal.comap (algebraMap R S)).ResidueField
        (Localization.Away h)) :
    ∃ (g : S), g ∉ q.asIdeal ∧
      ∃ (n c : ℕ) (f : Fin c → MvPolynomial (Fin n) R),
        IsRelativeGlobalCompleteIntersectionPresentation f ∧
        Nonempty (Localization.Away g ≃ₐ[R]
          (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))) := by
  obtain ⟨n, c, f, π, u, _, hu, hbij, hc, hdim⟩ :=
    exists_equationCount_comparison_of_syntomicAtPrime q hfp hflat hci
  let T := MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)
  let qT := q.comap π.toRingHom
  obtain ⟨h, hg, hrel, _, e₁, _⟩ :=
    exists_localization_relativeGlobalCompleteIntersection R n c f qT ⟨hc, hdim⟩
  let g : T := Ideal.Quotient.mk _ h
  let a := e₁.symm (algebraMap T (Localization.Away g) u)
  obtain ⟨N, C, F, hF, ⟨eF⟩⟩ := presentation_away hrel a
  let e := AlgEquiv.ofBijective
    (IsLocalization.Away.mapₐ (Localization.Away u) (Localization.Away (π u)) π u) hbij
  have he : e (algebraMap T (Localization.Away u) g) =
      algebraMap S (Localization.Away (π u)) (π g) := by
    change IsLocalization.map (M := Submonoid.powers u) (T := Submonoid.powers (π u))
      (Localization.Away (π u)) π.toRingHom
      (by
        apply Submonoid.powers_le.mpr
        change π u ∈ Submonoid.powers (π u)
        exact Submonoid.mem_powers _)
      (algebraMap T (Localization.Away u) g) = _
    exact IsLocalization.map_eq _ g
  let e₂ := awayEquiv e (algebraMap T (Localization.Away u) g)
  let e₃ : Localization.Away (algebraMap T (Localization.Away g) u) ≃ₐ[R]
      Localization.Away (algebraMap T (Localization.Away u) g) :=
    (doubleAwayEquiv g u).trans
      ((mul_comm g u) ▸ (doubleAwayEquiv u g).symm)
  let e₄ := doubleAwayEquiv (R := R) (π u) (π g)
  let e₅ := awayEquiv e₁ a
  have ha : e₁ a = algebraMap T (Localization.Away g) u := e₁.apply_symm_apply _
  have hpg : π g ∉ q.asIdeal := hg
  refine ⟨π u * π g, q.asIdeal.primeCompl.mul_mem hu hpg, N, C, F, hF, ⟨?_⟩⟩
  exact e₄.symm.trans (((he ▸ e₂).symm).trans
    (e₃.symm.trans ((ha ▸ e₅).symm.trans eF)))

private theorem flat_away_atPrime {R S : Type*}
    [CommRing R] [CommRing S] [Algebra R S] (q : PrimeSpectrum S)
    (g : S) (q₁ : PrimeSpectrum (Localization.Away g))
    (hq : q₁.comap (algebraMap S (Localization.Away g)) = q)
    (hflat : (Localization.localRingHom (q.asIdeal.comap (algebraMap R S)) q.asIdeal
      (algebraMap R S) rfl).Flat) :
    (Localization.localRingHom
      (q₁.asIdeal.comap (algebraMap R (Localization.Away g))) q₁.asIdeal
      (algebraMap R (Localization.Away g)) rfl).Flat := by
  subst q
  have hf : (algebraMap S (Localization.Away g)).Flat :=
    RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat _ (Submonoid.powers g))
  have hf₁ := hf.localRingHom q₁.asIdeal
    (q₁.asIdeal.comap (algebraMap S (Localization.Away g))) rfl
  have hc := hflat.comp hf₁
  dsimp only [PrimeSpectrum.comap] at hc
  rw [← Localization.localRingHom_comp
    ((q₁.asIdeal.comap (algebraMap S (Localization.Away g))).comap (algebraMap R S))
    (q₁.asIdeal.comap (algebraMap S (Localization.Away g))) q₁.asIdeal
    (algebraMap R S) rfl (algebraMap S (Localization.Away g)) rfl] at hc
  simp only [Ideal.comap_comap] at hc
  let property (f : R →+* Localization.Away g) : Prop :=
    (Localization.localRingHom (q₁.asIdeal.comap f) q₁.asIdeal f rfl).Flat
  have hc' : property ((algebraMap S (Localization.Away g)).comp (algebraMap R S)) := hc
  have heq := congrArg property (IsScalarTower.algebraMap_eq R S (Localization.Away g))
  exact heq.symm.mp hc'

private theorem descend_presentation_away {R S : Type*}
    [CommRing R] [CommRing S] [Algebra R S] (q : PrimeSpectrum S)
    (g : S) (hg : g ∉ q.asIdeal)
    (q₁ : PrimeSpectrum (Localization.Away g))
    (hq : q₁.comap (algebraMap S (Localization.Away g)) = q)
    (a : Localization.Away g) (ha : a ∉ q₁.asIdeal)
    {n c : ℕ} (f : Fin c → MvPolynomial (Fin n) R)
    (e : Localization.Away a ≃ₐ[R]
      (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))) :
    ∃ s : S, s ∉ q.asIdeal ∧
      Nonempty (Localization.Away s ≃ₐ[R]
        (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))) := by
  let s := (IsLocalization.Away.sec g a).1
  have hassoc : Associated (algebraMap S (Localization.Away g) s) a :=
    IsLocalization.Away.associated_sec_fst g a
  have hs : s ∉ q.asIdeal := by
    intro hs
    have hs' : algebraMap S (Localization.Away g) s ∈ q₁.asIdeal := by
      change s ∈ (q₁.comap (algebraMap S (Localization.Away g))).asIdeal
      rwa [hq]
    exact ha ((q₁.asIdeal.mem_iff_of_associated hassoc).mp hs')
  have : IsLocalization.Away (g * s) (Localization.Away a) :=
    IsLocalization.Away.mul_of_associated g s a hassoc
  refine ⟨g * s, q.asIdeal.primeCompl.mul_mem hg hs, ⟨?_⟩⟩
  exact ((IsLocalization.algEquiv (Submonoid.powers (g * s))
    (Localization.Away (g * s)) (Localization.Away a)).restrictScalars R).trans e

/-- A ring map finitely presented near a prime, flat on the induced local rings, and with
complete-intersection fibre near the canonical fibre prime admits a relative global complete
intersection presentation after a principal localization outside the prime. -/
theorem exists_relativeGlobalCompleteIntersection_of_syntomicAtPrime
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (q : PrimeSpectrum S)
    (hfp : ∃ g : S, g ∉ q.asIdeal ∧ FinitePresentation R (Localization.Away g))
    (hflat : (Localization.localRingHom (q.asIdeal.comap (algebraMap R S)) q.asIdeal
      (algebraMap R S) rfl).Flat)
    (hci : ∃ h : (q.asIdeal.comap (algebraMap R S)).Fiber S,
      h ∉ (PrimeSpectrum.preimageEquivFiber R S (q.comap (algebraMap R S))
        ⟨q, rfl⟩).asIdeal ∧
      IsGlobalCompleteIntersection (q.asIdeal.comap (algebraMap R S)).ResidueField
        (Localization.Away h)) :
    ∃ (g' : S), g' ∉ q.asIdeal ∧
      ∃ (n c : ℕ) (f : Fin c → MvPolynomial (Fin n) R),
        IsRelativeGlobalCompleteIntersectionPresentation f ∧
        Nonempty (Localization.Away g' ≃ₐ[R]
          (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))) := by
  obtain ⟨g, hg, hfg⟩ := hfp
  obtain ⟨q₁, hq, hci₁⟩ := exists_completeIntersection_fibre_away q g hg hci
  have hflat₁ := flat_away_atPrime q g q₁ hq hflat
  obtain ⟨a, ha, n, c, f, hf, ⟨e⟩⟩ :=
    presentation_of_comparison q₁ hfg hflat₁ hci₁
  obtain ⟨s, hs, he⟩ := descend_presentation_away q g hg q₁ hq a ha f e
  exact ⟨s, hs, n, c, f, hf, he⟩

end Algebra
