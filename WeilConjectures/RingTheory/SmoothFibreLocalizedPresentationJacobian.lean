/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import WeilConjectures.AlgebraicGeometry.RelativeGlobalCompleteIntersectionPresentation
public import WeilConjectures.RingTheory.SingularIdeal
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RingTheory.Localization.BaseChange
import WeilConjectures.AlgebraicGeometry.RelativeGlobalCompleteIntersectionBaseChange
import WeilConjectures.RingTheory.RelativeGlobalCompleteIntersectionSmoothJacobian

/-!
# A Jacobian minor from a smooth fibre of a localized presentation

If the fibre of `R → S` at a prime `q` of `S` is smooth, then for any relative global complete
intersection presentation of a principal neighbourhood `S_g` of `q`, some maximal Jacobian minor
avoids the prime corresponding to `q`.

## References

* [Stacks, Tag 00TF]
* [Stacks, Tag 00TE]
-/

@[expose] public section

universe u v

namespace Algebra

/-- Transport a smooth principal neighbourhood along an algebra equivalence. -/
private theorem smoothAt_comap_equiv {R A B : Type*}
    [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (e : A ≃ₐ[R] B) (q : PrimeSpectrum B) (h : IsSmoothAtPrime R q) :
    IsSmoothAtPrime R (PrimeSpectrum.comap e.toRingHom q) := by
  obtain ⟨b, hb, hsm⟩ := h
  have := hsm
  refine ⟨e.symm b, ?_, ?_⟩
  · simpa using hb
  · exact Smooth.of_equiv
      (IsLocalization.algEquivOfAlgEquiv (M := .powers b) (T := .powers (e.symm b))
        (Localization.Away b) (Localization.Away (e.symm b)) e.symm
        (Submonoid.map_powers e.symm b))

/-- A principal localization preserves smoothness at a prime above the given prime. -/
private theorem smoothAt_away {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (g : A) (q : PrimeSpectrum (Localization.Away g))
    (h : IsSmoothAtPrime R (PrimeSpectrum.comap (algebraMap A (Localization.Away g)) q)) :
    IsSmoothAtPrime R q := by
  obtain ⟨h, hh, hsm⟩ := h
  have := hsm
  let Ag := Localization.Away g
  let Ah := Localization.Away h
  let Agh := Localization.Away (algebraMap A Ag h)
  let Ahg := Localization.Away (algebraMap A Ah g)
  have : Smooth Ah Ahg := Smooth.of_isLocalization_Away (algebraMap A Ah g)
  have : Smooth R Ahg := Smooth.comp R Ah Ahg
  have : IsLocalization.Away (g * h) Agh := inferInstance
  have : IsLocalization.Away (g * h) Ahg := inferInstance
  refine ⟨algebraMap A Ag h, hh, ?_⟩
  exact Smooth.of_equiv
    ((IsLocalization.algEquiv (.powers (g * h)) Ahg Agh).restrictScalars R)

/-- A smooth fibre at a prime supplies a maximal Jacobian minor of any relative global
complete intersection presentation of a principal neighbourhood, avoiding the lifted prime. -/
theorem exists_jacobian_minor_of_smooth_fibre_localizedPresentation
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (q : PrimeSpectrum S) (g : S)
    (qg : PrimeSpectrum (Localization.Away g))
    (hqg : PrimeSpectrum.comap (algebraMap S (Localization.Away g)) qg = q)
    (n c : ℕ) (f : Fin c → MvPolynomial (Fin n) R)
    (hci : IsRelativeGlobalCompleteIntersectionPresentation f)
    (e : Localization.Away g ≃ₐ[R]
      (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)))
    (hsmooth : IsSmoothAtPrime (q.comap (algebraMap R S)).asIdeal.ResidueField
      (PrimeSpectrum.preimageEquivFiber R S (q.comap (algebraMap R S)) ⟨q, rfl⟩)) :
    ∃ i : Fin c → Fin n, StrictMono i ∧
      Ideal.Quotient.mk (Ideal.span (Set.range f))
        (Matrix.det (fun j k : Fin c ↦ MvPolynomial.pderiv (i k) (f j))) ∉
          (PrimeSpectrum.comap e.symm.toRingHom qg).asIdeal := by
  let p := q.comap (algebraMap R S)
  let k := p.asIdeal.ResidueField
  let T := MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)
  let fbar : Fin c → MvPolynomial (Fin n) k :=
    fun j ↦ MvPolynomial.map (algebraMap R k) (f j)
  let Tbar := MvPolynomial (Fin n) k ⧸ Ideal.span (Set.range fbar)
  obtain ⟨⟨ebar, hX⟩, hbase⟩ :=
    relativeGlobalCompleteIntersection_baseChange R k n c f
  have hciBar : IsRelativeGlobalCompleteIntersectionPresentation fbar := hbase hci
  let Q := PrimeSpectrum.preimageEquivFiber R S p ⟨q, rfl⟩
  let gbar : p.asIdeal.Fiber S := _root_.TensorProduct.tmul R (1 : k) g
  have hQ : PrimeSpectrum.comap
      (TensorProduct.includeRight : S →ₐ[R] p.asIdeal.Fiber S).toRingHom Q = q := by
    exact congrArg Subtype.val ((PrimeSpectrum.preimageEquivFiber R S p).symm_apply_apply
      ⟨q, rfl⟩)
  have hg : g ∉ q.asIdeal := by
    intro hg
    have hg' : algebraMap S (Localization.Away g) g ∈ qg.asIdeal := by
      change g ∈ (PrimeSpectrum.comap (algebraMap S (Localization.Away g)) qg).asIdeal
      rwa [hqg]
    exact qg.isPrime.ne_top (qg.asIdeal.eq_top_of_isUnit_mem hg'
      (IsLocalization.Away.algebraMap_isUnit g))
  have hgbar : gbar ∉ Q.asIdeal := by
    change g ∉ (PrimeSpectrum.comap
      (TensorProduct.includeRight : S →ₐ[R] p.asIdeal.Fiber S).toRingHom Q).asIdeal
    rwa [hQ]
  have hQrange : Q ∈ Set.range (PrimeSpectrum.comap
      (algebraMap (p.asIdeal.Fiber S) (Localization.Away gbar))) := by
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away gbar) gbar]
    exact hgbar
  obtain ⟨Qg, hQg⟩ := hQrange
  have hsmg : IsSmoothAtPrime k Qg := smoothAt_away gbar Qg (by rwa [hQg])
  let etensor := TensorProduct.congr (AlgEquiv.refl : k ≃ₐ[k] k) e
  let eloc := IsLocalization.Away.tensorProductEquivTMulRight R k g (Localization.Away g)
  let E : Tbar ≃ₐ[k] Localization.Away gbar := (ebar.trans etensor.symm).trans eloc
  let Qbar := PrimeSpectrum.comap E.toRingHom Qg
  have hsmbar : IsSmoothAtPrime k Qbar := smoothAt_comap_equiv E Qg hsmg
  obtain ⟨i, hi, hminor⟩ :=
    (isSmoothAtPrime_iff_exists_jacobian_minor k n c fbar hciBar Qbar).mp hsmbar
  refine ⟨i, hi, ?_⟩
  have hpoly (a : MvPolynomial (Fin n) R) :
      ebar (Ideal.Quotient.mk (Ideal.span (Set.range fbar))
        (MvPolynomial.map (algebraMap R k) a)) =
      _root_.TensorProduct.tmul R (1 : k)
        (Ideal.Quotient.mk (Ideal.span (Set.range f)) a) := by
    let L : MvPolynomial (Fin n) R →ₐ[R] _root_.TensorProduct R k T :=
      (ebar.toAlgHom.restrictScalars R).comp
        ((Ideal.Quotient.mkₐ R (Ideal.span (Set.range fbar))).comp
          (MvPolynomial.mapAlgHom (Algebra.ofId R k)))
    let H : MvPolynomial (Fin n) R →ₐ[R] _root_.TensorProduct R k T :=
      TensorProduct.includeRight.comp (Ideal.Quotient.mkₐ R (Ideal.span (Set.range f)))
    have heq : L = H := by
      apply MvPolynomial.algHom_ext
      intro j
      change ebar (Ideal.Quotient.mk (Ideal.span (Set.range fbar))
        (MvPolynomial.mapAlgHom (Algebra.ofId R k) (MvPolynomial.X j))) =
        _root_.TensorProduct.tmul R (1 : k)
          (Ideal.Quotient.mk (Ideal.span (Set.range f)) (MvPolynomial.X j))
      rw [MvPolynomial.mapAlgHom_apply, MvPolynomial.map_X]
      exact hX j
    exact DFunLike.congr_fun heq a
  let Qc := PrimeSpectrum.comap eloc.toRingHom Qg
  let qc := PrimeSpectrum.comap
    (TensorProduct.includeRight : Localization.Away g →ₐ[R]
      _root_.TensorProduct R k (Localization.Away g)).toRingHom Qc
  have hqc : qc = qg := by
    apply PrimeSpectrum.localization_comap_injective (Localization.Away g) (.powers g)
    rw [hqg]
    ext s
    change eloc (_root_.TensorProduct.tmul R (1 : k)
      (algebraMap S (Localization.Away g) s)) ∈ Qg.asIdeal ↔ s ∈ q.asIdeal
    rw [IsLocalization.Away.tensorProductEquivTMulRight_tmul]
    change _root_.TensorProduct.tmul R (1 : k) s ∈
      (PrimeSpectrum.comap
        (algebraMap (p.asIdeal.Fiber S) (Localization.Away gbar)) Qg).asIdeal ↔ _
    rw [hQg]
    change s ∈ (PrimeSpectrum.comap
      (TensorProduct.includeRight : S →ₐ[R] p.asIdeal.Fiber S).toRingHom Q).asIdeal ↔ _
    rw [hQ]
  have hmem (a : MvPolynomial (Fin n) R) :
      Ideal.Quotient.mk (Ideal.span (Set.range fbar))
        (MvPolynomial.map (algebraMap R k) a) ∈ Qbar.asIdeal ↔
      Ideal.Quotient.mk (Ideal.span (Set.range f)) a ∈
        (PrimeSpectrum.comap e.symm.toRingHom qg).asIdeal := by
    change eloc (etensor.symm (ebar
      (Ideal.Quotient.mk (Ideal.span (Set.range fbar))
        (MvPolynomial.map (algebraMap R k) a)))) ∈ Qg.asIdeal ↔ _
    rw [hpoly]
    simp only [etensor, TensorProduct.congr_symm_apply, TensorProduct.map_tmul]
    change e.symm (Ideal.Quotient.mk (Ideal.span (Set.range f)) a) ∈ qc.asIdeal ↔ _
    rw [hqc]
    rfl
  have hdet :
      MvPolynomial.map (algebraMap R k)
        (Matrix.det (fun j l : Fin c ↦ MvPolynomial.pderiv (i l) (f j))) =
      Matrix.det (fun j l : Fin c ↦ MvPolynomial.pderiv (i l) (fbar j)) := by
    rw [RingHom.map_det]
    simp only [fbar, MvPolynomial.pderiv_map]
    rfl
  intro h
  exact hminor (hdet ▸ (hmem _).mpr h)

end Algebra
