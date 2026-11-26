/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GRing
public import WeilConjectures.RingTheory.PopescuResolution
public import WeilConjectures.RingTheory.EssentiallySmooth
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Artinian.Defs
import WeilConjectures.RingTheory.PopescuCoefficientRescaling
import WeilConjectures.RingTheory.PolynomialParameterQuotientChart

/-!
# Rescaling data before polynomial coefficient base change

We perform the simultaneous rescaling of the parameters in the proof of Stacks Lemma 07FJ,
retaining the coefficient quotient and its polynomial identification, before giving the
polynomial ring over `D'` its algebra structures.

## Implementation details

`exists_popescu_rescaling_data` supplies no algebra structure on `D'[t_i]` over `R/H^n` and
asserts no essential smoothness for that polynomial ring. The coefficient ring is shrunk to
`Type (max u v)` by presenting its smooth finite-presentation model and its localization over
the small ring `P/p₀^n`. The case `d = 0` is included.

## References

* [Stacks, Tag 07FJ] (steps 10--13 and 15 of the proof, and the coefficient quotient of step 25)
-/

@[expose] public section

set_option autoImplicit false

universe u v w
namespace Algebra

/-- Simultaneous rescaling, retaining the coefficient quotient and its polynomial
identification, before giving the polynomial ring over D' its algebra structures. -/
theorem exists_popescu_rescaling_data
    {k : Type u} {A : Type v} {Λ : Type w}
    [Field k] [CommRing A] [CommRing Λ] [Algebra k A] [Algebra k Λ]
    [FinitePresentation k A] [IsNoetherianRing Λ]
    (p : ℕ) [CharP k p] (hp : 0 < p)
    (α : A →ₐ[k] Λ) (q : PrimeSpectrum Λ)
    (hreg : IsGeometricallyRegular k Λ)
    (N : ℕ) (hN : 0 < N)
    (hpower : IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal) ^ N ≤
      (Ideal.map α.toRingHom (singularIdeal k A)).map
        (algebraMap Λ (Localization.AtPrime q.asIdeal)))
    (d : ℕ) (hd : d =
      (IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal)).spanFinrank)
    (s : ℕ) (a : Fin s → A) (ha : Ideal.span (Set.range a) = singularIdeal k A)
    (c : ℕ) (hc : 0 < c)
    (r : ℕ) (f : MvPolynomial (Fin r) k →ₐ[k] A) (hf : Function.Surjective f)
    (m₀ : ℕ) (φ₀ : MvPolynomial (Fin m₀) k →ₐ[k] Λ)
    (ψ₀ : Localization.AtPrime (q.asIdeal.comap φ₀.toRingHom) →+*
      Localization.AtPrime q.asIdeal)
    (hψ₀ : ψ₀.comp (algebraMap (MvPolynomial (Fin m₀) k)
        (Localization.AtPrime (q.asIdeal.comap φ₀.toRingHom))) =
      (algebraMap Λ (Localization.AtPrime q.asIdeal)).comp φ₀.toRingHom)
    (hideal₀ : q.asIdeal.map (algebraMap Λ (Localization.AtPrime q.asIdeal)) =
      (q.asIdeal.comap φ₀.toRingHom).map
        ((algebraMap Λ (Localization.AtPrime q.asIdeal)).comp φ₀.toRingHom))
    (hflat₀ : ψ₀.Flat)
    (D₀ : Type (max u w)) [CommRing D₀] [IsLocalRing D₀] [IsArtinianRing D₀]
    [Algebra (Localization.AtPrime (q.asIdeal.comap φ₀.toRingHom) ⧸
      ((q.asIdeal.comap φ₀.toRingHom).map (algebraMap (MvPolynomial (Fin m₀) k)
        (Localization.AtPrime (q.asIdeal.comap φ₀.toRingHom)))) ^ (N + d * (8 * c))) D₀]
    (g₀ : D₀ →+* Localization.AtPrime q.asIdeal ⧸
      (q.asIdeal.map (algebraMap Λ (Localization.AtPrime q.asIdeal))) ^
        (N + d * (8 * c)))
    [IsLocalHom (algebraMap (Localization.AtPrime (q.asIdeal.comap φ₀.toRingHom) ⧸
      ((q.asIdeal.comap φ₀.toRingHom).map (algebraMap (MvPolynomial (Fin m₀) k)
        (Localization.AtPrime (q.asIdeal.comap φ₀.toRingHom)))) ^
          (N + d * (8 * c))) D₀)]
    [IsLocalHom g₀]
    (hsmooth₀ : EssentiallySmooth
      (Localization.AtPrime (q.asIdeal.comap φ₀.toRingHom) ⧸
        ((q.asIdeal.comap φ₀.toRingHom).map (algebraMap (MvPolynomial (Fin m₀) k)
          (Localization.AtPrime (q.asIdeal.comap φ₀.toRingHom)))) ^
            (N + d * (8 * c))) D₀)
    (hgflat₀ : g₀.Flat)
    (hfactor₀ : (g₀.comp (algebraMap
      (Localization.AtPrime (q.asIdeal.comap φ₀.toRingHom) ⧸
        ((q.asIdeal.comap φ₀.toRingHom).map (algebraMap (MvPolynomial (Fin m₀) k)
          (Localization.AtPrime (q.asIdeal.comap φ₀.toRingHom)))) ^
            (N + d * (8 * c))) D₀)).comp
      (Ideal.Quotient.mk (((q.asIdeal.comap φ₀.toRingHom).map
        (algebraMap (MvPolynomial (Fin m₀) k)
          (Localization.AtPrime (q.asIdeal.comap φ₀.toRingHom)))) ^
            (N + d * (8 * c)))) =
      (Ideal.Quotient.mk ((q.asIdeal.map
        (algebraMap Λ (Localization.AtPrime q.asIdeal))) ^
          (N + d * (8 * c)))).comp ψ₀)
    (hinc₀ : ∀ i : Fin r, Ideal.Quotient.mk
      ((q.asIdeal.map (algebraMap Λ (Localization.AtPrime q.asIdeal))) ^
        (N + d * (8 * c)))
      (algebraMap Λ (Localization.AtPrime q.asIdeal) (α (f (MvPolynomial.X i)))) ∈
        Set.range g₀) :
    let S := MvPolynomial (Fin d) k
    ∃ (m : ℕ) (_ : Algebra (MvPolynomial (Fin m) k) Λ)
      (_ : IsScalarTower k (MvPolynomial (Fin m) k) Λ)
      (_ : Algebra S (MvPolynomial (Fin m) k))
      (_ : IsScalarTower k S (MvPolynomial (Fin m) k))
      (_ : Algebra S Λ) (_ : IsScalarTower S (MvPolynomial (Fin m) k) Λ)
      (_ : IsScalarTower k S Λ) (ell : Fin d × Fin s → Λ)
      (rho : Fin d → MvPolynomial (Fin m) k),
    (rho = fun i ↦ algebraMap S (MvPolynomial (Fin m) k) (MvPolynomial.X i)) ∧
    (∀ i, algebraMap S Λ (MvPolynomial.X i) ^ (2 * N) =
      ∑ j : Fin s, ell (i, j) * α (a j)) ∧
    (∀ i, algebraMap (MvPolynomial (Fin m) k) Λ (rho i) ∈ q.asIdeal) ∧
    (∀ (i : Fin d)
      (x : MvPolynomial (Fin m) k ⧸ Ideal.span
        {y | ∃ j : Fin d, j.val < i.val ∧ y = rho j ^ (c * 8)}),
      rho i • x = 0 ↔ rho i ^ 2 • x = 0) ∧
    (∀ (i : Fin d)
      (x : Λ ⧸ Ideal.span
        {y | ∃ j : Fin d, j.val < i.val ∧
            y = algebraMap (MvPolynomial (Fin m) k) Λ (rho j) ^ (c * 8)}),
      rho i • x = 0 ↔ rho i ^ 2 • x = 0) ∧
    let R := MvPolynomial (Fin m) k
    let Q := Localization.AtPrime (q.asIdeal.under R)
    let L := Localization.AtPrime q.asIdeal
    let K := IsLocalRing.maximalIdeal L ^ (N + d * (8 * c))
    ∃ (H : Ideal R),
      H.map (algebraMap R Q) =
        Ideal.span (Set.range (fun i : Fin d ↦ algebraMap R Q (rho i))) ∧
      H.map ((algebraMap Λ L).comp (algebraMap R Λ)) = IsLocalRing.maximalIdeal L ∧
      ∃ (B : Type u) (_ : CommRing B) (_ : Algebra k B)
        (D' : Type (max u v)) (_ : CommRing D')
        (_ : IsLocalRing D') (_ : IsArtinianRing D') (_ : Algebra k D')
        (_ : Algebra B D') (_ : IsScalarTower k B D'),
        let I₀ := H ^ (N + d * (8 * c))
        ∃ (e : (R ⧸ I₀) ≃ₐ[k] MvPolynomial (Fin d) B),
          EssentiallySmooth B D' ∧
          ∃ (f₀ : A →ₐ[k] D') (g : D' →+* L ⧸ K)
            (u₀ : Fin d → D') (δ : Fin d → D'ˣ) (coeff : Fin d × Fin s → D'),
            IsLocalRing (L ⧸ K) ∧ IsLocalHom g ∧ g.Flat ∧
            (∀ i : Fin d,
              MvPolynomial.map (algebraMap B D')
                (e (Ideal.Quotient.mk I₀ (algebraMap S R (MvPolynomial.X i)))) =
              MvPolynomial.C (σ := Fin d) (u₀ i) * MvPolynomial.X (R := D') i) ∧
            (∀ z : R, MvPolynomial.eval₂Hom g (fun i ↦ g (δ i : D'))
              (MvPolynomial.map (algebraMap B D') (e (Ideal.Quotient.mk I₀ z))) =
              Ideal.Quotient.mk K (algebraMap Λ L (algebraMap R Λ z))) ∧
            (∀ x, g (f₀ x) = Ideal.Quotient.mk K (algebraMap Λ L (α x))) ∧
            (∀ ij, g (coeff ij) = Ideal.Quotient.mk K (algebraMap Λ L (ell ij))) := by
  classical
  obtain ⟨m, hRΛ, hkRΛ, hSR, hkSR, hSΛ, hSRΛ, hkSΛ, ell, rho,
    hrho, hrel, hmem, hkerR, hkerΛ, E, uP, tΛ, huP, hparameters, ht,
    hErho, hC, hX, D, hD, hlocalD, hartD, hkD, hBD, hkBD, hsmooth,
    f₀, g, δ, coeff, hlocal, hlocalg, hflatg, hgC, hgX, hgf, hgcoeff⟩ :=
    exists_popescu_coefficient_rescaling p hp α q hreg N hN hpower d hd s a ha c hc
      r f hf m₀ φ₀ ψ₀ hψ₀ hideal₀ hflat₀ D₀ g₀ hsmooth₀ hgflat₀ hfactor₀ hinc₀
  let R := MvPolynomial (Fin m) k
  let P := MvPolynomial (Fin m₀) k
  let p₀ := q.asIdeal.comap φ₀.toRingHom
  let n := N + d * (8 * c)
  let B := P ⧸ p₀ ^ n
  let S := MvPolynomial (Fin d) k
  let L := Localization.AtPrime q.asIdeal
  let K := IsLocalRing.maximalIdeal L ^ n
  let : Algebra R Λ := hRΛ
  have : IsScalarTower k R Λ := hkRΛ
  let : Algebra S R := hSR
  have : IsScalarTower k S R := hkSR
  let : Algebra S Λ := hSΛ
  have : IsScalarTower S R Λ := hSRΛ
  have : IsScalarTower k S Λ := hkSΛ
  let : CommRing D := hD
  have : IsLocalRing D := hlocalD
  have : IsArtinianRing D := hartD
  let : Algebra k D := hkD
  let : Algebra B D := hBD
  have : IsScalarTower k B D := hkBD
  obtain ⟨H, e, hHQ, hHL, heC, heX⟩ :=
    exists_polynomial_parameter_quotient_chart m₀ m d n φ₀ q E uP tΛ
      hparameters hideal₀ ht hC hX
  have hrhoE (i : Fin d) : rho i = E.symm (MvPolynomial.C (uP i) * MvPolynomial.X i) :=
    E.injective (by simpa only [AlgEquiv.apply_symm_apply] using hErho i)
  have hHQ' : H.map (algebraMap R (Localization.AtPrime (q.asIdeal.under R))) =
      Ideal.span (Set.range (fun i ↦
        algebraMap R (Localization.AtPrime (q.asIdeal.under R)) (rho i))) := by
    simpa only [hrhoE] using hHQ
  let u₀ : Fin d → D := fun i ↦ algebraMap B D (Ideal.Quotient.mk (p₀ ^ n) (uP i))
  have hpoly (i : Fin d) :
      MvPolynomial.map (algebraMap B D)
        (e (Ideal.Quotient.mk (H ^ n) (algebraMap S R (MvPolynomial.X i)))) =
      MvPolynomial.C (u₀ i) * MvPolynomial.X i := by
    have hi : algebraMap S R (MvPolynomial.X i) = rho i := congrFun hrho i |>.symm
    rw [hi, hrhoE i, map_mul, map_mul, map_mul, heC, heX, map_mul]
    change MvPolynomial.map (algebraMap B D)
      (MvPolynomial.C (Ideal.Quotient.mk (p₀ ^ n) (uP i))) *
        MvPolynomial.map (algebraMap B D) (MvPolynomial.X i) = _
    rw [MvPolynomial.map_C, MvPolynomial.map_X]
  let ev : MvPolynomial (Fin d) D →+* L ⧸ K :=
    MvPolynomial.eval₂Hom g (fun i ↦ g (δ i : D))
  let red : R →+* MvPolynomial (Fin d) D :=
    (MvPolynomial.map (algebraMap B D)).comp
      (e.toRingHom.comp (Ideal.Quotient.mk (H ^ n)))
  let target : R →+* L ⧸ K :=
    (Ideal.Quotient.mk K).comp ((algebraMap Λ L).comp (algebraMap R Λ))
  have heval : ev.comp (red.comp E.symm.toRingHom) = target.comp E.symm.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro z
      change ev (MvPolynomial.map (algebraMap B D)
        (e (Ideal.Quotient.mk (H ^ n) (E.symm (MvPolynomial.C z))))) =
        Ideal.Quotient.mk K (algebraMap Λ L (algebraMap R Λ (E.symm (MvPolynomial.C z))))
      rw [heC, MvPolynomial.map_C, hC]
      simp only [ev, MvPolynomial.eval₂Hom_C]
      exact hgC z
    · intro i
      change ev (MvPolynomial.map (algebraMap B D)
        (e (Ideal.Quotient.mk (H ^ n) (E.symm (MvPolynomial.X i))))) =
        Ideal.Quotient.mk K (algebraMap Λ L (algebraMap R Λ (E.symm (MvPolynomial.X i))))
      rw [heX, MvPolynomial.map_X, hX]
      simp only [ev, MvPolynomial.eval₂Hom_X']
      exact hgX i
  have heval' (z : R) :
      MvPolynomial.eval₂Hom g (fun i ↦ g (δ i : D))
        (MvPolynomial.map (algebraMap B D) (e (Ideal.Quotient.mk (H ^ n) z))) =
      Ideal.Quotient.mk K (algebraMap Λ L (algebraMap R Λ z)) := by
    have hz := RingHom.congr_fun heval (E z)
    change ev (red (E.symm (E z))) = target (E.symm (E z)) at hz
    rw [AlgEquiv.symm_apply_apply] at hz
    dsimp only [ev, red, target] at hz
    simp only [RingHom.comp_apply] at hz
    exact hz
  exact ⟨m, hRΛ, hkRΛ, hSR, hkSR, hSΛ, hSRΛ, hkSΛ, ell, rho,
    hrho, hrel, hmem, hkerR, hkerΛ, H, hHQ', hHL, B, inferInstance, inferInstance,
    D, hD, hlocalD, hartD, hkD, hBD, hkBD, e, hsmooth,
    f₀, g, u₀, δ, coeff, hlocal, hlocalg, hflatg, hpoly, heval', hgf, hgcoeff⟩


end Algebra
