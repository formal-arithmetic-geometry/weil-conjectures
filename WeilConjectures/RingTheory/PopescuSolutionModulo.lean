/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GRing
public import WeilConjectures.RingTheory.EssentiallySmooth
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.LocalRing.Defs
import WeilConjectures.RingTheory.PopescuFlatCoordinates
import WeilConjectures.RingTheory.PopescuEtaleQuotientMap
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# Solving modulo a prime power through an essentially smooth Artinian algebra

For a geometrically regular Noetherian `k`-algebra `Λ` and a prime `q`, every finite subset of
`Λ_q / (q Λ_q)^n` lies in the image of an Artinian local algebra `D` that is essentially smooth
over `P / (𝔭 P)^n`, where `P` is the localization of a polynomial algebra `k[y_1, …, y_m]` at a
prime `𝔭` with `𝔭 Λ_q = q Λ_q` and `P → Λ_q` flat.

## Implementation details

The algebra `D` is a Popescu-admissible subalgebra of `Λ_q / (q Λ_q)^n` containing the given
finite set. Unlike in the Stacks Project, the subalgebra is first enlarged
(`exists_popescu_admissible_differential_basis`), since suitable elements of `Λ` need not exist
for every admissible subalgebra. The map `P / (𝔭 P)^n → D` is then shown to be étale (flat,
finitely presented, with `m_D = 𝔭 D` and finite separable residue field extension), hence
essentially smooth.

## References

* [Stacks Project, Tag 07FH](https://stacks.math.columbia.edu/tag/07FH)
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace Algebra

private theorem local_artinian_prime_pow
    (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (n : ℕ) (hn : 1 ≤ n) :
    IsLocalRing (R ⧸ IsLocalRing.maximalIdeal R ^ n) ∧
      IsArtinianRing (R ⧸ IsLocalRing.maximalIdeal R ^ n) := by
  have hn0 : n ≠ 0 := Nat.ne_zero_of_lt hn
  have hproper : IsLocalRing.maximalIdeal R ^ n ≠ ⊤ := by
    exact ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal R).ne_top
      (Ideal.pow_le_self hn0)
  have : Nontrivial (R ⧸ IsLocalRing.maximalIdeal R ^ n) :=
    Ideal.Quotient.nontrivial_iff.mpr hproper
  refine ⟨IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective, ?_⟩
  apply IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing
  rw [← Ideal.radical_minimalPrimes, Ideal.radical_pow _ hn0,
    Ideal.IsPrime.radical (IsLocalRing.maximalIdeal.isMaximal R).isPrime,
    Ideal.minimalPrimes_eq_subsingleton_self]
  exact Set.mem_singleton _


/-- Let `k` be a field of characteristic `p > 0`, `Λ` a Noetherian, geometrically regular
`k`-algebra, `q` a prime of `Λ`, `n ≥ 1`, and `E` a finite subset of `Λ_q / (q Λ_q)^n`. Then
there are a `k`-algebra map `φ : k[y_1, …, y_m] → Λ` and, with `𝔭 = φ⁻¹(q)` and `P = k[y]_𝔭`, a
flat map `ψ : P → Λ_q` compatible with `φ` such that `q Λ_q = 𝔭 Λ_q`, the quotients
`P / (𝔭 P)^n` and `Λ_q / (q Λ_q)^n` are Artinian local, and there is an Artinian local ring `D`
with local homomorphisms `P / (𝔭 P)^n → D → Λ_q / (q Λ_q)^n`, the first essentially smooth and
the second flat, whose composite is induced by `ψ` and whose image contains `E`. -/
theorem exists_essentiallySmooth_artinian_factorization_mod_prime_pow
    (k : Type u) (Λ : Type v) [Field k] [CommRing Λ] [Algebra k Λ]
    [IsNoetherianRing Λ] (p : ℕ) [CharP k p] (hp : 0 < p)
    (hreg : IsGeometricallyRegular k Λ) (q : Ideal Λ) [q.IsPrime]
    (n : ℕ) (hn : 1 ≤ n)
    (E : Finset (Localization.AtPrime q ⧸
      (q.map (algebraMap Λ (Localization.AtPrime q))) ^ n)) :
    ∃ (m : ℕ) (φ : MvPolynomial (Fin m) k →ₐ[k] Λ)
      (ψ : Localization.AtPrime (q.comap φ.toRingHom) →+* Localization.AtPrime q),
      ψ.comp (algebraMap (MvPolynomial (Fin m) k)
          (Localization.AtPrime (q.comap φ.toRingHom))) =
        (algebraMap Λ (Localization.AtPrime q)).comp φ.toRingHom ∧
      q.map (algebraMap Λ (Localization.AtPrime q)) =
        (q.comap φ.toRingHom).map
          ((algebraMap Λ (Localization.AtPrime q)).comp φ.toRingHom) ∧
      ψ.Flat ∧
      IsLocalRing (Localization.AtPrime (q.comap φ.toRingHom) ⧸
        ((q.comap φ.toRingHom).map (algebraMap (MvPolynomial (Fin m) k)
          (Localization.AtPrime (q.comap φ.toRingHom)))) ^ n) ∧
      IsArtinianRing (Localization.AtPrime (q.comap φ.toRingHom) ⧸
        ((q.comap φ.toRingHom).map (algebraMap (MvPolynomial (Fin m) k)
          (Localization.AtPrime (q.comap φ.toRingHom)))) ^ n) ∧
      IsLocalRing (Localization.AtPrime q ⧸
        (q.map (algebraMap Λ (Localization.AtPrime q))) ^ n) ∧
      IsArtinianRing (Localization.AtPrime q ⧸
        (q.map (algebraMap Λ (Localization.AtPrime q))) ^ n) ∧
      ∃ (D : Type (max u v)) (_ : CommRing D)
        (_ : Algebra (Localization.AtPrime (q.comap φ.toRingHom) ⧸
          ((q.comap φ.toRingHom).map (algebraMap (MvPolynomial (Fin m) k)
            (Localization.AtPrime (q.comap φ.toRingHom)))) ^ n) D)
        (g : D →+* Localization.AtPrime q ⧸
          (q.map (algebraMap Λ (Localization.AtPrime q))) ^ n),
        IsLocalRing D ∧ IsArtinianRing D ∧
        IsLocalHom (algebraMap (Localization.AtPrime (q.comap φ.toRingHom) ⧸
          ((q.comap φ.toRingHom).map (algebraMap (MvPolynomial (Fin m) k)
            (Localization.AtPrime (q.comap φ.toRingHom)))) ^ n) D) ∧
        IsLocalHom g ∧
        EssentiallySmooth (Localization.AtPrime (q.comap φ.toRingHom) ⧸
          ((q.comap φ.toRingHom).map (algebraMap (MvPolynomial (Fin m) k)
            (Localization.AtPrime (q.comap φ.toRingHom)))) ^ n) D ∧
        g.Flat ∧
        (g.comp (algebraMap (Localization.AtPrime (q.comap φ.toRingHom) ⧸
          ((q.comap φ.toRingHom).map (algebraMap (MvPolynomial (Fin m) k)
            (Localization.AtPrime (q.comap φ.toRingHom)))) ^ n) D)).comp
          (Ideal.Quotient.mk ((q.comap φ.toRingHom).map (algebraMap (MvPolynomial (Fin m) k)
            (Localization.AtPrime (q.comap φ.toRingHom))) ^ n)) =
          (Ideal.Quotient.mk
            ((q.map (algebraMap Λ (Localization.AtPrime q))) ^ n)).comp ψ ∧
        ∀ e ∈ E, e ∈ Set.range g := by
  obtain ⟨A, hlocal, hA, hAm, hE, m, φ, ψ, hψ, hideal, hflat, a, ha, hspan⟩ :=
    exists_popescu_flat_coordinates k Λ p hp hreg q n hn E
  let : IsLocalRing A := hlocal
  let P := Localization.AtPrime (q.comap φ.toRingHom)
  let I : Ideal P := (q.comap φ.toRingHom).map (algebraMap (MvPolynomial (Fin m) k) P)
  let B := Localization.AtPrime q ⧸ (q.map (algebraMap Λ (Localization.AtPrime q))) ^ n
  let Q := P ⧸ I ^ n
  have hP : I = IsLocalRing.maximalIdeal P := Localization.AtPrime.map_eq_maximalIdeal
  have hQ : IsLocalRing Q ∧ IsArtinianRing Q := by
    dsimp [Q]
    rw [hP]
    exact local_artinian_prime_pow P n hn
  have hB : IsLocalRing B ∧ IsArtinianRing B := by
    dsimp [B]
    rw [Localization.AtPrime.map_eq_maximalIdeal]
    exact local_artinian_prime_pow (Localization.AtPrime q) n hn
  have : IsLocalRing Q := hQ.1
  have : IsArtinianRing Q := hQ.2
  have : IsLocalRing B := hB.1
  obtain ⟨f, hfLocal, hfEtale, hfcomm⟩ :=
    exists_etale_popescu_quotient_map k Λ q n hn A hA hAm m φ ψ hψ hideal hflat a ha hspan
  let : Algebra Q A := f.toAlgebra
  have : Etale Q A := hfEtale
  have : IsLocalHom f := hfLocal
  have : IsArtinianRing A := hA.1
  let D := ULift.{u} A
  let e : D ≃ₐ[Q] A := ULift.algEquiv
  have : IsLocalRing D := e.toRingEquiv.symm.isLocalRing
  have : IsArtinianRing D := e.toRingEquiv.symm.isArtinianRing
  have : Etale Q D := Etale.of_equiv e.symm
  let g : D →+* B := A.val.toRingHom.comp e.toRingHom
  have hvalLocal : IsLocalHom A.val.toRingHom := by
    apply (IsLocalRing.local_hom_TFAE A.val.toRingHom).out 5 1 |>.mp
    change (IsLocalRing.maximalIdeal B).comap A.val.toRingHom = _
    rw [← IsLocalRing.map_maximalIdeal_of_surjective
      (Ideal.Quotient.mk ((q.map (algebraMap Λ (Localization.AtPrime q))) ^ n))
      Ideal.Quotient.mk_surjective, ← Localization.AtPrime.map_eq_maximalIdeal]
    exact hAm.symm
  have : IsLocalHom A.val.toRingHom := hvalLocal
  have : IsLocalHom e.toRingHom := IsLocalHom.of_surjective _ e.surjective
  have hgLocal : IsLocalHom g := RingHom.isLocalHom_comp _ _
  have hgFlat : g.Flat :=
    (RingHom.Flat.of_bijective e.bijective).comp hA.2.2.choose_spec.1
  have hsmooth : EssentiallySmooth Q D := by
    refine ⟨D, inferInstance, inferInstance, inferInstance, ⊥, ?_⟩
    exact ⟨(IsLocalization.atUnits D (⊥ : Submonoid D)
      (S := Localization (⊥ : Submonoid D)) bot_le).restrictScalars Q⟩
  refine ⟨m, φ, ψ, hψ, hideal, hflat, hQ.1, hQ.2, hB.1, hB.2,
    D, inferInstance, inferInstance, g, inferInstance, inferInstance,
    ?_, hgLocal, hsmooth, hgFlat, ?_, ?_⟩
  · change IsLocalHom (e.symm.toRingHom.comp f)
    have : IsLocalHom e.symm.toRingHom := IsLocalHom.of_surjective _ e.symm.surjective
    exact RingHom.isLocalHom_comp _ _
  · change (g.comp (algebraMap Q D)).comp (Ideal.Quotient.mk (I ^ n)) = _
    have hgf : g.comp (algebraMap Q D) = A.val.toRingHom.comp f := by
      ext x
      rfl
    rw [hgf]
    exact hfcomm
  · intro x hx
    refine ⟨e.symm ⟨x, hE x hx⟩, ?_⟩
    exact congrArg (fun y : A ↦ (y : B)) (e.apply_symm_apply _)

end Algebra
