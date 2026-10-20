/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Sheaf.RingTheory.ExcellentRing
public import Mathlib.RingTheory.FiniteType
public import Mathlib.Algebra.Module.LocalizedModule.Basic
import Sheaf.RingTheory.FiniteTypeGRing
import Sheaf.RingTheory.ExcellentOfWeaklyEtale
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Finiteness.Small
import Mathlib.Algebra.Algebra.Shrink
import WeilConjectures.Mathlib.RingTheory.Etale.Weakly
import WeilConjectures.RingTheory.ProEtale.WeaklyEtale

/-!
# Excellence of finite type algebras and their localizations

Source: Stacks Project, More on Algebra, Tag 07QU, lemma-finite-type-over-excellent
(blueprint: lem-exc-finite-type-localization-excellent).
-/

@[expose] public section

set_option autoImplicit false

universe u v

private theorem catenary_equiv {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] (e : R ≃+* A) (hR : IsCatenaryRing R) :
    IsCatenaryRing A := by
  let E := e.idealComapOrderIso
  have prime (p : Ideal A) (hp : p.IsPrime) : (E p).IsPrime := by
    exact hp.comap e.toRingHom
  have chain (p q : Ideal A) (n : ℕ) (c : Fin (n + 1) → Ideal A)
      (hc : IsPrimeChain A p q n c) :
      IsPrimeChain R (E p) (E q) n (fun i ↦ E (c i)) := by
    refine ⟨fun i ↦ prime _ (hc.1 i), congrArg E hc.2.1,
      congrArg E hc.2.2.1, fun i ↦ E.lt_iff_lt.mpr (hc.2.2.2 i)⟩
  have saturated (p q : Ideal A) (n : ℕ) (c : Fin (n + 1) → Ideal A)
      (hc : IsSaturatedPrimeChain A p q n c) :
      IsSaturatedPrimeChain R (E p) (E q) n (fun i ↦ E (c i)) := by
    refine ⟨chain p q n c hc.1, ?_⟩
    intro i
    rintro ⟨r, hr, hleft, hright⟩
    have : r.IsPrime := hr
    have hprime : (E.symm r).IsPrime := by
      change (r.map e).IsPrime
      exact Ideal.map_isPrime_of_equiv e
    apply hc.2 i
    refine ⟨E.symm r, hprime, ?_, ?_⟩
    · exact E.lt_iff_lt.mp (by simpa using hleft)
    · exact E.lt_iff_lt.mp (by simpa using hright)
  intro p q hp hq hpq
  have : (E p).IsPrime := prime p hp
  have : (E q).IsPrime := prime q hq
  obtain ⟨⟨N, hN⟩, hsat⟩ := hR (E p) (E q) (E.monotone hpq)
  refine ⟨⟨N, fun n c hc ↦ hN n _ (chain p q n c hc)⟩, ?_⟩
  intro n m c d hc hd
  exact hsat n m _ _ (saturated p q n c hc) (saturated p q m d hd)

private theorem open_regular_equiv {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] (e : R ≃+* A)
    (hR : IsOpen {p : PrimeSpectrum R |
      IsRegularLocalRing (Localization.AtPrime p.asIdeal)}) :
    IsOpen {p : PrimeSpectrum A |
      IsRegularLocalRing (Localization.AtPrime p.asIdeal)} := by
  have heq : {p : PrimeSpectrum A |
      IsRegularLocalRing (Localization.AtPrime p.asIdeal)} =
      PrimeSpectrum.comap e.toRingHom ⁻¹' {p : PrimeSpectrum R |
        IsRegularLocalRing (Localization.AtPrime p.asIdeal)} := by
    ext p
    let q : Ideal R := p.asIdeal.comap e.toRingHom
    let a := Localization.localRingEquiv q p.asIdeal e rfl
    constructor
    · intro hp
      have : IsRegularLocalRing (Localization.AtPrime p.asIdeal) := hp
      exact IsRegularLocalRing.of_ringEquiv a.symm
    · intro hp
      have : IsRegularLocalRing (Localization.AtPrime q) := hp
      exact IsRegularLocalRing.of_ringEquiv a
  rw [heq]
  exact hR.preimage (PrimeSpectrum.continuous_comap e.toRingHom)

/-- A localization of a finite type algebra over an excellent ring is excellent;
in particular the finite type algebra itself is excellent. Here `LocalizedModule S A`
is the ring localization: it is definitionally `Localization S`.

Source: Stacks Project, More on Algebra, Tag 07QU, lemma-finite-type-over-excellent
(blueprint: lem-exc-finite-type-localization-excellent).

Proof:
1. Unpack `IsExcellent R`: `R` is Noetherian, a G-ring, J-2 and universally catenary.
   By `lem-weil-pbc-finite-type-algebra-noetherian`, `A` is Noetherian. By
   `lem-weil-pbc-finite-type-over-g-ring`, `A` is a G-ring. Neither assertion requires
   injectivity of the structure map.
2. A finite type algebra over `A` is finite type over `R`: combine finite generating
   families, substituting polynomial expressions. Its regular locus is therefore open
   and it is catenary by `def-exc-excellent-ring` for `R`. Thus `A` is J-2 and universally
   catenary, hence excellent. This proves the final conjunct.
3. Put `B = S⁻¹A`. The fraction construction of `def-weil-pbc-module-localization`
   inverts `S`, represents every element by a fraction, and detects zero by multiplication
   by a denominator. Apply `lem-weil-pbc-localization-noetherian` to make `B` Noetherian.
4. For a prime `q` of `B`, contract it to `p` in `A`. By
   `lem-weil-pbc-localization-prime-residue-field-iso`, the canonical isomorphism
   `Aₚ ≃ B_q` identifies their maximal ideals. By `lem-weil-pbc-adic-completion-ring-equiv`
   it extends to their completions and commutes with the completion maps. The map for
   `Aₚ` is regular by `def-weil-pbc-g-ring`. Transfer regularity through the commuting
   isomorphisms using `lem-weil-pbc-regular-ring-map-ring-equiv`. Thus `B` is a G-ring.
5. For any finite type `B`-algebra `C`, let `D` be the subring of `C` generated by the
   image of `A` and a finite generating family for `C` over `B`. Then `D` is finite type
   over `A`. The image of `S` in `D` consists of units in `C`. The fraction map from
   its localization to `C` is injective since `D` is a subring of `C`; it is surjective
   by writing each polynomial expression over a common denominator. Thus `C` is this
   localization of `D`, without any injectivity assumption on `A → C`.
6. Both `D` and `C` are Noetherian by `lem-weil-pbc-finite-type-algebra-noetherian`.
   The regular locus of `D` is open by J-2 for `A`. Contraction on spectra is continuous
   by `lem-weil-pbc-localization-spectrum-embedding`. The local-ring isomorphisms of
   `lem-weil-pbc-localization-prime-residue-field-iso` identify regular loci, since
   regular locality is invariant under ring isomorphism: ideals, their generators,
   maximal ideals and prime-chain lengths correspond. Hence the regular locus of `C`
   is the inverse image of that of `D`, so it is open. This proves J-2 for `B`.
7. The ring `D` is catenary by universal catenarity of `A`. The prime correspondence of
   `lem-weil-pbc-localization-prime-residue-field-iso` preserves whole intervals between
   primes avoiding the denominators: every intermediate prime also avoids them. It
   preserves chain lengths and saturation, so `C` is catenary. As `C` was arbitrary,
   `B` is universally catenary.
8. The four properties in steps 3, 4, 6 and 7 give excellence of `B`. Equivalently,
   the final assertion also follows by taking `S = {1}`. No condition excluding zero
   from `S` is needed: if it contains zero, `B` and every `B`-algebra are zero, and
   the primewise and open-locus conditions are vacuous.
-/
theorem isExcellent_finiteType_localization {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A] (hR : IsExcellent R)
    [Algebra.FiniteType R A] (S : Submonoid A) :
    IsExcellent (LocalizedModule S A) ∧ IsExcellent A := by
  have hA : IsExcellent A := by
    have : IsNoetherianRing R := hR.1.1
    have hnoeth : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing R A
    refine ⟨⟨hnoeth, isGRing_of_finiteType hR.1.2.1, ?_⟩, hnoeth, ?_⟩
    · intro T _ _ _
      let : Algebra R T := ((algebraMap A T).comp (algebraMap R A)).toAlgebra
      have : IsScalarTower R A T := IsScalarTower.of_algebraMap_eq' rfl
      have : Algebra.FiniteType R T :=
        Algebra.FiniteType.trans (R := R) (S := A) inferInstance inferInstance
      have : Small.{u} T := Algebra.FiniteType.small (R := R)
      let T₀ := Shrink.{u} T
      have : Algebra.FiniteType R T₀ :=
        Algebra.FiniteType.of_surjective (Shrink.algEquiv R T).symm.toAlgHom
          (Shrink.algEquiv R T).symm.surjective
      exact open_regular_equiv (Shrink.algEquiv R T).toRingEquiv (hR.1.2.2 T₀)
    · intro T _ _ _
      let : Algebra R T := ((algebraMap A T).comp (algebraMap R A)).toAlgebra
      have : IsScalarTower R A T := IsScalarTower.of_algebraMap_eq' rfl
      have : Algebra.FiniteType R T :=
        Algebra.FiniteType.trans (R := R) (S := A) inferInstance inferInstance
      have : Small.{u} T := Algebra.FiniteType.small (R := R)
      let T₀ := Shrink.{u} T
      have : Algebra.FiniteType R T₀ :=
        Algebra.FiniteType.of_surjective (Shrink.algEquiv R T).symm.toAlgHom
          (Shrink.algEquiv R T).symm.surjective
      exact catenary_equiv (Shrink.algEquiv R T).toRingEquiv (hR.2.2 T₀)
  have : IsNoetherianRing A := hA.1.1
  have : IsNoetherianRing (LocalizedModule S A) :=
    IsLocalization.isNoetherianRing S _ inferInstance
  refine ⟨?_, hA⟩
  -- Localization is weakly étale, so the existing excellence ascent theorem applies.
  apply RingHom.isExcellent_of_weaklyEtale (algebraMap A (LocalizedModule S A)) hA
  exact RingHom.weaklyEtale_algebraMap_iff.mpr
    (Algebra.WeaklyEtale.of_isLocalization A S _)
