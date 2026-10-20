/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect
public import Mathlib.CategoryTheory.Monoidal.Tor
import Sheaf.RingTheory.BoundedProjectiveResolutionDimension
import Sheaf.RingTheory.BoundedFiniteProjectiveResolution
import Sheaf.RingTheory.PerfectModuleFiniteProjectiveDimension
import WeilConjectures.RingTheory.DepthLeSupportDimension
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Sheaf.RingTheory.AuslanderBuchsbaum
import WeilConjectures.RingTheory.FiniteProjectiveDimensionOfTorBound

/-!
# A uniform finite projective resolution bound for perfect ideal-power quotients

Source: Stacks Project, Algebra, Tag 090V (proposition-Auslander-Buchsbaum), assembled with
Tags 00O5 and 065R and the local-global projective-dimension criterion
(blueprint: lem-weil-pbc-uniform-perfect-quotient-bound).

Homological degree `i` of a projective resolution corresponds to cochain degree `-i`.
Thus vanishing above `r` means cochain support in `[-r, 0]`. The derived tensor with a module
is computed by tensoring this resolution; its degree `-i` cohomology is `Tor'` in degree `i`.
It has no positive cochain terms. No nonzero-quotient assumption is made.

## Main statements

- `ModuleCat.exists_uniform_finite_projective_resolution_quotient_pow`: one common resolution
  length and Tor bound for every positive ideal power.
- `ModuleCat.uniform_finite_projective_resolution_quotient_pow_iff_tor_vanishing`: equivalence
  of the two uniform bounds for the same prescribed integer.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat

private theorem tor_zero_of_bounded_resolution
    {A : Type u} [CommRing A] (X : ModuleCat.{u} A)
    (P : ProjectiveResolution X) (r : ℕ)
    (hP : ∀ i : ℕ, r < i → IsZero (P.complex.X i))
    (M : ModuleCat.{u} A) (i : ℕ) (hi : r < i) :
    IsZero (((Tor' (ModuleCat.{u} A) i).obj X).obj M) := by
  refine IsZero.of_iso ?_ (P.isoLeftDerivedObj (MonoidalCategory.tensorRight M) i)
  erw [← HomologicalComplex.exactAt_iff_isZero_homology]
  exact ShortComplex.exact_of_isZero_X₂ _
    ((MonoidalCategory.tensorRight M).map_isZero (hP i hi))

private theorem local_ring_depth_ne_top
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] :
    IsLocalRing.depth (R := R) R ≠ ⊤ := by
  have h := IsLocalRing.depth_le_supportDim (R := R) R
  rw [Module.supportDim_self_eq_ringKrullDim] at h
  intro ht
  rw [ht] at h
  exact ringKrullDim_ne_top (R := R) (top_le_iff.mp h)

/-- Finite perfect ideal-power quotients have one common finite-projective resolution bound.
Source: Stacks Project, Algebra, Tag 090V and the assembly recorded in
(blueprint: lem-weil-pbc-uniform-perfect-quotient-bound).

Proof:
1. A bounded projective model of a degree-zero perfect module is K-projective.
Maps from it to a module shifted beyond its lowest degree vanish termwise. The Ext
characterization therefore gives finite projective dimension for every quotient.
2. The maximal ideals containing `I` form a finite set: extension along `A → A/I`
embeds them into the subsets of the finite quotient. Each corresponding Noetherian
local ring has finite depth, bounded by its finite Krull dimension. Choose `r` to bound
these finitely many depths; an empty set is allowed.
3. Localizing a quotient preserves its finite projective dimension. A nonzero
localization has its maximal ideal in the quotient's support, so that ideal contains
`I^n`, and hence `I`. Auslander–Buchsbaum bounds its projective dimension by the
local ring depth, and therefore by `r`. Zero localizations satisfy the bound too.
4. The maximal-localization criterion gives the same global projective-dimension bound.
5. Inducting on that bound, choose a finite free presentation. Noetherianity makes
its kernel finite, dimension shifting lowers its projective dimension, and splicing
a finite resolution of the kernel gives finite projective terms with the same bound.
6. Tensor this resolution with any module and compute Tor by its homology. All terms
above `r` vanish, so the same holds for Tor. -/
theorem exists_uniform_finite_projective_resolution_quotient_pow
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    [HasDerivedCategory.{u} (ModuleCat.{u} A)] (I : Ideal A)
    (hfinite : ∀ n : ℕ, 1 ≤ n → Finite (A ⧸ I ^ n))
    (hperfect : ∀ n : ℕ, 1 ≤ n →
      DerivedCategory.IsPerfect
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
          (ModuleCat.of A (A ⧸ I ^ n)))) :
    ∃ r : ℕ,
      (∀ n : ℕ, 1 ≤ n →
        ∃ P : ProjectiveResolution (ModuleCat.of A (A ⧸ I ^ n)),
          (∀ i : ℕ, Module.Finite A (P.complex.X i)) ∧
          (∀ i : ℕ, r < i → IsZero (P.complex.X i))) ∧
      (∀ n : ℕ, 1 ≤ n → ∀ (M : ModuleCat.{u} A) (i : ℕ), r < i →
        IsZero (((Tor' (ModuleCat.{u} A) i).obj (ModuleCat.of A (A ⧸ I ^ n))).obj M)) := by
  classical
  have hfin : Finite (A ⧸ I) := by simpa using hfinite 1 le_rfl
  let T := {m : MaximalSpectrum A // I ≤ m.asIdeal}
  have : Finite T := by
    apply Finite.of_injective
      (fun m : T ↦ (m.1.asIdeal.map (Ideal.Quotient.mk I) : Set (A ⧸ I)))
    intro m k hmk
    apply Subtype.ext
    apply MaximalSpectrum.ext
    have he : m.1.asIdeal.map (Ideal.Quotient.mk I) =
        k.1.asIdeal.map (Ideal.Quotient.mk I) := SetLike.coe_injective hmk
    have he' := congrArg (Ideal.comap (Ideal.Quotient.mk I)) he
    simpa only [Ideal.comap_map_mk m.2, Ideal.comap_map_mk k.2] using he'
  let depthNat (m : T) :=
    (IsLocalRing.depth (R := Localization.AtPrime m.1.asIdeal)
      (Localization.AtPrime m.1.asIdeal)).toNat
  obtain ⟨r, hr⟩ := (Set.finite_range depthNat).bddAbove
  have hpd (n : ℕ) (hn : 1 ≤ n) :
      HasProjectiveDimensionLE (ModuleCat.of A (A ⧸ I ^ n)) r := by
    let X := ModuleCat.of A (A ⧸ I ^ n)
    obtain ⟨d, hd⟩ := finite_projectiveDimension_of_perfect_single X (hperfect n hn)
    apply (hasProjectiveDimensionLE_iff_forall_maximalSpectrum r X).mpr
    intro m
    let R := Localization.AtPrime m.asIdeal
    let N := X.localizedModule m.asIdeal.primeCompl
    have hNfin : Module.Finite R N := by
      change Module.Finite (Localization m.asIdeal.primeCompl)
        (Shrink.{u} (LocalizedModule m.asIdeal.primeCompl X))
      exact Module.Finite.equiv
        (Shrink.linearEquiv (Localization m.asIdeal.primeCompl) _).symm
    have hdloc : HasProjectiveDimensionLE N d := by
      have := hd
      exact localizedModule_hasProjectiveDimensionLE d m.asIdeal.primeCompl X
    by_cases hnt : Nontrivial N
    · have hsupport : (⟨m.asIdeal, m.isMaximal.isPrime⟩ : PrimeSpectrum A) ∈
          Module.support A (A ⧸ I ^ n) := by
        rw [Module.mem_support_iff]
        have : Nontrivial (Shrink.{u} (LocalizedModule m.asIdeal.primeCompl X)) := hnt
        exact (equivShrink.{u} (LocalizedModule m.asIdeal.primeCompl X)).nontrivial
      have hIn : I ^ n ≤ m.asIdeal := by
        have hh := Module.annihilator_le_of_mem_support hsupport
        simpa only [Ideal.annihilator_quotient] using hh
      have hI : I ≤ m.asIdeal := by
        intro a ha
        exact m.isMaximal.isPrime.mem_of_pow_mem n
          (hIn (Ideal.pow_mem_pow ha n))
      have hdepth : IsLocalRing.depth (R := R) R ≤ (r : ℕ∞) := by
        rw [← ENat.natCast_toNat (local_ring_depth_ne_top R)]
        exact_mod_cast hr (Set.mem_range_self (⟨m, hI⟩ : T))
      have hres : HasFiniteProjectiveDimension N :=
        ⟨d, (hasProjectiveResolutionLE_iff_hasProjectiveDimensionLE N d).mpr hdloc⟩
      have hab := IsLocalRing.depth_eq_projectiveDimension_add_depth (R := R) N hres
      have hbound : (ModuleCat.projectiveDimension N hres : ℕ∞) ≤ (r : ℕ∞) := by
        calc
          _ ≤ (ModuleCat.projectiveDimension N hres : ℕ∞) +
              IsLocalRing.depth (R := R) N := le_self_add
          _ = IsLocalRing.depth (R := R) R := hab.symm
          _ ≤ _ := hdepth
      have hboundNat : ModuleCat.projectiveDimension N hres ≤ r := by
        exact_mod_cast hbound
      have hdim : HasProjectiveDimensionLE N (ModuleCat.projectiveDimension N hres) :=
        (hasProjectiveResolutionLE_iff_hasProjectiveDimensionLE N _).mp
          (Nat.find_spec hres)
      have := hdim
      exact hasProjectiveDimensionLT_of_ge N
        (ModuleCat.projectiveDimension N hres + 1) (r + 1) (by omega)
    · have : Subsingleton N := not_nontrivial_iff_subsingleton.mp hnt
      have hz : IsZero N := ModuleCat.isZero_iff_subsingleton.mpr inferInstance
      have := hz.hasProjectiveDimensionLT_zero
      exact hasProjectiveDimensionLT_of_ge N 0 (r + 1) (by omega)
  refine ⟨r, ?_, ?_⟩
  · intro n hn
    exact exists_bounded_finite_projective_resolution _ r (hpd n hn)
  · intro n hn M i hi
    obtain ⟨P, _, hP⟩ := exists_bounded_finite_projective_resolution _ r (hpd n hn)
    exact tor_zero_of_bounded_resolution _ P r hP M i hi

set_option linter.unusedVariables false in
/-- The same bound can equivalently be expressed by derived tensor amplitude `[-r, 0]`.
Source: Stacks Project, Algebra, Tags 00LY, 00M5, 058R and 065R; the equivalence clause of
(blueprint: lem-weil-pbc-uniform-perfect-quotient-bound).

Proof: compute Tor from the supplied projective resolution. Tensoring preserves its
zero terms, so homology vanishes above `r`. Conversely, the finite-module Tor-bound
criterion gives projective dimension at most `r`. Induction through finite free
presentations then constructs a resolution by finite projectives of the same length.
The extra finite-set and perfectness assumptions are unnecessary for this equivalence;
cyclicity and Noetherianity suffice. The argument includes `r = 0` and zero quotients. -/
theorem uniform_finite_projective_resolution_quotient_pow_iff_tor_vanishing
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    [HasDerivedCategory.{u} (ModuleCat.{u} A)] (I : Ideal A)
    (hfinite : ∀ n : ℕ, 1 ≤ n → Finite (A ⧸ I ^ n))
    (hperfect : ∀ n : ℕ, 1 ≤ n →
      DerivedCategory.IsPerfect
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
          (ModuleCat.of A (A ⧸ I ^ n)))) (r : ℕ) :
    (∀ n : ℕ, 1 ≤ n →
      ∃ P : ProjectiveResolution (ModuleCat.of A (A ⧸ I ^ n)),
        (∀ i : ℕ, Module.Finite A (P.complex.X i)) ∧
        (∀ i : ℕ, r < i → IsZero (P.complex.X i))) ↔
    (∀ n : ℕ, 1 ≤ n → ∀ (M : ModuleCat.{u} A) (i : ℕ), r < i →
      IsZero (((Tor' (ModuleCat.{u} A) i).obj (ModuleCat.of A (A ⧸ I ^ n))).obj M)) := by
  constructor
  · intro h n hn M i hi
    obtain ⟨P, _, hP⟩ := h n hn
    exact tor_zero_of_bounded_resolution _ P r hP M i hi
  · intro h n hn
    exact exists_bounded_finite_projective_resolution _ r
      (finite_hasProjectiveDimensionLE_of_tor_bound _ r (h n hn))

end ModuleCat
