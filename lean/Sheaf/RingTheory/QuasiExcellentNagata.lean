/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NU
-/
module

public import Sheaf.RingTheory.ExcellentRing
public import WeilConjectures.RingTheory.NagataRing
import Sheaf.RingTheory.FiniteTypeGRing
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Localization.Submodule
import WeilConjectures.RingTheory.RegularRingNormal
import WeilConjectures.RingTheory.IsN1OfIsAnalyticallyUnramified
import WeilConjectures.RingTheory.IsN1OfLocalCharacterization
import Sheaf.RingTheory.RegularMapReducedTarget
import Sheaf.RingTheory.UniversallyJapaneseN1Criterion
import WeilConjectures.RingTheory.AdicCompletionNoetherian

/-!
# Quasi-excellent rings are Nagata

Source: Stacks Project, More on Algebra, Lemma Tag 07QV
(blueprint: lem-exc-quasi-excellent-nagata).
-/

@[expose] public section

set_option autoImplicit false

universe u

/-- Every commutative quasi-excellent ring is Nagata.

Source: Stacks Project, More on Algebra, Lemma Tag 07QV
(blueprint: lem-exc-quasi-excellent-nagata).

Proof:
1. Let `S` be any finite type domain algebra over `R`. The G-ring clause of
   `def-exc-excellent-ring` and `lem-weil-pbc-finite-type-over-g-ring` make `S` a
   Noetherian G-ring (`def-weil-pbc-g-ring`). We show that `S` is N-1.
2. The J-2 clause says the regular locus of `Spec S` is open. The zero-prime
   localization is the fraction field (`def-weil-pbc-localization-at-prime`), which
   is regular (`lem-weil-pbc-field-regular-ring`). The closed complement is `V(I)`
   by `lem-weil-pbc-spec-irreducible-closed-subsets-primes`. Since it misses the
   zero prime, some nonzero `f` lies in `I`; then `D(f)` is contained in the regular
   locus (`def-weil-affine-spectrum`).
3. The ring `S_f` (`def-weil-ring-localization-away`) is Noetherian by
   `lem-weil-pbc-localization-noetherian`. A prime `Q` contracts to a prime `p`
   outside `f` (`lem-weil-pbc-localization-spectrum-embedding`). The local rings
   `(S_f)_Q` and `S_p` are isomorphic: on fractions the maps are
   `a/u ↦ (a/1)/(u/1)` and `(a/f^n)/(b/f^m) ↦ a*f^m/(b*f^n)`.
   The localization equality criteria make these well-defined inverse maps.
   Thus every prime localization is regular local. By `def-weil-regular-scheme`
   and `lem-weil-pbc-regular-ring-normal`, the principal localization is normal.
4. For every maximal ideal `m` of `S`, put `A = S_m`. This is Noetherian local,
   and is a domain: a zero product of fractions gives `w*a*b = 0` for a nonzero
   denominator `w`, hence one numerator is zero. Its maximal-ideal completion
   map is regular by `def-weil-pbc-g-ring`, and its completion is Noetherian by
   `lem-weil-pbc-adic-completion-noetherian`. Apply
   `lem-exc-regular-map-reduced-target` to the reduced domain `A` to see that
   this completion is reduced.
5. Apply `lem-weil-pbc-analytically-unramified-n1` to each such `A`. It follows
   that every maximal localization of `S` is N-1.
6. Apply `lem-weil-pbc-n1-local-characterization` to the nonzero `f` from step 2,
   its normal principal localization from step 3, and the local N-1 conclusion
   of step 5. Hence `S` is N-1. This holds for every finite type domain algebra.
7. By `lem-exc-universally-japanese-n1-criterion`, `R` is universally Japanese:
   every finite type domain algebra is N-2.
8. For any prime `p` of `R`, the quotient `R/p` is a domain and is a finite type
   `R`-algebra (no generators are needed, `def-weil-pbc-finite-type-algebra`).
   Step 7 makes it N-2. Together with Noetherianity from quasi-excellence these
   are exactly the two clauses of `def-weil-pbc-nagata-ring`.
-/
theorem isNagataRing_of_isQuasiExcellent (R : Type u) [CommRing R]
    (hR : IsQuasiExcellent R) : IsNagataRing R := by
  let : IsNoetherianRing R := hR.1
  have hJapanese : IsUniversallyJapanese R := by
    apply isUniversallyJapanese_of_forall_isN1 R
    intro S _ _ _ _
    have hG : IsGRing S := isGRing_of_finiteType hR.2.1
    let : IsNoetherianRing S := hG.1
    apply isN1_of_local_characterization S (FractionRing S)
    · let p₀ : PrimeSpectrum S := ⟨⊥, inferInstance⟩
      have hreg : IsRegularLocalRing (Localization.AtPrime p₀.asIdeal) := by
        let : IsLocalization (⊥ : Ideal S).primeCompl (FractionRing S) := by
          rw [Ideal.primeCompl_bot]
          infer_instance
        exact IsRegularLocalRing.of_ringEquiv
          (IsLocalization.algEquiv (⊥ : Ideal S).primeCompl
            (FractionRing S) (Localization.AtPrime (⊥ : Ideal S))).toRingEquiv
      obtain ⟨_, ⟨_, ⟨f, rfl⟩, rfl⟩, h₀f, hfU⟩ :=
        PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hreg (hR.2.2 S)
      refine ⟨f, ?_, ?_⟩
      · simpa [p₀, PrimeSpectrum.mem_basicOpen] using h₀f
      · have : IsRegularRing (Localization.Away f) := by
          apply isRegularRing_iff.mpr
          intro p hp
          have hpf : PrimeSpectrum.comap (algebraMap S (Localization.Away f))
              ⟨p, hp⟩ ∈ PrimeSpectrum.basicOpen f := by
            change PrimeSpectrum.comap (algebraMap S (Localization.Away f))
              ⟨p, hp⟩ ∈ (↑(PrimeSpectrum.basicOpen f) : Set (PrimeSpectrum S))
            rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away f) f]
            exact ⟨⟨p, hp⟩, rfl⟩
          have : IsRegularLocalRing
              (Localization.AtPrime (p.comap (algebraMap S (Localization.Away f)))) :=
            hfU hpf
          exact IsRegularLocalRing.of_ringEquiv
            (IsLocalization.localizationLocalizationAtPrimeIsoLocalization
              (Submonoid.powers f) p).toRingEquiv
        exact IsRegularRing.isNormalRing (Localization.Away f)
    · intro m hm
      let A := Localization.AtPrime m
      let : IsNoetherianRing A := inferInstance
      have : IsNoetherianRing (AdicCompletion (IsLocalRing.maximalIdeal A) A) :=
        AdicCompletion.isNoetherianRing _
      apply isN1_of_isAnalyticallyUnramified A (FractionRing A)
      exact RingHom.isReduced_of_isRegular
        (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) (hG.2 m)
  exact ⟨hR.1, fun p _ ↦ hJapanese (R ⧸ p)⟩
