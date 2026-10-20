/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Mathlib.RingTheory.Etale.Locus
public import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.Localization.LocalizationLocalization
import WeilConjectures.RingTheory.OpenFlatLocus

/-!
# Étale at a prime and flat unramifiedness

Source: Stacks Project, Lemma 00U6 (lemma-characterize-etale),
lemma-unramified-at-prime, and Lemma 08WD
(blueprint: lem-sc-etale-at-prime-flat-unramified-criterion).
-/

@[expose] public section

namespace Algebra

universe u v

/-- For a finitely presented algebra, étaleness at `q` is equivalent both to an étale
basic neighbourhood and to flatness of `Rₚ → S_q` and vanishing of localized differentials,
where `p = q.under R` is the inverse image of `q`. The étale morphism
`Spec S_g → Spec R` of the node is the affine one, rendered as `Algebra.Etale R S_g`.
Source: Stacks Project, Tags 00U6 and 08WD, and lemma-unramified-at-prime.
(blueprint: lem-sc-etale-at-prime-flat-unramified-criterion)

Proof:
1. `exists_etale_of_isEtaleAt` gives an étale basic neighbourhood. Conversely,
   `basicOpen_subset_etaleLocus_iff_etale` puts the prime in the étale locus.
2. An étale basic neighbourhood is flat over `R`. Localizing further gives flatness
   of `S_q` over `R`, and base localization gives flatness over `Rₚ`. The support
   description of the étale locus gives vanishing of localized differentials.
3. Conversely, base localization identifies flatness over `Rₚ` with flatness over `R`.
   Intersect the open flat locus with the open unramified locus and choose a basic
   neighbourhood of `q` in this intersection.
4. At every maximal ideal of this basic localization, its local ring is the local
   ring of `S` at the contracted prime. These local rings are flat over `R`, so the
   basic localization is flat. It is also formally unramified and finitely presented;
   `Etale.of_formallyUnramified_of_flat` makes it étale, and step 1 finishes. -/
theorem isEtaleAt_iff_exists_away_etale_iff_flat_localized_kaehler
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S] (q : Ideal S) [q.IsPrime] :
    (IsEtaleAt R q ↔
      (∃ g : S, g ∉ q ∧ Algebra.Etale R (Localization.Away g))) ∧
    (IsEtaleAt R q ↔
      (RingHom.Flat
          (Localization.localRingHom (q.under R) q (algebraMap R S) rfl) ∧
        Subsingleton (LocalizedModule q.primeCompl (KaehlerDifferential R S)))) := by
  have hbasic : IsEtaleAt R q ↔
      ∃ g : S, g ∉ q ∧ Algebra.Etale R (Localization.Away g) := by
    constructor
    · intro h
      let := h
      exact exists_etale_of_isEtaleAt (R := R) q
    · rintro ⟨g, hg, he⟩
      exact (basicOpen_subset_etaleLocus_iff_etale.mpr he)
        (show (⟨q, inferInstance⟩ : PrimeSpectrum S) ∈ PrimeSpectrum.basicOpen g from hg)
  refine ⟨hbasic, ⟨?_, ?_⟩⟩
  · intro he
    obtain ⟨g, hg, hge⟩ := hbasic.mp he
    let T := Localization.Away g
    let B := Localization.AtPrime q
    let : Algebra.Etale R T := hge
    have hle : Submonoid.powers g ≤ q.primeCompl := by
      rw [Submonoid.powers_le]
      exact hg
    let : Algebra T B := IsLocalization.localizationAlgebraOfSubmonoidLe T B
      (Submonoid.powers g) q.primeCompl hle
    have : IsScalarTower S T B := IsLocalization.localization_isScalarTower_of_submonoid_le
      T B (Submonoid.powers g) q.primeCompl hle
    have : IsLocalization (q.primeCompl.map (algebraMap S T)) B :=
      IsLocalization.isLocalization_of_submonoid_le T B
        (Submonoid.powers g) q.primeCompl hle
    have : Module.Flat T B :=
      IsLocalization.flat B (q.primeCompl.map (algebraMap S T))
    have : IsScalarTower R T B := IsScalarTower.to₁₃₄ R S T B
    have : Module.Flat R B := Module.Flat.trans R T B
    have hflat : RingHom.Flat
        (Localization.localRingHom (q.under R) q (algebraMap R S) rfl) := by
      let := (Localization.localRingHom (q.under R) q (algebraMap R S) rfl).toAlgebra
      have : IsScalarTower R (Localization.AtPrime (q.under R)) B :=
        .of_algebraMap_eq fun x ↦
          (Localization.localRingHom_to_map (q.under R) q (algebraMap R S) rfl x).symm
      exact (Module.flat_iff_of_isLocalization (Localization.AtPrime (q.under R))
        (q.under R).primeCompl B).mpr inferInstance
    refine ⟨hflat, ?_⟩
    have hmem : (⟨q, inferInstance⟩ : PrimeSpectrum S) ∈ etaleLocus R S := he
    rw [etaleLocus_eq_compl_support] at hmem
    exact Module.notMem_support_iff.mp hmem.1
  · rintro ⟨hf, hΩ⟩
    let B := Localization.AtPrime q
    let := (Localization.localRingHom (q.under R) q (algebraMap R S) rfl).toAlgebra
    have : IsScalarTower R (Localization.AtPrime (q.under R)) B :=
      .of_algebraMap_eq fun x ↦
        (Localization.localRingHom_to_map (q.under R) q (algebraMap R S) rfl x).symm
    have : Module.Flat (Localization.AtPrime (q.under R)) B := hf
    have : Module.Flat R B :=
      (Module.flat_iff_of_isLocalization (Localization.AtPrime (q.under R))
        (q.under R).primeCompl B).mp inferInstance
    have hqflat : Module.Flat R (LocalizedModule q.primeCompl S) :=
      Module.Flat.of_linearEquiv ((IsLocalizedModule.iso q.primeCompl
        (Algebra.linearMap S B)).restrictScalars R)
    have hqur : (⟨q, inferInstance⟩ : PrimeSpectrum S) ∈ unramifiedLocus R S := by
      rw [unramifiedLocus_eq_compl_support]
      exact Module.notMem_support_iff.mpr hΩ
    obtain ⟨_, ⟨_, ⟨g, rfl⟩, rfl⟩, hg, hsub⟩ :=
      PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open
        (show (⟨q, inferInstance⟩ : PrimeSpectrum S) ∈
          {p : PrimeSpectrum S | Module.Flat R (LocalizedModule p.asIdeal.primeCompl S)} ∩
            unramifiedLocus R S from ⟨hqflat, hqur⟩)
        ((Module.isOpen_setOf_flat_localizedModule (R := R) (S := S) (M := S)).inter
          isOpen_unramifiedLocus)
    have : Module.Flat R (Localization.Away g) := by
      apply Module.flat_of_isLocalized_maximal (S := Localization.Away g)
        (M := Localization.Away g) (fun P ↦ Localization.AtPrime P)
        (fun P ↦ Algebra.linearMap _ _)
      intro P _
      let p := P.comap (algebraMap S (Localization.Away g))
      have hp : g ∉ p := by
        intro h
        exact (inferInstance : P.IsPrime).ne_top (P.eq_top_of_isUnit_mem h
          (IsLocalization.Away.algebraMap_isUnit g))
      have : Module.Flat R (LocalizedModule p.primeCompl S) :=
        (hsub (show (⟨p, inferInstance⟩ : PrimeSpectrum S) ∈ PrimeSpectrum.basicOpen g
          from hp)).1
      have : Module.Flat R (Localization.AtPrime p) :=
        Module.Flat.of_linearEquiv ((IsLocalizedModule.iso p.primeCompl
          (Algebra.linearMap S (Localization.AtPrime p))).restrictScalars R).symm
      exact Module.Flat.of_linearEquiv
        ((IsLocalization.localizationLocalizationAtPrimeIsoLocalization
          (Submonoid.powers g) P).toLinearEquiv.restrictScalars R).symm
    have : FormallyUnramified R (Localization.Away g) :=
      basicOpen_subset_unramifiedLocus_iff.mp fun p hp ↦ (hsub hp).2
    have het : Algebra.Etale R (Localization.Away g) :=
      Etale.of_formallyUnramified_of_flat
    exact hbasic.mpr ⟨g, hg, het⟩

end Algebra
