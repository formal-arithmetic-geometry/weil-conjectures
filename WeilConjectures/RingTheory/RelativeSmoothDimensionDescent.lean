/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.RingHom.StandardSmooth
public import Mathlib.RingTheory.RingHom.Locally
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.RingHomProperties

import Mathlib.RingTheory.Etale.Descent
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Kaehler.TensorProduct
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-!
# Faithfully flat descent of relative smooth dimension

Source: Stacks Project, Descent, Tag 02VL, and Morphisms, Tag 02G1;
Algebra, Tag 00T7, part (2).
(blueprint: lem-pd-relative-smooth-dimension-codescent).
-/

@[expose] public section

namespace RingHom

private theorem smooth_of_locally_dimension {R S : Type _} [CommRing R] [CommRing S]
    [Algebra R S] (n : ℕ)
    (h : Locally (IsStandardSmoothOfRelativeDimension n) (algebraMap R S)) :
    Algebra.Smooth R S := by
  rw [← smooth_algebraMap]
  obtain ⟨s, hs, h⟩ := h
  apply Smooth.ofLocalizationSpanTarget (algebraMap R S) s hs
  intro g
  have hstd : Algebra.IsStandardSmoothOfRelativeDimension n R
      (Localization.Away g.val) := by
    rw [← isStandardSmoothOfRelativeDimension_algebraMap]
    simpa only [← IsScalarTower.algebraMap_eq R S (Localization.Away g.val)] using
      h g.val g.property
  have : Algebra.IsStandardSmooth R (Localization.Away g.val) :=
    @Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n R
      (Localization.Away g.val) _ _ _ hstd
  rw [← IsScalarTower.algebraMap_eq R S (Localization.Away g.val), smooth_algebraMap]
  infer_instance

private theorem rankAtStalk_kaehler_away {R S : Type _} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.Smooth R S] (g : S) (q : PrimeSpectrum (Localization.Away g)) :
    Module.rankAtStalk Ω[Localization.Away g⁄R] q =
      Module.rankAtStalk Ω[S⁄R] (q.comap (algebraMap S (Localization.Away g))) := by
  rw [← Module.rankAtStalk_eq_of_equiv
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R S (Localization.Away g))]
  exact Module.rankAtStalk_baseChange (M := Ω[S⁄R]) q

private theorem rankAtStalk_of_locally_dimension {R S : Type _} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.Smooth R S] (n : ℕ)
    (h : Locally (IsStandardSmoothOfRelativeDimension n) (algebraMap R S))
    (p : PrimeSpectrum S) : Module.rankAtStalk Ω[S⁄R] p = n := by
  obtain ⟨s, hs, h⟩ := h
  obtain ⟨g, hg, hgp⟩ : ∃ g ∈ s, g ∉ p.asIdeal := by
    by_contra! hn
    have hle : Ideal.span s ≤ p.asIdeal := Ideal.span_le.mpr hn
    rw [hs, top_le_iff] at hle
    exact p.isPrime.ne_top hle
  have hp : p ∈ Set.range (PrimeSpectrum.comap (algebraMap S (Localization.Away g))) := by
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away g) g]
    exact hgp
  obtain ⟨q, rfl⟩ := hp
  have hstd : Algebra.IsStandardSmoothOfRelativeDimension n R (Localization.Away g) := by
    rw [← isStandardSmoothOfRelativeDimension_algebraMap]
    simpa only [← IsScalarTower.algebraMap_eq R S (Localization.Away g)] using h g hg
  have : Algebra.IsStandardSmooth R (Localization.Away g) :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  have : Nontrivial (Localization.Away g) := q.nontrivial
  rw [← rankAtStalk_kaehler_away g q, Module.rankAtStalk_eq_finrank_of_free]
  simp only [Pi.natCast_apply]
  have hr := Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential
    (R := R) (S := Localization.Away g) n
  rw [← Module.finrank_eq_rank] at hr
  exact_mod_cast hr

private theorem locally_dimension_of_rankAtStalk {R S : Type _} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.Smooth R S] (n : ℕ)
    (h : ∀ p : PrimeSpectrum S, Module.rankAtStalk Ω[S⁄R] p = n) :
    Locally (IsStandardSmoothOfRelativeDimension n) (algebraMap R S) := by
  classical
  have H (p : PrimeSpectrum S) : ∃ g : S, g ∉ p.asIdeal ∧
      Algebra.IsStandardSmoothOfRelativeDimension n R (Localization.Away g) := by
    obtain ⟨g, hgp, hstd⟩ :=
      Algebra.IsSmoothAt.exists_notMem_isStandardSmooth R p.asIdeal
    have hp : p ∈ Set.range (PrimeSpectrum.comap (algebraMap S (Localization.Away g))) := by
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away g) g]
      exact hgp
    obtain ⟨q, hq⟩ := hp
    have : Nontrivial (Localization.Away g) := q.nontrivial
    refine ⟨g, hgp, ?_⟩
    apply (Algebra.IsStandardSmoothOfRelativeDimension.iff_of_isStandardSmooth n).mpr
    have heq := rankAtStalk_kaehler_away (R := R) g q
    rw [hq, h p, Module.rankAtStalk_eq_finrank_of_free] at heq
    change Module.finrank (Localization.Away g) Ω[Localization.Away g⁄R] = n at heq
    rw [← Module.finrank_eq_rank]
    exact_mod_cast heq
  choose g hg hstd using H
  refine ⟨Set.range g, ?_, ?_⟩
  · by_contra hn
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hn
    exact hg ⟨m, hm.isPrime⟩ (hle (Ideal.subset_span ⟨⟨m, hm.isPrime⟩, rfl⟩))
  · rintro _ ⟨p, rfl⟩
    rw [← IsScalarTower.algebraMap_eq R S (Localization.Away (g p))]
    exact (isStandardSmoothOfRelativeDimension_algebraMap n).mpr (hstd p)

/-- Locally standard smooth maps of fixed relative dimension descend under faithfully flat
base change. Source: Stacks Project, Tags 02VL, 02G1 and 00T7 (2).
(blueprint: lem-pd-relative-smooth-dimension-codescent).

Proof: Let R -> S and R -> T be the maps in the codescent square, with R -> T faithfully
flat. The tensor product S -> T tensor_R S is faithfully flat. Smoothness of R -> S
follows from faithfully flat descent of smooth algebras (02VL, or its affine algebraic
proof). Around any prime of S choose a standard smooth presentation. Its differentials
are free of rank the presentation dimension, by 00T7 (2). Choose a prime upstairs over
this prime, possible by faithful flatness. Differentials commute with base change;
their fibre vector space at this prime is obtained by extending the residue field of
the original prime. Its dimension is n since the upstairs map is locally standard
smooth of dimension n. Extension of a field preserves the dimension of a finite
vector space, so the standard smooth chart downstairs has presentation dimension n.
The chart therefore witnesses locally standard smooth of relative dimension n at the
original prime. Such charts cover Spec S. If S is the zero ring, Spec S is empty and
local standard smoothness of every relative dimension is vacuous. -/
theorem locally_standardSmoothOfRelativeDimension_codescendsAlong_faithfullyFlat (n : ℕ) :
    CodescendsAlong (Locally (IsStandardSmoothOfRelativeDimension n)) FaithfullyFlat := by
  intro R S T U _ _ _ _ _ _ _ _ _ _ _ _ hff hdim
  have hsmU : Algebra.Smooth T U := smooth_of_locally_dimension n hdim
  have hsmS : Algebra.Smooth R S := by
    rw [← smooth_algebraMap]
    exact Smooth.codescendsAlong_faithfullyFlat hff (smooth_algebraMap.mpr hsmU)
  have : Algebra.IsPushout R T S U := Algebra.IsPushout.symm inferInstance
  have : Module.FaithfullyFlat S U := by
    rw [← faithfullyFlat_algebraMap_iff]
    exact FaithfullyFlat.isStableUnderBaseChange (R := R) (S := T) (R' := S) (S' := U) hff
  apply locally_dimension_of_rankAtStalk n
  intro p
  obtain ⟨q, rfl⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := S) (B := U) p
  rw [← Module.rankAtStalk_baseChange (M := Ω[S⁄R]) q,
    Module.rankAtStalk_eq_of_equiv (KaehlerDifferential.tensorKaehlerEquiv R T S U)]
  exact rankAtStalk_of_locally_dimension n hdim q

end RingHom
