/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothCoefficientArrows
import all WeilConjectures.AlgebraicGeometry.Reduction.ReductionDirectImage
import all WeilConjectures.AlgebraicGeometry.Etale.ProEtale.EtaleProEtaleExceptionalObjectComparison
import WeilConjectures.AlgebraicGeometry.SupportedEtaleTensorOrigin.SupportedEtaleTensorOrigin

/-! # Quotient scalar extension on the intrinsic finite-Tor domain

Source: latest blueprint, sk-lem-sp-reduction, first paragraph, and flat-model lemma.
(blueprint: lem-pur-quotient-intrinsic-ctf).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.FiniteSmoothPurity

/-- Quotient extension preserves intrinsic bounded constructibility and finite
Tor amplitude on an arbitrary scheme; no prime-invertibility hypothesis is used.
Source: latest blueprint, sk-lem-sp-reduction.proof.md, first paragraph;
scalarExtensionFunctor_preserves_constructible_tor, Stacks 06YY and 094H.
(blueprint: lem-pur-quotient-intrinsic-ctf).

Proof: transport fixed coefficient modules to modules over the actual constant
ring sheaf by the canonical exact section-action equivalence. Its derived
monoidal comparison identifies the finite-Tor test and transports constructible
cohomology stratum by stratum, preserving finite geometric stalks. The canonical
scalar functor is identified with scalarExtensionFunctor by uniqueness of left
adjoints to restriction of scalars. Apply its constructibility and Tor preservation
theorem, using the ell^r and ell^m annihilators. Finite homology support follows
from the finite-Tor interval; conversely, a finite subset of Z is contained in an
ordered bounded interval. Transport back along the exact equivalence and its
homology isomorphisms. These identifications yield precisely IsCtf for proScalar,
including its test on every degree-zero fixed module. This uses neither a global
etale origin nor Noetherianity or invertibility of ell on T. Zero inputs and equal
levels are included. -/
theorem quotientIntrinsicCtf
    (ell : ℕ) [Fact ell.Prime] (r m : ℕ) (_hm : 1 ≤ m) (hmr : m ≤ r)
    (T : Scheme.{u}) (K : proCategory (coefficient ell r) T)
    (hK : IsCtf (coefficient ell r) T K) :
    IsCtf (coefficient ell m) T
      ((proScalar (FiniteReduction.quotient ell hmr) T).obj K) := by
  classical
  let A := FiniteReduction.Ring.{u} ell r
  let B := FiniteReduction.Ring.{u} ell m
  let φ : A →+* B := (ZMod.castHom (pow_dvd_pow ell hmr) (ZMod (ell ^ m))).ulift
  have hbounded : _root_.DerivedCategory.TStructure.t.bounded K := by
    obtain ⟨a, b, _, hv⟩ := hK.2.1
    exact ⟨⟨a, (_root_.DerivedCategory.isGE_iff K a).mpr
      (fun i hi ↦ hv i (Or.inl hi))⟩,
      ⟨b, (_root_.DerivedCategory.isLE_iff K b).mpr
        (fun i hi ↦ hv i (Or.inr hi))⟩⟩
  have hnative : ProEtale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (coefficient ell r)) T K := by
    refine ⟨ProEtale.DerivedCategory.boundedConstructible_of_homology _ hbounded
      (fun i ↦ ?_), ?_⟩
    · exact ProEtale.exists_isConstructibleSheaf_iso_comparisonUpperStar_obj _
        ((ProEtale.fixed_constructible_iff _ T _).mp (hK.1 i))
    · obtain ⟨a, b, _, ht⟩ := hK.2.2
      exact ⟨a, b, ht⟩
  have hann (n : ℕ) : ∃ k : ℕ, ∀ x : FiniteReduction.Ring.{u} ell n,
      (ell ^ k) • x = 0 := by
    refine ⟨n, fun x ↦ ?_⟩
    rw [← Nat.cast_smul_eq_nsmul (FiniteReduction.Ring ell n),
      CharP.cast_eq_zero, zero_smul]
  have hgood := (ProEtale.reductionGood_realization_iff T A K).mpr hnative
  have hscalar := ProEtale.reductionGood_scalar ell (hann r) (hann m) φ T _ hgood
  have htarget := ProEtale.reductionGood_iso
    ((ProEtale.SupportedEtaleTensorOrigin.scalarPresentation φ T).app K) hscalar
  have hn := (ProEtale.reductionGood_realization_iff T B _).mp htarget
  have hc := ProEtale.DerivedCategory.boundedConstructible_le_boundedConstructibleIntrinsic _ hn.1
  change IsCtf (ULift.{u + 1} B) T
    ((ProEtale.SupportedEtaleTensorOrigin.fixedScalar φ T).obj K)
  refine ⟨fun i ↦ (ProEtale.fixed_constructible_iff _ T _).mpr (hc.2 i), ?_, ?_⟩
  · obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hc.1
    refine ⟨min a b, b, min_le_right _ _, fun i hi ↦ ?_⟩
    rcases hi with hi | hi
    · exact (_root_.DerivedCategory.isGE_iff _ a).mp ha i
        (lt_of_lt_of_le hi (min_le_left _ _))
    · exact (_root_.DerivedCategory.isLE_iff _ b).mp hb i hi
  · obtain ⟨a, b, ht⟩ := hn.2
    exact ⟨min a b, max a b, min_le_max,
      ht.mono (min_le_left _ _) (le_max_right _ _)⟩

end AlgebraicGeometry.Etale.FiniteSmoothPurity
