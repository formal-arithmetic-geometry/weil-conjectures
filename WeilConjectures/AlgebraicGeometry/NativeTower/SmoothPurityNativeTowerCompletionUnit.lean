/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityReductionTowerData
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityTowerReconstructionData
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
public import WeilConjectures.Algebra.Homology.System.SystemScalarGenerators
public import WeilConjectures.Algebra.Homology.System.SystemScalarCoherence
public import WeilConjectures.CategoryTheory.SixFunctors.ResolvingDerivedAdjunction
public import WeilConjectures.ProperBaseChange.RingedToposDerivedPushforwardComposition
public import WeilConjectures.CategoryTheory.Cochain.CochainHomotopyComparison
public import WeilConjectures.AlgebraicGeometry.Picard.KFlatResolutionIndependentCoefficients
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution

import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityReductionTowerData
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityTowerReconstructionData
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
import WeilConjectures.Algebra.Homology.System.SystemScalarGenerators
import WeilConjectures.Algebra.Homology.System.SystemScalarCoherence
import WeilConjectures.CategoryTheory.SixFunctors.ResolvingDerivedAdjunction
import WeilConjectures.ProperBaseChange.RingedToposDerivedPushforwardComposition
import WeilConjectures.CategoryTheory.Cochain.CochainHomotopyComparison
import WeilConjectures.AlgebraicGeometry.Picard.KFlatResolutionIndependentCoefficients
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.PrincipalQuotientCompletion.PrincipalQuotientCompletionModel
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralReduction
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.Algebra.Homology.BifunctorShift
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.RegularQuotientCone.RegularQuotientConeBasic
import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import WeilConjectures.CategoryTheory.RingedPowerTorsion.RingedPowerTorsionLimitComplete
import WeilConjectures.AlgebraicGeometry.ProEtaleCountableProductsExact

/-! # The actual ell-completion unit on a native uniformizer-complete object

Source: current sk-lem-sp-tower proof, first paragraph and current plan step 2.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.NativeTower

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})
  (D : SpCoefficientTowersAbelian l E T) (R : SpReductionTower l E T D)

attribute [local instance] SpReductionTower.additive

private theorem section_products_exact :
    HasExactLimitsOfShape (Discrete ℕ) (spIntegralSectionModules l E T) := by
  let A := spIntegralSectionModules l E T
  let S := spIntegralSectionRing l E T
  let : HasCountableProducts A := (Scheme.ProEt.countableProducts_exact.{u, u, 0} T S).1
  have hprod := (Scheme.ProEt.countableProducts_exact.{u, u, 0} T S).2.2
  have : (CategoryTheory.Limits.lim (J := Discrete ℕ) (C := A)).PreservesEpimorphisms := by
    constructor
    intro F G f hf
    have h : Epi (Limits.Pi.map (fun n : ℕ ↦ f.app ⟨n⟩)) :=
      hprod ℕ _ _ _ (fun n ↦ inferInstance)
    have heq : CategoryTheory.Limits.lim.map f = (Pi.isoLimit F).inv ≫
        Limits.Pi.map (fun n : ℕ ↦ f.app ⟨n⟩) ≫ (Pi.isoLimit G).hom := by
      apply limit.hom_ext
      rintro ⟨n⟩
      simp
    rw [heq]
    infer_instance
  exact hasExactLimitsOfShape_of_preservesEpi A (Discrete ℕ)

private theorem unit_isIso_iff_section (L : Limit l E T D R) (K : Integral l E T) :
    IsIso ((redLimitAdjunction l E T D R L).unit.app K) ↔
      IsIso (L.adjunction.unit.app ((sectionEquivalence l E T).functor.obj K)) := by
  change IsIso (((sectionEquivalence l E T).toAdjunction.comp L.adjunction).unit.app K) ↔ _
  rw [Adjunction.comp_unit_app]
  change IsIso ((sectionEquivalence l E T).unitIso.hom.app K ≫
    (sectionEquivalence l E T).inverse.map
      (L.adjunction.unit.app ((sectionEquivalence l E T).functor.obj K))) ↔ _
  constructor
  · intro h
    have := h
    have : IsIso ((sectionEquivalence l E T).inverse.map
        (L.adjunction.unit.app ((sectionEquivalence l E T).functor.obj K))) :=
      IsIso.of_isIso_comp_left ((sectionEquivalence l E T).unitIso.hom.app K) _
    exact isIso_of_reflects_iso _ (sectionEquivalence l E T).inverse
  · intro h
    have := h
    infer_instance

/-- Native uniformizer completeness makes the actual ell-tower adjunction unit
invertible. This is a comparison of the specified augmented completion maps, and
contains no constructibility assumption.
Source: current blueprint sk-lem-sp-tower, first paragraph; Stacks 0940
(blueprint: lem-sp-native-tower-completion-unit).

Proof: represent the native uniformizer-completion augmentation by its augmented
Roos complex on a K-flat representative. Its rows are strict quotient modules killed
by pi^(j+1), hence by ell^(j+1), since ell=u*pi^e and e is positive. Pass through the
exact section/internal module equivalence and use exact countable module products on
the replete pro-etale site. Apply the ringed power-torsion limit theorem with t=ell
and row exponent j+1. It makes the canonical ell-completion unit at this pi-complete
limit invertible; the theorem retains the tensor units and signed double-Roos
coordinates. The normalized coefficient comparison identifies the principal ell
quotients with the finite rings used by R. Ordinary tensor generators and L's
representative normalization identify that augmented comparison with the actual
redLimitAdjunction unit. Finally transport across the given pi-completion isomorphism
and use naturality of the unit. No K-flat replacement is claimed to retain torsion. -/
theorem unit_isIso_of_complete (L : Limit l E T D R) (K : Integral l E T)
    (hK : Complete l E T K) :
    IsIso ((redLimitAdjunction l E T D R L).unit.app K) := by
  obtain ⟨M, e, he⟩ := principal_completion_comparison l E T D R L
  have := section_products_exact l E T
  obtain ⟨U, hU, ⟨eK⟩⟩ := complete_torsion_roos l E T K hK
  obtain ⟨_, _, _, hcomplete⟩ := RingedPowerTorsion.limit_complete.{u + 1, u, u + 1, u + 2}
    (spIntegralSectionRing l E T) (ellSection l E T) (ell_regular l E T)
  have hM := ((hcomplete U (fun n ↦ n + 1) (fun n ↦ Nat.le_add_left 1 n) hU).1 M).1
  have : IsIso (eK.hom ≫ M.unit.app (DerivedCategory.Q.obj (roosF.obj U))) := by
    infer_instance
  have hn := M.unit.naturality eK.hom
  have hsection : IsIso (M.unit.app ((sectionEquivalence l E T).functor.obj K)) := by
    have : IsIso (M.unit.app ((sectionEquivalence l E T).functor.obj K) ≫
        M.completion.map eK.hom) := by
      rw [← hn]
      exact inferInstance
    exact IsIso.of_isIso_comp_right _ (M.completion.map eK.hom)
  apply (unit_isIso_iff_section l E T D R L K).mpr
  have : IsIso (L.adjunction.unit.app ((sectionEquivalence l E T).functor.obj K) ≫
      e.hom.app ((sectionEquivalence l E T).functor.obj K)) := by
    rw [he]
    exact hsection
  exact IsIso.of_isIso_comp_right _
    (e.hom.app ((sectionEquivalence l E T).functor.obj K))

end AlgebraicGeometry.ProEtale.NativeTower
