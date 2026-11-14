/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOrdinaryModuleComposition
import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOrdinaryComparisonNormalization
import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOrdinaryCartesianEvaluation
import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOrdinarySectionEvaluation
import WeilConjectures.AlgebraicGeometry.VaryingRing.OrdinarySquareComparison.VaryingRingOrdinarySquarePasting

/-!
# Ordinary coefficient evaluation of the clopen comparison

Source: Zheng, Construction 4.1 and Lemma 4.10; Stacks Project, Tags 09AE and 0F7B.
The evaluation used here first takes an ordinary system component, then makes a
constant tower concentrated in degree zero. Its faithfulness concerns ordinary
system morphisms only.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.VaryingRing
variable (R : ℕ → CommRingCat.{u + 1}) (φ : ∀ n : ℕ, R (n + 1) ⟶ R n)
attribute [local instance 2000] WeilConjectures.SemilinearSections.sequenceSmall
  StrictTower.towers_hasDerivedCategory Scheme.proEtaleRingModules_hasDerivedCategory
attribute [local irreducible] ordinaryRealization ordinaryPullComparison ordinaryOpenComparison
  moduleAlpha moduleGComp StrictTower.alpha Functor.leftAdjoint

private theorem ordinaryClopenComparison_factor (n : ℕ) :
    OrdinaryClopenComparison R φ n (ordinaryPullComparison R φ n)
      (ordinaryOpenComparison R φ n) := by
  intro V W S T k r p i _ _ _ _ _ _ h
  have hf : moduleAlpha R φ k r p i h =
      (moduleBeta R φ (pullback.snd p i) (pullback.fst p i) i p
        pullback.condition.symm (IsPullback.of_hasPullback p i).flip).hom ≫
          moduleSectionArrow R φ k r p i h := by
    delta moduleAlpha moduleSectionArrow
    rfl
  have hh := OrdinarySquareComparison.trans
    (ordinaryPullComparison R φ n V S r) (ordinaryPullComparison R φ n W T p)
    (ordinaryOpenComparison R φ n V W k) (ordinaryOpenComparison R φ n S T i)
    (ordinaryPullComparison R φ n _ S (pullback.snd p i))
    (ordinaryOpenComparison R φ n _ W (pullback.fst p i))
    _ _ _ _
    (ordinaryCartesianEvaluation R φ n (pullback.snd p i)
      (pullback.fst p i) i p pullback.condition.symm
        (IsPullback.of_hasPullback p i).flip)
    (ordinarySectionEvaluation R φ n k r p i h)
  simpa only [hf, strictAlpha_factorization] using hh

/-- Ordinary evaluation preserves the specified inverse-image and open-extension
comparisons and the single-square clopen arrow.
Source: Zheng, Construction 4.1 and Lemma 4.10; Stacks 09AE and 0F7B. -/
theorem ordinaryClopenEvaluation (n : ℕ) :
    ∃ (gIso : OrdinaryPullComparison R φ n) (jIso : OrdinaryOpenComparison R φ n),
      OrdinaryPullComposition R φ n gIso ∧ OrdinaryOpenComposition R φ n jIso ∧
        OrdinaryClopenComparison R φ n gIso jIso := by
  have hn := ordinaryComparisonNormalization R φ n
  exact ⟨ordinaryPullComparison R φ n, ordinaryOpenComparison R φ n, hn.1,
    hn.2, ordinaryClopenComparison_factor R φ n⟩

end AlgebraicGeometry.ProEtale.VaryingRing
