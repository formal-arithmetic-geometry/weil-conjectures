/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Realization.DiagonalRealizationPullback
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Completed.DiagonalCompletedPushSquare
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Completed.CompletedCoefficientOrdinarySquare
import WeilConjectures.CategoryTheory.ProEtaleCoefficients.EquivalenceAdjunctionComparisonSupplement
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsCanonicalAdjunctionSupplement

/-! # Ordinary completed realization and inverse image

Source: blueprint coefficient changes, paragraph (3).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local irreducible] diagonalCompletedCoefficientMap
  Scheme.purTwistZlCompletionOfUniverses

private def completedPushIso (l : ℕ) [Fact l.Prime]
    {X S : Scheme.{u}} (f : X ⟶ S) :
    diagonalTracePush l f ≅ Scheme.proEtaleRingModuleDirectImage f
      (Scheme.purTwistZlCompletion S l) (Scheme.purTwistZlCompletion X l)
      (asIso (diagonalCompletedCoefficientMap l f)) :=
  NatIso.ofComponents (fun M ↦
    (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun _ ↦ Iso.refl _) (by intros; rfl)))
    (by intros; ext U x; rfl)

/-- The inverse mate of the normalized ordinary direct-image square compares
completed realization with geometric inverse image over arbitrary schemes.

Source: blueprint coefficient changes (3), realization of exact inverse image.
(blueprint: lem-diagonal-ordinary-realization-pullback).

Proof: the completed direct image agrees sectionwise with the right adjoint of
completed pullback. Transport the ordinary realization square through this
sectionwise comparison. Both realization functors are equivalences, so its
inverse mate is invertible. The mate theorem also supplies the full Hom equation;
this fixes the pullback comparison uniquely without a Noetherian hypothesis. -/
theorem diagonalOrdinaryRealization_pullback (l : ℕ) [Fact l.Prime]
    {X S : Scheme.{u}} (f : X ⟶ S)
    (eX : CompletedRealization l X) (eS : CompletedRealization l S) :
    ∃ (d : diagonalTracePush l f ≅ Scheme.proEtaleRingModuleDirectImage f
        (Scheme.purTwistZlCompletion S l) (Scheme.purTwistZlCompletion X l)
        (asIso (diagonalCompletedCoefficientMap l f)))
      (s : CompletedOrdinarySquare l f eX eS)
      (e : diagonalRealizationPull l f ⋙ eX.F ≅ eS.F ⋙
        CondensedRing.upperStar (Profinite.continuousMapRingObj.{u} ℤ_[l]) f),
      (∀ (M : DiagonalCompleted l X) (U : S.ProEtᵒᵖ)
        (x : ((diagonalTracePush l f).obj M).val.obj U),
        HEq ((d.hom.app M).val.app U x) x) ∧
      ∀ (M : DiagonalCompleted l S) (N : DiagonalCompleted l X)
        (a : (diagonalRealizationPull l f).obj M ⟶ N),
        (CondensedRing.upperStarLowerStarAdjunction
          (Profinite.continuousMapRingObj.{u} ℤ_[l]) f).homEquiv _ _
            (e.inv.app M ≫ eX.F.map a) =
          eS.F.map ((Scheme.proEtaleRingModuleAdjunction f
            (Scheme.purTwistZlCompletion S l) (Scheme.purTwistZlCompletion X l)
            (asIso (diagonalCompletedCoefficientMap l f))).homEquiv _ _ a) ≫
          eS.F.map (d.inv.app N) ≫ s.ordinary.hom.app N := by
  obtain ⟨s⟩ := completedCoefficientOrdinarySquare_exists l f eX eS
  let adj := Scheme.proEtaleRingModuleAdjunction f
    (Scheme.purTwistZlCompletion S l) (Scheme.purTwistZlCompletion X l)
    (asIso (diagonalCompletedCoefficientMap l f))
  let t := Functor.isoWhiskerRight (completedPushIso l f).symm eS.F ≪≫ s.ordinary
  obtain ⟨e, _, _, he, _, _⟩ := exists_equivalenceAdjunctionComparison
    eS.F.asEquivalence eX.F.asEquivalence adj
    (CondensedRing.upperStarLowerStarAdjunction
      (Profinite.continuousMapRingObj.{u} ℤ_[l]) f) t
  refine ⟨completedPushIso l f, s, e, ?_, ?_⟩
  · intro M U x
    rfl
  · intro M N a
    simpa only [Functor.asEquivalence, adj, t, Iso.trans_hom,
      Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
      NatTrans.comp_app, Iso.symm_hom, Category.assoc] using he M N a

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
