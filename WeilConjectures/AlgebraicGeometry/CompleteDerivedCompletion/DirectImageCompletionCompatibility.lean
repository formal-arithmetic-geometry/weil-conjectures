/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompleteDerivedCompletion.CompletePullbackReduction
import WeilConjectures.AlgebraicGeometry.CompleteDerivedCompletion.DirectImageCompletionUnitSquare
import WeilConjectures.AlgebraicGeometry.CompleteDerivedCompletion.DirectImageReductionMapIsIso

/-!
# Reduction and completion compatibility for direct image
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale.CompleteDerivedCompletion

attribute [local instance] AdicCompletion.ringMonoidalObject AdicCompletion.ringCommutative
  AdicCompletion.modulesDerived

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The canonical reduction/direct-image mate. -/
def pushReductionMap : rpushModule l E f ⋙ red l E Y ⟶ red l E X ⋙ rpush l E f :=
  (mateEquiv (moduleAdjunction l E f) (towerAdjunction l E f)
    (.mk _ _ _ _ (pullReduction l E f).hom))

/-- The completion equation follows by applying the derived limit to the augmentation
square and the iterated-mate identity. -/
private theorem directImage_completion_compatibility_eq
    (χ : rpushModule l E f ⋙ dconstant l E Y ≅ dconstant l E X ⋙ rpush l E f)
    (hχ : χ.hom = (mateEquiv (moduleAdjunction l E f) (towerAdjunction l E f)
      (.mk _ _ _ _ (constantInterchange l E
        (CondensedRing.upperStar (DerivedNakayama.integerRing l E) f)).inv)))
    (hsquare : ∀ K : DerivedCategory (AdicCompletion.Modules l E X),
      (augmentation l E Y).app ((rpushModule l E f).obj K) ≫
          (pushReductionMap l E f).app K =
        χ.hom.app K ≫ (rpush l E f).map ((augmentation l E X).app K)) :
    ∀ K : DerivedCategory (AdicCompletion.Modules l E X),
      (rpushModule l E f).map ((kappa l E X).app K) ≫
          (pushLimitIso l E f).hom.app ((red l E X).obj K) =
        (kappa l E Y).app ((rpushModule l E f).obj K) ≫
          (rlim l E Y).map ((pushReductionMap l E f).app K) := by
  intro K
  let α := TwoSquare.mk (dconstant l E Y) (dpullModule l E f)
    (dpull l E f) (dconstant l E X)
    (constantInterchange l E
      (CondensedRing.upperStar (DerivedNakayama.integerRing l E) f)).inv
  have hi := iterated_mateEquiv_conjugateEquiv
    (moduleAdjunction l E f) (towerAdjunction l E f)
    (constantLimitAdjunction l E Y) (constantLimitAdjunction l E X) α
  have hu := unit_mateEquiv
    (constantLimitAdjunction l E X) (constantLimitAdjunction l E Y)
    (mateEquiv (moduleAdjunction l E f) (towerAdjunction l E f) α) K
  have hhu := congr_app hi ((dconstant l E X).obj K)
  rw [hhu] at hu
  have hnat := (pushLimitIso l E f).hom.naturality ((augmentation l E X).app K)
  have hs := congrArg ((rlim l E Y).map) (hsquare K)
  simp only [Functor.comp_map] at hnat
  simp only [Functor.map_comp] at hs
  dsimp [α] at hu
  have hχK := (congr_app hχ K).symm
  rw [hχK] at hu
  have hu' : (rpushModule l E f).map ((constantLimitAdjunction l E X).unit.app K) ≫
      (pushLimitIso l E f).hom.app ((dconstant l E X).obj K) =
    (constantLimitAdjunction l E Y).unit.app ((rpushModule l E f).obj K) ≫
      (rlim l E Y).map (χ.hom.app K) := by
    simpa [pushLimitIso, α] using hu
  simp only [kappa, NatTrans.comp_app, Functor.map_comp,
    Functor.whiskerRight_app, Category.assoc]
  dsimp [completion]
  rw [hnat, ← Category.assoc, hu', Category.assoc]
  change _ = (constantLimitAdjunction l E Y).unit.app _ ≫
    (rlim l E Y).map ((augmentation l E Y).app _) ≫
      (rlim l E Y).map ((pushReductionMap l E f).app K)
  rw [← hs]

/-- Reduction, completion-unit compatibility, and reconstruction for direct image:
assertions (2) and (3) of proposition-proper-base-change-complete-integral--1.
Source: Stacks Tags 099N, 0944. -/
theorem directImage_completion_compatibility :
    (∀ K : DerivedCategory (AdicCompletion.Modules l E X),
      IsIso ((pushReductionMap l E f).app K)) ∧
    (∀ K : DerivedCategory (AdicCompletion.Modules l E X),
      (rpushModule l E f).map ((kappa l E X).app K) ≫
          (pushLimitIso l E f).hom.app ((red l E X).obj K) =
        (kappa l E Y).app ((rpushModule l E f).obj K) ≫
          (rlim l E Y).map ((pushReductionMap l E f).app K)) ∧
    (∀ K : DerivedCategory (AdicCompletion.Modules l E X),
      IsDerivedComplete l E X K →
        IsDerivedComplete l E Y ((rpushModule l E f).obj K) ∧
        Nonempty ((rpushModule l E f).obj K ≅
          (rlim l E Y).obj ((rpush l E f).obj ((red l E X).obj K)))) := by
  have h := directImageCompletionUnitSquare l E f
  rcases h with ⟨χ, hχ, hsquare⟩
  have hpush (K : DerivedCategory (AdicCompletion.Modules l E X)) :
      IsIso ((pushReductionMap l E f).app K) := by
    simpa [pushReductionMap] using directImage_pushReductionMap_isIso l E f K
  have heq := directImage_completion_compatibility_eq l E f χ hχ hsquare
  refine ⟨hpush, heq, ?_⟩
  intro K hK
  have hcomp := completeDerivedCompletion l E Y Y (𝟙 Y)
  have hcriterion := hcomp.2.2.2.2.2.2.2.1
  have hkX := (completeDerivedCompletion l E X X (𝟙 X)).2.2.2.2.2.2.2.1 K
  letI : IsIso ((kappa l E X).app K) := hkX.mp hK
  have hmap : IsIso ((rpushModule l E f).map ((kappa l E X).app K)) := inferInstance
  letI : IsIso ((rpushModule l E f).map ((kappa l E X).app K)) := hmap
  letI : IsIso ((pushLimitIso l E f).hom.app ((red l E X).obj K)) := inferInstance
  letI : IsIso ((pushReductionMap l E f).app K) := hpush K
  letI : IsIso ((rlim l E Y).map ((pushReductionMap l E f).app K)) := inferInstance
  have hky : IsIso ((kappa l E Y).app ((rpushModule l E f).obj K)) := by
    have hc : IsIso ((kappa l E Y).app ((rpushModule l E f).obj K) ≫
        (rlim l E Y).map ((pushReductionMap l E f).app K)) := by
      rw [← heq K]
      infer_instance
    letI := hc
    exact IsIso.of_isIso_comp_right
      ((kappa l E Y).app ((rpushModule l E f).obj K))
      ((rlim l E Y).map ((pushReductionMap l E f).app K))
  constructor
  · exact (hcriterion ((rpushModule l E f).obj K)).mpr hky
  · let e₁ : (rpushModule l E f).obj K ≅
        (rpushModule l E f).obj ((rlim l E X).obj ((red l E X).obj K)) :=
      asIso ((rpushModule l E f).map ((kappa l E X).app K))
    let e₂ : (rpushModule l E f).obj ((rlim l E X).obj ((red l E X).obj K)) ≅
        (rlim l E Y).obj ((rpush l E f).obj ((red l E X).obj K)) :=
      asIso ((pushLimitIso l E f).hom.app ((red l E X).obj K))
    exact ⟨e₁ ≪≫ e₂⟩

end AlgebraicGeometry.ProEtale.CompleteDerivedCompletion
