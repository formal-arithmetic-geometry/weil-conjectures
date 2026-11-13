/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.FourCornersSupplement
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedRlimFunctor
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCompletion
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedTowerPullbackSupplement
public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedPullbackInterface
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import WeilConjectures.AlgebraicGeometry.Completed.Koszul.CompletedKoszulQuotientComparison

/-!
# Completed pullback through strict completed-coefficient towers

Source: Stacks Tag 099N.

## Main definitions

- `AlgebraicGeometry.Scheme.AdicCoefficientDatum.completedPull`
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)

/-- The quotient-tower unit and the intrinsic Koszul unit give the same complete inputs. -/
theorem AdicCoefficientDatum.towerComplete_iff_intrinsic (T : Scheme.{t})
    (K : d.derived T) :
    d.TowerComplete T K ↔
      ∀ (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal),
        ∀ (C : CochainComplex (reductionModules T (d.completedRing T)) ℤ)
          (e : DerivedCategory.Q.obj C ≅ K),
          IsDerivedCompleteIntrinsic T d r a ha K C e := by
  classical
  have hcomparison (r : ℕ) (a : Fin r → A)
      (ha : Ideal.span (Set.range a) = d.ideal)
      (C : CochainComplex (reductionModules T (d.completedRing T)) ℤ)
      (e : DerivedCategory.Q.obj C ≅ K) :
      IsDerivedCompleteIntrinsic T d r a ha K C e ↔ d.TowerComplete T K := by
    obtain ⟨c, hc⟩ := completedKoszulQuotientComparison T d r a ha K C e
    change IsIso (intrinsicCompletionUnit T d r a ha K C e) ↔ IsIso (d.completionUnit T K)
    change intrinsicCompletionUnit T d r a ha K C e ≫ c.hom = d.completionUnit T K at hc
    rw [← hc]
    exact (isIso_comp_right_iff _ c.hom).symm
  constructor
  · intro h r a ha C e
    exact (hcomparison r a ha C e).mpr h
  · intro h
    obtain ⟨r, a, ha⟩ := Submodule.fg_iff_exists_fin_generating_family.mp d.finitelyGenerated
    exact (hcomparison r a ha (DerivedCategory.Q.objPreimage K)
      (DerivedCategory.Q.objObjPreimageIso K)).mp
        (h r a ha _ _)

/-- Completed pullback is precisely Rlim of tower pullback of the strict reduction tower.
The formula extends to ambient inputs.
Source: Stacks 099N. -/
def AdicCoefficientDatum.completedPull {U V : Scheme.{t}} (f : U ⟶ V) :
    d.derived V ⥤ d.derived U :=
  completedReductionTower V d ⋙ d.towerPull f ⋙ completedRlim U (d.completedRing U)

/-- The canonical ordinary-to-completed comparison: constant-tower unit followed by
the image of the actual strict quotient augmentation. -/
def AdicCoefficientDatum.ordinaryToCompleted {U V : Scheme.{t}} (g : U ⟶ V)
    (K : d.derived V) : (d.pull g).obj K ⟶ (d.completedPull g).obj K :=
  (d.constantRlimAdjunction U).unit.app ((d.pull g).obj K) ≫
    (completedRlim U (d.completedRing U)).map
      ((d.derivedConstantPullbackIso g).inv.app K ≫
        (d.towerPull g).map ((completedReductionAugmentation d V).app K))

end AlgebraicGeometry.Scheme
