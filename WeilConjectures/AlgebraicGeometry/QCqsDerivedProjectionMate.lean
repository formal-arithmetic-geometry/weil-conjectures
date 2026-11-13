/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

import WeilConjectures.AlgebraicGeometry.QCqsProjectionMateAffineDescent
import WeilConjectures.AlgebraicGeometry.QCqsProjectionMateShiftedUnit
import WeilConjectures.AlgebraicGeometry.QCqsProjectionMateAffineLocus
import WeilConjectures.AlgebraicGeometry.AffineQCohDerivedEquivalence
import WeilConjectures.CategoryTheory.DerivedModuleFreeGeneration
import WeilConjectures.AlgebraicGeometry.AffineDerivedPullbackTensorTilde
import WeilConjectures.AlgebraicGeometry.DerivedDirectImageOpenRestriction
import WeilConjectures.AlgebraicGeometry.DerivedDirectImagePreservesDirectSums
import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorQCoh
import WeilConjectures.AlgebraicGeometry.DerivedTensorQCohClosure
import WeilConjectures.AlgebraicGeometry.DerivedTensorRightCoproducts
import WeilConjectures.AlgebraicGeometry.ProjectionFormulaLocality

/-! # The quasi-coherent derived projection mate

## References

* [Stacks Project, Tag 08EU](https://stacks.math.columbia.edu/tag/08EU)
* [Stacks Project, Tag 0A9Q](https://stacks.math.columbia.edu/tag/0A9Q)
-/

@[expose] public section

universe u w
open CategoryTheory MonoidalCategory
namespace AlgebraicGeometry

/-- The projection mate for quasi-coherent derived objects is invertible. -/
theorem qcqsDerivedProjectionMate_isIso (X Y : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (p : derivedPullback f ⊣ schemeDerivedDirectImage f)
    (t : tensor (schemeDerivedCategory Y) ⋙ derivedPullback f ≅
      (derivedPullback f).prod (derivedPullback f) ⋙ tensor (schemeDerivedCategory X))
    (M : schemeDerivedQCohCategory Y) (L : schemeDerivedQCohCategory X) :
    IsIso (p.homEquiv (M.obj ⊗ (schemeDerivedDirectImage f).obj L.obj)
      ((derivedPullback f).obj M.obj ⊗ L.obj)
        (t.hom.app (M.obj, (schemeDerivedDirectImage f).obj L.obj) ≫
          (𝟙 ((derivedPullback f).obj M.obj) ⊗ₘ p.counit.app L.obj))) := by
  classical
  apply qcqsProjectionMate_of_affine ?_ X Y f p t M L
  intro A _ Z _ _ _ _ g _ _ q s N E
  let : HasDerivedCategory.{u + 1} (ModuleCat.{u} A) :=
    HasDerivedCategory.standard (ModuleCat.{u} A)
  obtain ⟨e, _, _, htri, hunit⟩ := exists_affineQCohDerivedEquivalence A
  let P : ObjectProperty (DerivedCategory (ModuleCat.{u} A)) := fun K ↦
    ∀ (B : schemeDerivedQCohCategory (Spec (.of A))) (n : ℤ),
      Nonempty ((e.functor.obj (K⟦n⟧)).obj ≅ B.obj) →
      IsIso (q.homEquiv (B.obj ⊗ (schemeDerivedDirectImage g).obj E.obj)
        ((derivedPullback g).obj B.obj ⊗ E.obj)
          (s.hom.app (B.obj, (schemeDerivedDirectImage g).obj E.obj) ≫
            (𝟙 ((derivedPullback g).obj B.obj) ⊗ₘ q.counit.app E.obj)))
  obtain ⟨hcop, htriangle, hretract⟩ :=
    qcqsProjectionMate_affineLocus_closed A Z g q s E e htri
  have hgen : ∀ m : ℤ, P (((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
      (ModuleCat.of A (ULift.{0} A)))⟦m⟧) :=
    by
      intro m B n hB
      obtain ⟨hB⟩ := hB
      let a : ModuleCat.of A (ULift.{0} A) ≅ ModuleCat.of A A :=
        (ULift.moduleEquiv : ULift.{0} A ≃ₗ[A] A).toModuleIso
      let d := ((shiftFunctorAdd (DerivedCategory (ModuleCat.{u} A)) m n).symm.app
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
            (ModuleCat.of A (ULift.{0} A)))) ≪≫
        (shiftFunctor (DerivedCategory (ModuleCat.{u} A)) (m + n)).mapIso
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).mapIso a)
      obtain ⟨hO⟩ := hunit (m + n)
      apply qcqsProjectionMate_shiftedUnit_isIso Z (Spec (.of A)) g q s
        B.obj E.obj (m + n)
      exact ⟨hB.symm ≪≫
        (schemeDerivedQCohProperty (Spec (.of A))).ι.mapIso (e.functor.mapIso d) ≪≫ hO⟩
  have hK : P (e.inverse.obj N) :=
    derivedModuleFreeGeneration.{u, 0, u + 1} A (e.inverse.obj N)
      P hgen hcop htriangle hretract
  apply hK N 0
  exact ⟨(schemeDerivedQCohProperty (Spec (.of A))).ι.mapIso
    (e.functor.mapIso ((shiftFunctorZero _ ℤ).app (e.inverse.obj N)) ≪≫
      e.counitIso.app N)⟩

end AlgebraicGeometry
