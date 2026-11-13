/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import WeilConjectures.Algebra.Homology.KFlatPullback

public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import WeilConjectures.Algebra.Homology.DerivedChangeOfRings
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.AlgebraicGeometry.RingedSpaceTensorPullbackAbsoluteAux

/-! # Absolute left derived tensor pullback via K-flat resolutions

## References

* [Stacks Project, Tag 06YJ](https://stacks.math.columbia.edu/tag/06YJ)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
* [Stacks Project, Tag 06XN](https://stacks.math.columbia.edu/tag/06XN)
-/

@[expose] public section

universe u wX wY

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.RingedSpace

/-- The concrete tensor pullback has a left derived comparison computed on K-flat
complexes, and this comparison remains left derived after postcomposition. -/
theorem exists_absolute_leftDerived_tensorModulePullback
    {X Y : RingedSpace.{u}}
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y))]
    (g : X ⟶ Y)
    (P : SheafOfModules.{u} (moduleRings Y) ⥤ SheafOfModules.{u} (moduleRings X))
    (h : ∀ M : SheafOfModules.{u} (moduleRings Y),
      P.obj M = SheafOfModules.changeOfRings.{u, u, u}
        (CochainComplex.tensorPullbackRingMap g.hom.base X.sheaf Y.sheaf ⟨g.hom.c⟩)
        (TopCat.Sheaf.inverseImageModule g.hom.base Y.sheaf M))
    (hm : ∀ {M N : SheafOfModules.{u} (moduleRings Y)} (a : M ⟶ N),
      P.map a = eqToHom (h M) ≫ SheafOfModules.changeOfRingsHom.{u, u, u}
        (CochainComplex.tensorPullbackRingMap g.hom.base X.sheaf Y.sheaf ⟨g.hom.c⟩)
        (TopCat.Sheaf.inverseImageModule g.hom.base Y.sheaf M)
        (TopCat.Sheaf.inverseImageModuleMap g.hom.base Y.sheaf M a) ≫
        eqToHom (h N).symm)
    [P.Additive] :
    ∃ (L : DerivedCategory (SheafOfModules.{u} (moduleRings Y)) ⥤
        DerivedCategory (SheafOfModules.{u} (moduleRings X)))
      (ε : DerivedCategory.Qh ⋙ L ⟶
        P.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh),
      L.IsLeftDerivedFunctor ε
        (HomotopyCategory.quasiIso (SheafOfModules.{u} (moduleRings Y))
          (ComplexShape.up ℤ)) ∧
      (∀ K : CochainComplex (SheafOfModules.{u} (moduleRings Y)) ℤ,
        K.IsKFlatTensor → IsIso
          (ε.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K))) ∧
      ∀ H : DerivedCategory (SheafOfModules.{u} (moduleRings X)) ⥤
          DerivedCategory (SheafOfModules.{u} (moduleRings Y)),
        (L ⋙ H).IsLeftDerivedFunctor
          ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight ε H)
          (HomotopyCategory.quasiIso (SheafOfModules.{u} (moduleRings Y))
            (ComplexShape.up ℤ)) := by
  obtain ⟨L, ε, hL, hK⟩ := exists_tensorPullback_leftDerived g P h hm
  exact ⟨L, ε, hL, hK, leftDerived_tensorPullback_absolute g P h hm L ε hL hK⟩

end AlgebraicGeometry.RingedSpace
