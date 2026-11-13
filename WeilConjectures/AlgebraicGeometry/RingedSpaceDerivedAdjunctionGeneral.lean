/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import WeilConjectures.Algebra.Homology.KFlatPullback
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import WeilConjectures.AlgebraicGeometry.RingedSpaceTensorPullbackUnderived
import WeilConjectures.AlgebraicGeometry.RingedSpaceTensorPullbackAbsolute
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import WeilConjectures.Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction

/-!
# Derived pullback/direct-image adjunction for ringed spaces

## References

* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
* [Stacks Project, Tag 06YJ](https://stacks.math.columbia.edu/tag/06YJ)
-/

@[expose] public section

universe u wX wY

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.RingedSpace

/-- The total left derived tensor pullback is left adjoint to derived direct image.
The additive functor `P` is specified on both objects and morphisms as inverse image
followed by extension of scalars along the adjoint structure map. Its total left
derived functor `L`, with comparison `ε`, is computed on K-flat complexes.
The adjunction includes its natural bifunctorial Hom equivalences. -/
theorem derivedModulePullback_adjunction
    {X Y : RingedSpace.{u}}
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y))]
    (g : X ⟶ Y) :
    ∃ (P : SheafOfModules.{u} (moduleRings Y) ⥤ SheafOfModules.{u} (moduleRings X))
      (h : ∀ M : SheafOfModules.{u} (moduleRings Y),
        P.obj M = SheafOfModules.changeOfRings.{u, u, u}
          (CochainComplex.tensorPullbackRingMap g.hom.base X.sheaf Y.sheaf ⟨g.hom.c⟩)
          (TopCat.Sheaf.inverseImageModule g.hom.base Y.sheaf M))
      (_ : ∀ {M N : SheafOfModules.{u} (moduleRings Y)} (a : M ⟶ N),
        P.map a = eqToHom (h M) ≫ SheafOfModules.changeOfRingsHom.{u, u, u}
          (CochainComplex.tensorPullbackRingMap g.hom.base X.sheaf Y.sheaf ⟨g.hom.c⟩)
          (TopCat.Sheaf.inverseImageModule g.hom.base Y.sheaf M)
          (TopCat.Sheaf.inverseImageModuleMap g.hom.base Y.sheaf M a) ≫
          eqToHom (h N).symm)
      (_ : P.Additive),
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
        Nonempty (L ⊣ derivedModuleDirectImage g) := by
  obtain ⟨P, h, hm, hP, ⟨adj⟩⟩ := exists_tensorModulePullback g
  let := hP
  obtain ⟨L, ε, hL, hK, hcomp⟩ :=
    exists_absolute_leftDerived_tensorModulePullback g P h hm
  let := hL
  let := hcomp (derivedModuleDirectImage g)
  let β := (moduleDirectImage g).rightDerivedFunctorUnit
  let : (derivedModuleDirectImage g ⋙ L).IsRightDerivedFunctor
      (Functor.whiskerRight β L ≫ (Functor.associator _ _ _).hom)
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (moduleRings X))
        (ComplexShape.up ℤ)) :=
    (HomotopyCategory.KInjectives.localizerMorphism
      (SheafOfModules.{u} (moduleRings X)))
      |>.isRightDerivedFunctor_comp_of_isRightDerivabilityStructure
        _ (fun I ↦ (HomotopyCategory.KInjectives.localizerMorphism_derives
          _).isIso_of_isRightDerivedFunctor _ I) _
  exact ⟨P, h, hm, hP, L, ε, hL, hK,
    ⟨(adj.mapHomotopyCategory (ComplexShape.up ℤ)).derived
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (moduleRings Y))
        (ComplexShape.up ℤ))
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (moduleRings X))
        (ComplexShape.up ℤ)) ε β⟩⟩

end AlgebraicGeometry.RingedSpace
