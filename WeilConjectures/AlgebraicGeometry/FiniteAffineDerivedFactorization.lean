/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.DirectImageAlgebraDerivedCategory
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import WeilConjectures.AlgebraicGeometry.DerivedRHomAlgebraModule
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HasSheafComposeForgetCommRingCat

/-! # Derived pushforward through the direct-image algebra

## References

* [Stacks Project, Tag 0AVW](https://stacks.math.columbia.edu/tag/0AVW)
-/

@[expose] public section

universe u wX wY wA

open CategoryTheory

namespace AlgebraicGeometry

private lemma moduleDirectImage_restrictScalars_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace f) ⋙
      SheafOfModules.restrictScalars
        (R := moduleRings Y.toRingedSpace)
        (R' := moduleRings (directImageAlgebraSpace f))
        ⟨Functor.whiskerRight f.c (forget₂ CommRingCat RingCat)⟩ =
      RingedSpace.moduleDirectImage f.toLRSHom.toShHom := rfl

/-- Scalar restriction of the algebra-valued derived pushforward is the scheme pushforward.
(Stacks, Tag 0AVW.) -/
theorem finite_affine_derived_factorization {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsFinite f]
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [HasDerivedCategory.{wA} (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace f)))]
    : Nonempty (RingedSpace.derivedModuleDirectImage (toDirectImageAlgebraSpace f) ⋙
        (SheafOfModules.restrictScalars
          (R := moduleRings Y.toRingedSpace)
          (R' := moduleRings (directImageAlgebraSpace f))
          ⟨Functor.whiskerRight f.c (forget₂ CommRingCat RingCat)⟩).rightDerivedFunctor ≅
          schemeDerivedDirectImage f) := by
  let F := RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace f)
  let S := SheafOfModules.restrictScalars
    (R := moduleRings Y.toRingedSpace)
    (R' := moduleRings (directImageAlgebraSpace f))
    ⟨Functor.whiskerRight f.c (forget₂ CommRingCat RingCat)⟩
  let instB : HasDerivedCategory.{wA} (SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology Y) (forget₂ CommRingCat RingCat)).obj
        ((Under.mk (⟨f.c⟩ : Y.sheaf ⟶
          (TopCat.Sheaf.pushforward CommRingCat f.base).obj X.sheaf)).right))) :=
    inferInstanceAs (HasDerivedCategory.{wA}
      (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace f))))
  have : CategoryTheory.Limits.PreservesFiniteLimits S :=
    sheafAlgebraRestrictScalars_preservesFiniteLimits Y
      (Under.mk (⟨f.c⟩ : Y.sheaf ⟶
        (TopCat.Sheaf.pushforward CommRingCat f.base).obj X.sheaf))
  have : CategoryTheory.Limits.PreservesFiniteColimits S :=
    sheafAlgebraRestrictScalars_preservesFiniteColimits Y
      (Under.mk (⟨f.c⟩ : Y.sheaf ⟶
        (TopCat.Sheaf.pushforward CommRingCat f.base).obj X.sheaf))
  let e : F ⋙ S ≅ RingedSpace.moduleDirectImage f.toLRSHom.toShHom :=
    eqToIso (moduleDirectImage_restrictScalars_eq f)
  let eS : S.rightDerivedFunctor ≅ S.mapDerivedCategory :=
    S.rightDerivedFunctorIsoMapDerivedCategory
  let eComp : (F ⋙ S).rightDerivedFunctor ≅ F.rightDerivedFunctor ⋙ S.mapDerivedCategory :=
    Functor.rightDerivedFunctorCompMapDerivedCategoryIso F S
  let eF : (F ⋙ S).rightDerivedFunctor ≅ schemeDerivedDirectImage f :=
    Functor.rightDerivedFunctorNatIso e
  exact ⟨Functor.isoWhiskerLeft F.rightDerivedFunctor eS ≪≫ eComp.symm ≪≫ eF⟩

end AlgebraicGeometry
