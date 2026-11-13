/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DirectImageAlgebraDerivedCategory
public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
import WeilConjectures.AlgebraicGeometry.FiniteSheafHomAffineAdjoint
import WeilConjectures.AlgebraicGeometry.DerivedRHomAlgebraModule
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HasSheafComposeForgetCommRingCat

/-! # Right adjoint to derived restriction along the direct-image algebra

## References

* Stacks Project, Duality for Schemes, Tags 0BV0, 0BV1 and 0AX3.
-/

@[expose] public section

universe u wY wA

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The auxiliary adjunction required by finite derived duality: an adjoint to derived
restriction of algebra scalars. (Stacks, Tag 0BV0) -/
theorem finiteRestriction_derived_rightAdjoint
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [HasDerivedCategory.{wA}
      (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace f)))] :
    ∃ (H : DerivedCategory (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ⥤
      DerivedCategory (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace f)))),
      Nonempty ((SheafOfModules.restrictScalars
        (R := moduleRings Y.toRingedSpace)
        (R' := moduleRings (directImageAlgebraSpace f))
        ⟨Functor.whiskerRight f.c (forget₂ CommRingCat RingCat)⟩).rightDerivedFunctor ⊣ H) := by
  classical
  let B : Y.CommAlgebraSheaf := Under.mk
    (show Y.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat f.base).obj X.sheaf from ⟨f.c⟩)
  let F := SheafOfModules.restrictScalars
    (R := moduleRings Y.toRingedSpace)
    (R' := moduleRings (directImageAlgebraSpace f))
    ⟨Functor.whiskerRight f.c (forget₂ CommRingCat RingCat)⟩
  let : HasDerivedCategory.{wA} (SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology Y)
        (forget₂ CommRingCat RingCat)).obj B.right)) := by
    change HasDerivedCategory.{wA}
      (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace f)))
    infer_instance
  have : PreservesFiniteLimits F := sheafAlgebraRestrictScalars_preservesFiniteLimits Y B
  have : PreservesFiniteColimits F := sheafAlgebraRestrictScalars_preservesFiniteColimits Y B
  obtain ⟨_, _, _, _, _, H, _, T, t, adj, _⟩ := exists_affine_derivedSheafHom_adjunction f
  let : Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
      (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) T := ⟨t⟩
  let e : T ≅ F.mapDerivedCategory := Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
    (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    T F.mapDerivedCategory (Iso.refl _)
  exact ⟨H, ⟨adj.ofNatIsoLeft (e ≪≫ F.rightDerivedFunctorIsoMapDerivedCategory.symm)⟩⟩

end AlgebraicGeometry
