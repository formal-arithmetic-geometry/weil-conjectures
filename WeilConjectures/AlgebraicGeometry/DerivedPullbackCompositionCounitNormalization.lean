/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCompositionCounitApex
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedMateEvaluation
import WeilConjectures.AlgebraicGeometry.DerivedPullbackCompositionLocalizedCounit
import all WeilConjectures.AlgebraicGeometry.DerivedDirectImagePastedCounitNormalization

/-! # Counit calculations for pullback composition

## References

* Stacks Project, Tags 079W, 0D5S and 0D5T
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory
namespace AlgebraicGeometry
-- Compare the recorded functors through their interfaces, without unfolding the
-- chosen resolutions or adjunction witnesses during statement elaboration.
-- Open the pinned adjunction explicitly only at its defining Hom equation.
attribute [local irreducible] Scheme.Modules.tensorPullback
  CategoryTheory.Functor.rightDerivedFunctor CategoryTheory.Functor.rightDerivedFunctorUnit
  DerivedCategory.Qh canonicalDerivedPullbackComposition schemeHomPullbackAdjunction
variable [∀ S : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]

set_option maxHeartbeats 500000 in
-- The selected adjunctions and composite sheaf instances need a larger budget.
/-- The chosen pullback comparison and composite direct-image unit transpose to the
explicit pasted underived counits (Stacks, Tags 079W, 0D5S and 0D5T). -/
theorem derivedPullbackComposition_counit_normalization
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (K : HomotopyCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace))
      (ComplexShape.up ℤ)) :
    (canonicalDerivedPullbackComposition f g).hom.app
        (((RingedSpace.moduleDirectImage (f ≫ g).toLRSHom.toShHom).mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).obj K) ≫
      (derivedPullback (f ≫ g)).map
        ((RingedSpace.moduleDirectImage (f ≫ g).toLRSHom.toShHom).rightDerivedFunctorUnit.app K) ≫
      (schemeHomPullbackAdjunction (f ≫ g)).counit.app (DerivedCategory.Qh.obj K) =
      derivedCompositionCounitApex f g K
    := by
  classical
  let ε {A B : Scheme.{u}} (s : A ⟶ B) :=
    (Classical.choose (Classical.choose_spec exists_derivedPullbackComposition.{u, w})) s
  let b {A B : Scheme.{u}} (s : A ⟶ B) :=
    (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction s)).mapHomotopyCategory
      (ComplexShape.up ℤ)
  let a {A B : Scheme.{u}} (s : A ⟶ B) := schemeHomPullbackAdjunction.{u, w} s
  have hc (M : HomotopyCategory
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ))
      (J : HomotopyCategory
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ))
      (t : ((Scheme.Modules.tensorPullback (f ≫ g)).mapHomotopyCategory
        (ComplexShape.up ℤ)).obj M ⟶ J) :
      (a (f ≫ g)).homEquiv (DerivedCategory.Qh.obj M) (DerivedCategory.Qh.obj J)
        ((ε (f ≫ g)).app M ≫ DerivedCategory.Qh.map t) =
      (DerivedCategory.Qh
        (C := SheafOfModules.{u} (moduleRings Z.toRingedSpace))).map
          ((b (f ≫ g)).homEquiv M J t) ≫
        (RingedSpace.moduleDirectImage (f ≫ g).toLRSHom.toShHom).rightDerivedFunctorUnit.app J := by
    dsimp only [a]
    delta schemeHomPullbackAdjunction
    exact Classical.choose_spec (exists_schemeDerivedAdjunction (f ≫ g)
      (hAdd := (Classical.choose exists_derivedPullbackComposition) (f ≫ g))
      (ε (f ≫ g)) ((Classical.choose (Classical.choose_spec
        (Classical.choose_spec exists_derivedPullbackComposition))) (f ≫ g))) M J t
  have he := counit_of_normalization (b (f ≫ g)) (a (f ≫ g))
    (DerivedCategory.Qh (C := SheafOfModules.{u} (moduleRings Z.toRingedSpace)))
    (DerivedCategory.Qh (C := SheafOfModules.{u} (moduleRings X.toRingedSpace)))
    (ε (f ≫ g))
    (RingedSpace.moduleDirectImage (f ≫ g).toLRSHom.toShHom).rightDerivedFunctorUnit hc K
  dsimp only [a] at he
  exact (congrArg
    (fun t ↦ (canonicalDerivedPullbackComposition f g).hom.app
      (DerivedCategory.Qh.obj
        (((Scheme.Modules.pushforward (f ≫ g)).mapHomotopyCategory
          (ComplexShape.up ℤ)).obj K)) ≫ t) he).trans
    (derivedPullbackComposition_localized_counit.{u, w} f g K)

end AlgebraicGeometry
