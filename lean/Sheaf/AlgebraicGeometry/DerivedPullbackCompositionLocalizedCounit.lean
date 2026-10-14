/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.DerivedCompositionCounitApex
public import Sheaf.AlgebraicGeometry.SchemeDerivedMateEvaluation

/-! # Localized underived counits and the derived composition comparison
Source: Stacks Project, Tags 0096, 079W and 0D5S.
(blueprint: lem-sc-derived-pullback-composition-localized-counit).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory
namespace AlgebraicGeometry
variable [∀ S : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
attribute [local irreducible] derivedPullback Scheme.Modules.tensorPullback
  DerivedCategory.Qh canonicalDerivedPullbackComposition

set_option maxHeartbeats 800000 in
-- The composite pushforward objects require dependent sheaf type comparisons.
/-- The left-derived lift equation followed by the localized underived composite
counit equals the pasted underived expression. This calculation involves no
right-derived unit or selected derived pullback/direct-image adjunction.
Source: Stacks Project, Tags 0096, 079W and 0D5S; steps 2 and 3 of
lem-sc-derived-pullback-composition-counit-normalization.
(blueprint: lem-sc-derived-pullback-composition-localized-counit).

Proof: The last chosen witness of exists_derivedPullbackComposition identifies
p.hom with the leftDerivedLift of the counits followed by the mapped inverse mate
of pushforwardComp. Its preceding witness says epsilon(fg) is a left-derived
counit. Apply Functor.leftDerived_fac_app and precompose the localized underived
counit. Expand the associator and whiskering components, removing identity maps.
At each degree, conjugateEquiv_counit_symm for the tensor adjunctions and
pushforwardComp.inv identifies the inverse mate followed by the (fg)-counit
with tensor pullback by f of the g-counit followed by the f-counit;
pushforwardComp.inv is the identity on sections. Map this natural equality
through the homotopy quotient and DerivedCategory.Qh. Naturality of epsilon(f)
at the g-counit moves Q of its tensor pullback past epsilon(f). Functor.map_comp
then combines the two Lf images and yields derivedCompositionCounitApex_eq.
This argument is valid for all complexes, without boundedness or K-flatness:
it is a universal-property and naturality calculation. Identity morphisms,
zero complexes, zero rings and empty schemes satisfy the same equations. -/
theorem derivedPullbackComposition_localized_counit
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (K : HomotopyCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace))
      (ComplexShape.up ℤ)) :
    let ε {A B : Scheme.{u}} (s : A ⟶ B) :=
      (Classical.choose (Classical.choose_spec exists_derivedPullbackComposition.{u, w})) s
    let b {A B : Scheme.{u}} (s : A ⟶ B) :=
      (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction s)).mapHomotopyCategory
        (ComplexShape.up ℤ)
    (canonicalDerivedPullbackComposition f g).hom.app
        (DerivedCategory.Qh.obj
          (((Scheme.Modules.pushforward (f ≫ g)).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj K)) ≫
      (ε (f ≫ g)).app
        (((Scheme.Modules.pushforward (f ≫ g)).mapHomotopyCategory
          (ComplexShape.up ℤ)).obj K) ≫
      DerivedCategory.Qh.map ((b (f ≫ g)).counit.app K) =
      derivedCompositionCounitApex f g K := by sorry

end AlgebraicGeometry
