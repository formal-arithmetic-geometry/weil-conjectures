/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.DerivedCompositionCounitApex

/-! # Localized homotopy counit pasting
Source: Stacks Project, Tags 0096, 0097 and 079W.
(blueprint: lem-sc-tensor-pullback-composition-homotopy-counit).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory
namespace AlgebraicGeometry
variable [∀ S : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]

set_option maxHeartbeats 800000 in
-- The mapped adjunctions use both module-category presentations.
/-- Localizing the underived inverse-mate identity and applying naturality pastes counits.
Source: Stacks Project, Tags 0096, 0097 and 079W.
(blueprint: lem-sc-tensor-pullback-composition-homotopy-counit).
Proof: At every module apply conjugateEquiv_counit_symm to afg and ag.comp af
and pushforwardComp.inv. The inverse comparison is the identity on sections,
so its pullback is an identity. The composite adjunction counit is pullback
of the g-counit followed by the f-counit. Apply this degreewise on a complex
representing K and pass to the homotopy quotient. Apply Qh to the resulting
identity and use its preservation of composition. Naturality of epsilonF
at the g-counit moves its localized image into derivedPullback f. Its
functoriality combines that image with epsilon(g), giving the concrete apex
construction equation. The counits here are the already recorded choices.
No composite derived adjunction, derived unit or derived comparison is used.
Identities, zero complexes and empty schemes
satisfy the same equations; there is no cancellation or flatness assumption. -/
theorem tensorPullbackComposition_localized_homotopy_counit
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (K : HomotopyCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace))
      (ComplexShape.up ℤ)) :
    let epsilon {A B : Scheme.{u}} (s : A ⟶ B) :=
      (Classical.choose (Classical.choose_spec exists_derivedPullbackComposition.{u, w})) s
    let a {A B : Scheme.{u}} (s : A ⟶ B) :=
      Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction s)
    let b {A B : Scheme.{u}} (s : A ⟶ B) :=
      (a s).mapHomotopyCategory (ComplexShape.up ℤ)
    let c := (conjugateIsoEquiv (a (f ≫ g)) ((a g).comp (a f))).symm
      (Scheme.Modules.pushforwardComp f g).symm
    let M := ((Scheme.Modules.pushforward (f ≫ g)).mapHomotopyCategory
      (ComplexShape.up ℤ)).obj K
    ((derivedPullback f).map ((epsilon g).app M) ≫
      (epsilon f).app
        (((Scheme.Modules.tensorPullback g).mapHomotopyCategory (ComplexShape.up ℤ)).obj M) ≫
      (DerivedCategory.Qh (C := SheafOfModules.{u} (moduleRings X.toRingedSpace))).map
        ((Functor.mapHomotopyCategoryCompIso c (ComplexShape.up ℤ)).hom.app M)) ≫
      (DerivedCategory.Qh (C := SheafOfModules.{u} (moduleRings X.toRingedSpace))).map
        ((b (f ≫ g)).counit.app K) = derivedCompositionCounitApex f g K := by sorry

end AlgebraicGeometry
