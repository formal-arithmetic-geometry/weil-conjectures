/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H3
-/
module

public import Sheaf.AlgebraicGeometry.SchemeDerivedBaseChangeMap
public import Sheaf.AlgebraicGeometry.ModuleBaseChangeMapOpenRestriction

/-! # Derived and ordinary exchange on the right-derived unit

Source: Stacks Project, Tag 08HY, mate description and derived adjunction compatibility.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory
namespace AlgebraicGeometry
noncomputable section

/-- Termwise ordinary exchange, with the composition identifications on homotopy categories.
Source: Stacks Project, Tag 08HY.
(blueprint: lem-pc-derived-base-change-unit-compatibility). -/
def moduleHomotopyBaseChange
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (p : X' ⟶ X)
    (h : p ≫ f = f' ≫ g)
    [(Scheme.Modules.tensorPullback g).Additive]
    [(Scheme.Modules.tensorPullback p).Additive] :
    (Scheme.Modules.pushforward f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (Scheme.Modules.tensorPullback g).mapHomotopyCategory (ComplexShape.up ℤ) ⟶
      (Scheme.Modules.tensorPullback p).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (Scheme.Modules.pushforward f').mapHomotopyCategory (ComplexShape.up ℤ) :=
  (Functor.mapHomotopyCategoryCompIso (Iso.refl
    (Scheme.Modules.pushforward f ⋙ Scheme.Modules.tensorPullback g))
    (ComplexShape.up ℤ)).hom ≫
  NatTrans.mapHomotopyCategory
    { app := Scheme.Modules.moduleBaseChangeMap f f' g p h
      naturality := fun _ _ a ↦
        Scheme.Modules.moduleBaseChangeMap_naturality f f' g p h a }
    (ComplexShape.up ℤ) ≫
  (Functor.mapHomotopyCategoryCompIso (Iso.refl
    (Scheme.Modules.tensorPullback p ⋙ Scheme.Modules.pushforward f'))
    (ComplexShape.up ℤ)).inv

/-- The pinned derived mate agrees with ordinary exchange before resolving the input.
There is no acyclicity, flatness, affine-base or cover hypothesis.
Source: Stacks Project, Tag 08HY, transposition of the mate; the derived adjunction
compatibility of Tag 09T5.
(blueprint: lem-pc-derived-base-change-unit-compatibility).

Proof: Transpose both composites under the pinned derived adjunction for f'.
The defining compatibility of that adjunction identifies a counit followed by
localization of an ordinary map with its ordinary adjoint followed by the
right-derived unit. Apply this first to p and then to f. The defining universal
property of the pinned composition comparisons replaces the successive left-derived
counits by the counit for the composite pullback. The commutativity of the square
identifies the composites. Naturality of the right-derived units moves these units
past the ordinary exchange, and the two adjunction triangle identities cancel the
remaining units and counits. The resulting ordinary adjoint is the pushforward of
the p-pullback unit followed by pushforward composition, precisely the definition
of moduleBaseChangeMap. Descend termwise to the homotopy categories and localize;
injectivity of the pinned Hom equivalence gives the equation. -/
theorem derivedBaseChange_unit_compatibility
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (p : X' ⟶ X)
    (h : p ≫ f = f' ≫ g)
    [(Scheme.Modules.tensorPullback g).Additive]
    [(Scheme.Modules.tensorPullback p).Additive]
    (D : HomotopyCategory X.Modules (ComplexShape.up ℤ)) :
    (derivedPullback g).map
        ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerivedFunctorUnit.app D) ≫
      schemeDerivedBaseChangeMap f f' g p h (DerivedCategory.Qh.obj D) ≫
      (schemeDerivedDirectImage f').map
        (((Classical.choose (Classical.choose_spec
          exists_derivedPullbackComposition.{u, w})) p).app D) =
    ((Classical.choose (Classical.choose_spec
        exists_derivedPullbackComposition.{u, w})) g).app
        (((Scheme.Modules.pushforward f).mapHomotopyCategory (ComplexShape.up ℤ)).obj D) ≫
      DerivedCategory.Qh.map ((moduleHomotopyBaseChange f f' g p h).app D) ≫
      (RingedSpace.moduleDirectImage f'.toLRSHom.toShHom).rightDerivedFunctorUnit.app
        (((Scheme.Modules.tensorPullback p).mapHomotopyCategory (ComplexShape.up ℤ)).obj D)
    := by sorry

end
end AlgebraicGeometry
