/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T3
-/
module

public import Sheaf.AlgebraicGeometry.DerivedGlobalGerm
public import WeilConjectures.SixFunctors.BaseChange.Square

/-! # Underived global germ and exchange

Source: Stacks Project, Tags 095T, 01F8 and 08J6.
-/

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Etale
open Scheme
attribute [local instance] GrothendieckTopology.Point.sheafFiber_additive
noncomputable local instance : AB5OfSize.{u, u} AddCommGrpCat.{u + 1} :=
  AB5OfSize_shrink.{u, u, u + 1, u + 1} _

/-- Global germs identify underived exchange with pullback of global sections.
Source: Stacks Project, etale-cohomology.tex, Tag 095T, final map-on-stalks paragraph;
cohomology.tex, Tag 01F8.
(blueprint: lem-weil-pbc-underived-global-germ-exchange)

Proof: Evaluate both transformations on a sheaf and a global section. The inverse of
`lowerStarCompGlobalSectionsIso` views the section on the terminal object over Y.
The pulled germ is its germ at the image of t, transported to the inverse-image stalk.
Expand the exchange as the mate of the pullback-square isomorphism. The adjunction
triangle identities cancel the counit and the unit on the Y side. What remains is the
unit into g'_*g'^* applied to the original section, followed by the terminal-object
identification over X' and its germ over Y'. Expand the stalk identification into
`sheafPullbackIso`, `sheafFiberComapIso` and `pointSmallEtaleComapIso`; their unit-germ
formulas give this equality already on each representative in the stalk colimit.
The terminal-section identifications give exactly the three remaining components of b.
This uses only commutativity of the square and works for separably closed Ω. -/
theorem underivedGlobalGerm_exchange
    {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (f' : X' ⟶ Y')
    (g : Y' ⟶ Y) (g' : X' ⟶ X) (sq : CommSq g' f' f g)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ Y') :
    let B := AddCommGrpCat.{u + 1}
    let F := lowerStar B f
    let F' := lowerStar B f'
    let G := upperStar B g
    let G' := upperStar B g'
    let R := lowerStar B g'
    let H := Sheaf.Γ X.smallEtaleTopology B
    let S := (pointSmallEtale t).sheafFiber
    let a : H ⟶ G' ⋙ F' ⋙ S :=
      (lowerStarCompGlobalSectionsIso B f).inv ≫
        Functor.whiskerLeft F (pulledGlobalGerm g t) ≫
        (Functor.associator F G S).inv ≫
        Functor.whiskerRight (baseChangeMap B sq) S ≫
        (Functor.associator G' F' S).hom
    let b : H ⟶ G' ⋙ F' ⋙ S :=
      (Functor.leftUnitor H).inv ≫
        Functor.whiskerRight (upperStarLowerStarAdjunction B g').unit H ≫
        (Functor.associator G' R H).hom ≫
        Functor.whiskerLeft G' (lowerStarCompGlobalSectionsIso B g').hom ≫
        Functor.whiskerLeft G' (lowerStarCompGlobalSectionsIso B f').inv ≫
        Functor.whiskerLeft G' (Functor.whiskerLeft F' (globalGerm t))
    a = b := by sorry

end AlgebraicGeometry.Etale
