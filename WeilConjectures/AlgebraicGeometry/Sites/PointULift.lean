/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Basic

/-!
# Raising a point of a site a universe

A point `Φ : J.Point.{w}` of a site can be raised to a point `Φ.ulift : J.Point.{max w w'}`
with the same sheaf fibres (`CategoryTheory.GrothendieckTopology.Point.ulift`,
`CategoryTheory.GrothendieckTopology.Point.uliftSheafFiberIso`). For a scheme `S`, the raised
geometric points at algebraic closures of the residue fields form a conservative family
(`AlgebraicGeometry.Scheme.isConservativeFamilyOfPoints_ulift_pointSmallEtale`). This file
packages these facts.
-/

@[expose] public section

universe w' w v v' u u'

open CategoryTheory Limits

namespace CategoryTheory.GrothendieckTopology.Point

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- Blueprint `lemma-openclosed-point-ulift`: Raising a point a universe

Composing the fibre functor of a point `Φ` of a site with `uliftFunctor` gives a point
`Φ.ulift` whose fibre functor on `A`-valued sheaves is isomorphic to that of `Φ`. -/
lemma nonempty_ulift_sheafFiber_iso (Φ : Point.{w} J) (A : Type u') [Category.{v'} A]
    [HasColimitsOfSize.{max w w', max w w'} A] :
    letI : HasColimitsOfSize.{w, w} A := hasColimitsOfSizeShrink.{w, w, w', w'} A
    Nonempty ((Φ.ulift.{w'}).sheafFiber (A := A) ≅ Φ.sheafFiber (A := A)) :=
  ⟨Φ.uliftSheafFiberIso A⟩

end CategoryTheory.GrothendieckTopology.Point

namespace AlgebraicGeometry.Scheme

/-- Blueprint `lemma-openclosed-point-ulift`: Raising a point a universe

For a scheme `S : Scheme.{u}`, the geometric points `S.uliftPointSmallEtale s` of the small étale
site, at an algebraic closure of the residue field of `s`, raised from `Type u` to
`Type (u + 1)`, have the same sheaf fibres as the original geometric points, and they form a
conservative family of points. -/
lemma nonempty_uliftPointSmallEtale_sheafFiber_iso_and_isConservativeFamilyOfPoints
    (S : Scheme.{u}) (A : Type u') [Category.{v'} A] [HasColimitsOfSize.{u + 1, u + 1} A] :
    letI : HasColimitsOfSize.{u, u} A := hasColimitsOfSizeShrink.{u, u, u + 1, u + 1} A
    (∀ s : S, Nonempty ((S.uliftPointSmallEtale s).sheafFiber (A := A) ≅
      (pointSmallEtale (S.algClosurePoint s)).sheafFiber (A := A))) ∧
    (ObjectProperty.ofObj S.uliftPointSmallEtale).IsConservativeFamilyOfPoints :=
  ⟨fun s ↦ (pointSmallEtale (S.algClosurePoint s)).nonempty_ulift_sheafFiber_iso A,
    S.isConservativeFamilyOfPoints_ulift_pointSmallEtale⟩

end AlgebraicGeometry.Scheme
