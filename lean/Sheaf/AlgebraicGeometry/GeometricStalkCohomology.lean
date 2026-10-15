/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NZ
-/
module

public import Sheaf.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import Sheaf.AlgebraicGeometry.GeometricStalkAsPullback

/-!
# Geometric stalks of cohomology sheaves

Source: blueprint `sec-smooth-purity/sk-prop-sf-kunneth-ordinary/`
`lem-kun-stalks-of-cohomology.md` (blueprint: lem-kun-stalks-of-cohomology).
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Etale

/-- Cohomology commutes with pullback to a geometric point, viewed as an abelian group.
The cohomology sheaf of the pullback to `Spec Ω` is evaluated at its identity geometric
fibre, identifying sheaves on the separably closed point with abelian groups.
`mapDerivedCategory` applies the exact inverse image termwise and localizes; no
boundedness is imposed.

Source: blueprint `sec-smooth-purity/sk-prop-sf-kunneth-ordinary/`
`lem-kun-stalks-of-cohomology.md` (blueprint: lem-kun-stalks-of-cohomology).

Proof plan:
1. Represent `Q` by any cochain complex, as in `def-weil-pbc-derived-categories`, and
   express its cohomology as cycles modulo boundaries.
2. Exactness of geometric stalks (`prop-weil-pbc-geometric-stalks-exact`) preserves the
   short exact sequences defining cycles, boundaries and their quotient. Thus taking
   stalks commutes canonically with cohomology, without boundedness assumptions.
3. These comparisons commute with chain maps and invert quasi-isomorphisms, so descend
   to the derived category. Identify the termwise stalk with pullback to the point by
   `lem-kun-stalk-as-pullback` (the underived comparison is
   `upperStarCompUliftSheafFiberIso`), giving the displayed canonical identification. -/
theorem nonempty_geometricStalk_cohomology_iso
    {T : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ T)
    (Q : _root_.DerivedCategory (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (q : ℤ) :
    Nonempty
      ((((Scheme.pointSmallEtale t).ulift.{u + 1}).sheafFiber
        (A := AddCommGrpCat.{u + 1})).obj
          ((_root_.DerivedCategory.homologyFunctor _ q).obj Q) ≅
        (((Scheme.pointSmallEtale (𝟙 (Spec (.of Ω)))).ulift.{u + 1}).sheafFiber
          (A := AddCommGrpCat.{u + 1})).obj
            ((_root_.DerivedCategory.homologyFunctor _ q).obj
              ((upperStar AddCommGrpCat.{u + 1} t).mapDerivedCategory.obj Q))) := by
  sorry

end AlgebraicGeometry.Etale
