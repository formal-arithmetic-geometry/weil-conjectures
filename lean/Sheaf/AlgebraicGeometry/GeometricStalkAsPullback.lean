/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Sheaf.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.AlgebraicGeometry.GeometricPointPullbackStalk

/-!
# Geometric stalks as inverse images

Source: blueprint sec-smooth-purity/sk-prop-sf-kunneth-ordinary,
lemma lem-kun-stalk-as-pullback (blueprint: lem-kun-stalk-as-pullback).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- A geometric stalk is inverse image to the geometric point, identifying sheaves on
`Spec Ω` with abelian groups by global sections. The same identification holds for the
functors induced termwise on the unbounded derived categories.

Source: blueprint sec-smooth-purity/sk-prop-sf-kunneth-ordinary,
lemma lem-kun-stalk-as-pullback (blueprint: lem-kun-stalk-as-pullback).

Proof: By lem-weil-pbc-geometric-point-pullback-stalk, global sections on `Spec Ω` give
an equivalence with abelian groups, and the sections of the inverse image of `F`
identify naturally with its geometric stalk. The stalk is exact by
prop-weil-pbc-geometric-stalks-exact. Thus inverse image and global sections are exact
here, act termwise on complexes and preserve quasi-isomorphisms. The natural sheaf
isomorphism passes to the localization at quasi-isomorphisms, giving the derived
isomorphism. Exactness also identifies the cohomology of a stalk complex with the
stalk of the corresponding cohomology sheaf. -/
theorem geometricStalk_as_pullback (T : Scheme.{u}) (Ω : Type u)
    [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T) :
    Nonempty (AlgebraicGeometry.Etale.upperStar AddCommGrpCat.{u + 1} t ⋙
      (sheafSections (Spec (.of Ω)).smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (op (Etale.mk (𝟙 (Spec (.of Ω))))) ≅
      (pointSmallEtale t).sheafFiber) ∧
    Nonempty ((AlgebraicGeometry.Etale.upperStar AddCommGrpCat.{u + 1} t).mapDerivedCategory ⋙
      AlgebraicGeometry.Etale.rightDerivedGlobalSections AddCommGrpCat.{u + 1}
        (Spec (.of Ω)) ≅
      (@Functor.mapDerivedCategory _ _ _ _ _ _ _ _
        (((pointSmallEtale t).ulift.{u + 1}).sheafFiber (A := AddCommGrpCat.{u + 1}))
        (((pointSmallEtale t).ulift.{u + 1}).sheafFiber_additive) _ _)) := by
  sorry

end AlgebraicGeometry.Scheme
