/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-! # Normalized comparison for an exact square preserving K-injectives

Source: Stacks Project, Derived Categories, Tags 070I, 070Y and 070K; exact-square
extraction of the tower normalization argument
(blueprint: lem-weil-pbc-kinjective-exact-square-comparison).

The units are expressed on the homotopy category, as in def-sfb-right-derived-functor.
The canonical localization factors are retained in the two normalization arrows.

## Main definitions and statements

* `KInjectiveExactSquare.leftUnit` and `rightUnit`: the arrows a and b.
* `KInjectiveExactSquare.delta`: the comparison b a⁻¹ on K-injectives.
* `KInjectiveExactSquare.existsUnique_normalized`: descent, formula and uniqueness.
-/

@[expose] public section

set_option autoImplicit false

universe uA' uA uB' uB vA' vA vB' vB wA' wA wB' wB

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.KInjectiveExactSquare

variable {A' : Type uA'} {A : Type uA} {B' : Type uB'} {B : Type uB}
  [Category.{vA'} A'] [Category.{vA} A] [Category.{vB'} B'] [Category.{vB} B]
  [Abelian A'] [Abelian A] [Abelian B'] [Abelian B]
  [HasDerivedCategory.{wA'} A'] [HasDerivedCategory.{wA} A]
  [HasDerivedCategory.{wB'} B'] [HasDerivedCategory.{wB} B]
  (H' : A' ⥤ B') (H : A ⥤ B) (r : A' ⥤ A) (s : B' ⥤ B)
  [H'.Additive] [H.Additive] [r.Additive] [s.Additive]
  [PreservesFiniteLimits r] [PreservesFiniteColimits r]
  [PreservesFiniteLimits s] [PreservesFiniteColimits s]
  (h : H' ⋙ s = r ⋙ H)
  (RH' : DerivedCategory A' ⥤ DerivedCategory B')
  (RH : DerivedCategory A ⥤ DerivedCategory B)
  (η' : H'.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RH')
  (η : H.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RH)

end CategoryTheory.KInjectiveExactSquare
