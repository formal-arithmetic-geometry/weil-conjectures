/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic

/-!
# The complex-level comparison for a derived pullback

Transport the specified homotopy-level counit along the canonical quotient isomorphisms.
This construction is independent of tensor preservation and its derived comparison theorem.
Source: Stacks Project, Tags 06YY and 07A4.
-/

@[expose] public section

universe u v u' v' wA wB

open CategoryTheory

namespace CategoryTheory

variable {A : Type u} [Category.{v} A] [Abelian A]
  {B : Type u'} [Category.{v'} B] [Abelian B]
  (L : A ⥤ B) [L.Additive]

/-- Transport the homotopy left-derived comparison to the complex localization Q.
Source: Stacks 06YY and 07A4
(blueprint: def-weil-pbc-derived-pullback-complex-comparison). -/
noncomputable def derivedPullbackComplexComparison
    [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
    (LF : DerivedCategory A ⥤ DerivedCategory B)
    (epsilon : DerivedCategory.Qh ⋙ LF ⟶
      L.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (P : CochainComplex A ℤ) :
    LF.obj (DerivedCategory.Q.obj P) ⟶ DerivedCategory.Q.obj
      ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) :=
  LF.map ((DerivedCategory.quotientCompQhIso A).inv.app P) ≫
    epsilon.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj P) ≫
      DerivedCategory.Qh.map ((L.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app P) ≫
        (DerivedCategory.quotientCompQhIso B).hom.app
          ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)

end CategoryTheory
