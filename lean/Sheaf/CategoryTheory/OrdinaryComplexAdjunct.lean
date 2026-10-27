/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P7
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Adjunction.Basic

/-! # The ordinary adjunct of a complex map from degree zero

Source: Stacks Project, Tags 072W and 0DVC.
(blueprint: def-weil-pbc-ordinary-complex-adjunct).
-/

@[expose] public section

set_option autoImplicit false

namespace CategoryTheory

/-- The ordinary termwise adjunct of a chain map out of a complex in degree zero.
Source: Stacks Project, Tags 072W and 0DVC, the ordinary adjunction unit formula.
(blueprint: def-weil-pbc-ordinary-complex-adjunct).

This is the actual composite of the single of the ordinary unit, the inverse
single-functor comparison for R, and the image of c. Its data is constructed directly.
The definition is irreducible so homology computations can use its declared source
and target without repeatedly normalizing the three complex maps. -/
@[irreducible] noncomputable def ordinaryComplexAdjunct
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (L : C ⥤ D) (R : D ⥤ C) [L.Additive] [R.Additive] (adj : L ⊣ R)
    (A : C) (J : CochainComplex D ℤ)
    (c : (CochainComplex.singleFunctor D 0).obj (L.obj A) ⟶ J) :
    (CochainComplex.singleFunctor C 0).obj A ⟶
      (R.mapHomologicalComplex (.up ℤ)).obj J :=
  (CochainComplex.singleFunctor C 0).map (adj.unit.app A) ≫
    (R.mapCochainComplexSingleFunctor 0).inv.app _ ≫
    (R.mapHomologicalComplex (.up ℤ)).map c

private theorem ordinaryComplexAdjunct_eq
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (L : C ⥤ D) (R : D ⥤ C) [L.Additive] [R.Additive] (adj : L ⊣ R)
    (A : C) (J : CochainComplex D ℤ)
    (c : (CochainComplex.singleFunctor D 0).obj (L.obj A) ⟶ J) :
    ordinaryComplexAdjunct L R adj A J c =
      (CochainComplex.singleFunctor C 0).map (adj.unit.app A) ≫
        (R.mapCochainComplexSingleFunctor 0).inv.app _ ≫
        (R.mapHomologicalComplex (.up ℤ)).map c := by
  unfold ordinaryComplexAdjunct
  rfl

end CategoryTheory
