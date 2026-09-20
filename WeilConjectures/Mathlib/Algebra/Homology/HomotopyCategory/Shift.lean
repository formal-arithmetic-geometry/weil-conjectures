/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.Shift

/-!
# Compatibility with the shift of the functors on cochain complexes

An additive functor `F : C ⥤ D` induces a functor
`F.mapHomologicalComplex (ComplexShape.up ℤ)` on cochain complexes which commutes with
the shift. In this file we record that the natural transformations relating these induced
functors also commute with the shift: this holds for
`CategoryTheory.NatTrans.mapHomologicalComplex`, and hence for
`CategoryTheory.NatIso.mapHomologicalComplex` and for the identity and composition
isomorphisms `CategoryTheory.Functor.mapHomologicalComplexIdIso` and
`CategoryTheory.Functor.mapHomologicalComplexCompIso`.
-/

@[expose] public section

open CategoryTheory Category Limits

namespace CategoryTheory.NatTrans

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {C D E : Type*} [Category C] [Category D] [Category E]
  [Preadditive C] [Preadditive D] [Preadditive E]

instance commShift_mapHomologicalComplex {F G : C ⥤ D} [F.Additive] [G.Additive] (α : F ⟶ G) :
    NatTrans.CommShift (NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)) ℤ := by
  constructor
  intro a
  ext K i
  dsimp
  simp

instance commShift_mapHomologicalComplexNatIso_hom {F G : C ⥤ D} [F.Additive] [G.Additive]
    (α : F ≅ G) :
    NatTrans.CommShift (NatIso.mapHomologicalComplex α (ComplexShape.up ℤ)).hom ℤ := by
  constructor
  intro a
  ext K i
  dsimp
  simp

instance commShift_mapHomologicalComplexIdIso_hom :
    NatTrans.CommShift (Functor.mapHomologicalComplexIdIso C (ComplexShape.up ℤ)).hom ℤ := by
  constructor
  intro a
  ext K i
  dsimp
  simp

instance commShift_mapHomologicalComplexCompIso_hom {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E}
    (e : F ⋙ G ≅ H) [F.Additive] [G.Additive] [H.Additive] :
    NatTrans.CommShift (Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℤ)).hom ℤ := by
  constructor
  intro a
  ext K i
  dsimp
  simp [Functor.commShiftIso_comp_hom_app]

end CategoryTheory.NatTrans
