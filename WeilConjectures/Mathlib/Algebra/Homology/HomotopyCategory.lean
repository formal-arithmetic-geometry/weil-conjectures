/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory

/-!
# The functor induced on homotopy categories by the identity functor

The functor `(𝟭 V).mapHomotopyCategory c` induced on homotopy categories by the identity
functor of a preadditive category `V` is isomorphic to the identity functor
(`CategoryTheory.Functor.mapHomotopyCategoryIdIso`). This is the homotopy category
counterpart of Mathlib's `CategoryTheory.Functor.mapHomologicalComplexIdIso`.

This material is destined for `Mathlib/Algebra/Homology/HomotopyCategory.lean`, next to
`CategoryTheory.Functor.mapHomotopyCategoryCompIso`.
-/

@[expose] public section

universe v u

open CategoryTheory

namespace CategoryTheory.Functor

variable (V : Type u) [Category.{v} V] [Preadditive V] {ι : Type*} (c : ComplexShape ι)

/-- The functor on homotopy categories induced by the identity functor is isomorphic to
the identity functor: the homotopy category counterpart of
`CategoryTheory.Functor.mapHomologicalComplexIdIso`. -/
noncomputable def mapHomotopyCategoryIdIso :
    (𝟭 V).mapHomotopyCategory c ≅ 𝟭 (HomotopyCategory V c) :=
  Quotient.natIsoLift _ ((𝟭 V).mapHomotopyCategoryFactors c ≪≫
    isoWhiskerRight (mapHomologicalComplexIdIso V c) (HomotopyCategory.quotient V c) ≪≫
    (HomotopyCategory.quotient V c).leftUnitor ≪≫
    (HomotopyCategory.quotient V c).rightUnitor.symm)

@[simp]
lemma mapHomotopyCategoryIdIso_hom_app (K : HomologicalComplex V c) :
    (mapHomotopyCategoryIdIso V c).hom.app ((HomotopyCategory.quotient V c).obj K) =
      (HomotopyCategory.quotient V c).map
        ((mapHomologicalComplexIdIso V c).hom.app K) := by
  simp only [mapHomotopyCategoryIdIso, HomotopyCategory.quotient, mapHomotopyCategoryFactors,
    Quotient.natIsoLift_hom, Quotient.natTransLift_app, id_obj, Iso.trans_hom,
    isoWhiskerRight_hom, Iso.symm_hom, NatTrans.comp_app, comp_obj, Quotient.lift.isLift_hom,
    whiskerRight_app, leftUnitor_hom_app, rightUnitor_inv_app, Category.comp_id]
  apply Category.id_comp

@[simp]
lemma mapHomotopyCategoryIdIso_inv_app (K : HomologicalComplex V c) :
    (mapHomotopyCategoryIdIso V c).inv.app ((HomotopyCategory.quotient V c).obj K) =
      (HomotopyCategory.quotient V c).map
        ((mapHomologicalComplexIdIso V c).inv.app K) := by
  simp [mapHomotopyCategoryIdIso, HomotopyCategory.quotient, mapHomotopyCategoryFactors]

end CategoryTheory.Functor
