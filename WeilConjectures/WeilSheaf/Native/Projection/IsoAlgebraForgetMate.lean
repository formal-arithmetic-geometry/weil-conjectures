/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraAdjunctionMate

/-! # The whole forget square of a lifted adjunction -/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.Endofunctor.IsoAlgebra

variable {C D : Type*} [Category C] [Category D] {F : C ⥤ C} {G : D ⥤ D}
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (eL : L ⋙ G ≅ F ⋙ L)
  (eR : R ⋙ F ≅ G ⋙ R)
  (h : (mateEquiv adj adj (TwoSquare.mk _ _ _ _ eL.inv)).natTrans = eR.hom)

/-- The mate of the left forget square is the right forget square. -/
lemma mateEquiv_mapOfNatIsoCompForgetIso_inv_eq :
    (mateEquiv (mapOfNatIsoAdjunction adj eL eR h) adj
      (mapOfNatIsoCompForgetIso eL).inv).natTrans =
        (mapOfNatIsoCompForgetIso eR).hom := by
  ext M : 1
  exact mateEquiv_mapOfNatIsoCompForgetIso_inv_app adj eL eR h M

end CategoryTheory.Endofunctor.IsoAlgebra
