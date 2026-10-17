/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraAdjunction

/-!
# Lifting a left adjoint to algebras with invertible structure morphism

Let `L ⊣ R` be an adjunction between `C` and `D`, and let `F : C ⥤ C` and `G : D ⥤ D` be
equivalences. `CategoryTheory.Endofunctor.IsoAlgebra.mateIso` lifts `L ⊣ R` along a given
exchange isomorphism `eL : L ⋙ G ≅ F ⋙ L` of the left adjoint. This file treats the converse
situation: given an exchange isomorphism `eR : R ⋙ F ≅ G ⋙ R` of the right adjoint, the inverse
mate of `eR` is an isomorphism (`CategoryTheory.Endofunctor.IsoAlgebra.isIso_mateEquiv_symm`), so
`R` transported along `eR` has the left adjoint `L` transported along the inverse mate
(`CategoryTheory.Endofunctor.IsoAlgebra.leftMateIso`,
`CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIsoLeftMateIsoAdjunction`).
-/

@[expose] public section

universe v v' u u'

open CategoryTheory

namespace CategoryTheory.Endofunctor.IsoAlgebra

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D] {F : C ⥤ C} {G : D ⥤ D}
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (eR : R ⋙ F ≅ G ⋙ R)

variable [F.IsEquivalence] [G.IsEquivalence]

/-- If `F` and `G` are equivalences, the inverse mate `F ⋙ L ⟶ L ⋙ G` of an isomorphism
`eR : R ⋙ F ≅ G ⋙ R` is an isomorphism: its iterated mate along the adjunctions `F ⊣ F⁻¹` and
`G ⊣ G⁻¹` is the mate of `eR` along these adjunctions, an isomorphism since their units and
counits are isomorphisms, and it is the conjugate of the inverse mate
(`CategoryTheory.iterated_mateEquiv_conjugateEquiv`). -/
instance isIso_mateEquiv_symm :
    IsIso ((mateEquiv adj adj).symm (TwoSquare.mk _ _ _ _ eR.hom)).natTrans := by
  have h := iterated_mateEquiv_conjugateEquiv adj adj F.asEquivalence.toAdjunction
    G.asEquivalence.toAdjunction ((mateEquiv adj adj).symm (TwoSquare.mk _ _ _ _ eR.hom))
  simp only [Equiv.apply_symm_apply] at h
  have : IsIso (mateEquiv G.asEquivalence.toAdjunction F.asEquivalence.toAdjunction
      (TwoSquare.mk _ _ _ _ eR.hom)).natTrans := by
    have (Y : D) : IsIso ((mateEquiv G.asEquivalence.toAdjunction F.asEquivalence.toAdjunction
        (TwoSquare.mk _ _ _ _ eR.hom)).natTrans.app Y) := by
      simp only [mateEquiv_apply, TwoSquare.mk, NatTrans.comp_app, Functor.comp_obj,
        Functor.id_obj, Functor.rightUnitor_inv_app, Functor.whiskerLeft_app,
        Functor.associator_hom_app, Functor.associator_inv_app, Functor.whiskerRight_app,
        Functor.leftUnitor_hom_app, Category.id_comp, Category.comp_id,
        Equivalence.toAdjunction_unit, Equivalence.toAdjunction_counit]
      infer_instance
    exact NatIso.isIso_of_isIso_app _
  rw [h] at this
  exact conjugateEquiv_of_iso (adj.comp G.asEquivalence.toAdjunction)
    (F.asEquivalence.toAdjunction.comp adj) _

/-- If `F` and `G` are equivalences, the exchange isomorphism `L ⋙ G ≅ F ⋙ L` of the left
adjoint whose inverse is the inverse mate of `eR : R ⋙ F ≅ G ⋙ R`. -/
noncomputable def leftMateIso : L ⋙ G ≅ F ⋙ L :=
  (asIso ((mateEquiv adj adj).symm (TwoSquare.mk _ _ _ _ eR.hom)).natTrans).symm

omit [F.IsEquivalence] [G.IsEquivalence] in
lemma mateEquiv_leftMateIso_inv [F.IsEquivalence] [G.IsEquivalence] :
    (mateEquiv adj adj (TwoSquare.mk _ _ _ _ (leftMateIso adj eR).inv)).natTrans = eR.hom := by
  simp only [leftMateIso, Iso.symm_inv, asIso_hom]
  exact congrArg TwoSquare.natTrans ((mateEquiv adj adj).apply_symm_apply _)

/-- **Lifting a right adjoint to algebras.** If `F` and `G` are equivalences, the transport of
`R` along `eR : R ⋙ F ≅ G ⋙ R` has the left adjoint the transport of `L` along
`CategoryTheory.Endofunctor.IsoAlgebra.leftMateIso`, with the unit and the counit of `L ⊣ R`. -/
noncomputable def mapOfNatIsoLeftMateIsoAdjunction :
    mapOfNatIso (leftMateIso adj eR) ⊣ mapOfNatIso eR :=
  mapOfNatIsoAdjunction adj _ eR (mateEquiv_leftMateIso_inv adj eR)

end CategoryTheory.Endofunctor.IsoAlgebra
