/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.SquareCompatible

/-!
# Isomorphisms transported along compatible commutation squares

Let `α : F ⟶ G` and `α' : F' ⟶ G'` be compatible with commutation squares
`ιF : F ⋙ T' ≅ T ⋙ F'` and `ιG : G ⋙ T' ≅ T ⋙ G'`
(`CategoryTheory.NatTrans.SquareCompatible`). Then `T' (α_K)` is an isomorphism if and only if
`α'_{T K}` is one (`CategoryTheory.NatTrans.SquareCompatible.isIso_map_app_iff`). Consequently:

* if `T'` reflects isomorphisms and `α'_{T K}` is an isomorphism, so is `α_K`
  (`CategoryTheory.NatTrans.SquareCompatible.isIso_app_of_isIso_app_obj`);
* if `α` is an isomorphism at every object and every object of the source of `F'` is isomorphic
  to some `T K`, then `α'` is an isomorphism at every object
  (`CategoryTheory.NatTrans.SquareCompatible.isIso_app_of_exists_iso`).

These are the formal steps of the reduction of isomorphism statements to finite coefficients
(blueprint `proposition-isomorphisms-reduce-finite-coefficients`).
-/

@[expose] public section

namespace CategoryTheory

namespace NatTrans.SquareCompatible

variable {A B A' B' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']
  {T : A ⥤ A'} {T' : B ⥤ B'} {F G : A ⥤ B} {F' G' : A' ⥤ B'} {ιF : F ⋙ T' ≅ T ⋙ F'}
  {ιG : G ⋙ T' ≅ T ⋙ G'} {α : F ⟶ G} {α' : F' ⟶ G'}

/-- For compatible transformations, `T' (α_K)` is an isomorphism if and only if `α'_{T K}` is
one: the two differ by the isomorphisms `ιF_K` and `ιG_K`. -/
lemma isIso_map_app_iff (h : SquareCompatible ιF ιG α α') (K : A) :
    IsIso (T'.map (α.app K)) ↔ IsIso (α'.app (T.obj K)) := by
  have e : α'.app (T.obj K) = ιF.inv.app K ≫ T'.map (α.app K) ≫ ιG.hom.app K := by
    rw [h K, Iso.inv_hom_id_app_assoc]
  constructor
  · intro
    rw [e]
    infer_instance
  · intro
    have e' : T'.map (α.app K) = ιF.hom.app K ≫ α'.app (T.obj K) ≫ ιG.inv.app K := by
      rw [← reassoc_of% (h K), Iso.hom_inv_id_app]
      exact (Category.comp_id _).symm
    rw [e']
    infer_instance

/-- For compatible transformations, if `α'_{T K}` is an isomorphism then so is `T' (α_K)`. -/
lemma isIso_map_app (h : SquareCompatible ιF ιG α α') (K : A) [IsIso (α'.app (T.obj K))] :
    IsIso (T'.map (α.app K)) :=
  (h.isIso_map_app_iff K).2 inferInstance

/-- For compatible transformations, if `α_K` is an isomorphism then so is `α'_{T K}`. -/
lemma isIso_app_obj (h : SquareCompatible ιF ιG α α') (K : A) [IsIso (α.app K)] :
    IsIso (α'.app (T.obj K)) :=
  (h.isIso_map_app_iff K).1 inferInstance

/-- For compatible transformations and `T'` reflecting isomorphisms, if `α'_{T K}` is an
isomorphism then so is `α_K`. -/
lemma isIso_app_of_isIso_app_obj [T'.ReflectsIsomorphisms] (h : SquareCompatible ιF ιG α α')
    (K : A) [IsIso (α'.app (T.obj K))] : IsIso (α.app K) :=
  have := h.isIso_map_app K
  isIso_of_reflects_iso _ T'

/-- For compatible transformations, if `α` is an isomorphism at every object and every object of
the source of `F'` is isomorphic to some `T K`, then `α'` is an isomorphism at every object. -/
lemma isIso_app_of_exists_iso (h : SquareCompatible ιF ιG α α')
    (hT : ∀ K' : A', ∃ K : A, Nonempty (T.obj K ≅ K')) (hα : ∀ K, IsIso (α.app K))
    (K' : A') : IsIso (α'.app K') := by
  obtain ⟨K, ⟨e⟩⟩ := hT K'
  have := h.isIso_app_obj K
  exact (NatTrans.isIso_app_iff_of_iso α' e).1 inferInstance

end NatTrans.SquareCompatible

end CategoryTheory
