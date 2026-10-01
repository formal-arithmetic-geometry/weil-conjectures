/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms

/-!
# Zero objects and monoidal equivalences in closed monoidal categories

In a monoidal closed category with zero morphisms, `K ⊗ M` is a zero object if `M` is, since
`K ⊗ -` is a left adjoint. If the category is moreover braided, the same holds if `K` is a
zero object, and the internal hom `[K, B]` out of a zero object `K` is a zero object.

A monoidal functor `G : C ⥤ D` between monoidal closed categories which is an equivalence
preserves internal homs: `G [A, B] ≅ [G A, G B]`
(`CategoryTheory.Functor.Monoidal.ihomIsoOfIsEquivalence`). Both `ihom A ⋙ G` and
`G ⋙ ihom (G A)` are right adjoints, of `G⁻¹ ⋙ (A ⊗ -)` and of `(G A ⊗ -) ⋙ G⁻¹`, and these
two left adjoints are isomorphic through the tensorator of `G`.
-/

@[expose] public section

namespace CategoryTheory.MonoidalCategory

open Limits

variable {C : Type*} [Category* C] [MonoidalCategory C] [MonoidalClosed C] [HasZeroMorphisms C]

/-- In a monoidal closed category, `K ⊗ M` is a zero object if `M` is. -/
lemma isZero_tensorObj_of_isZero_right (K : C) {M : C} (hM : IsZero M) : IsZero (K ⊗ M) := by
  rw [IsZero.iff_id_eq_zero]
  exact ((ihom.adjunction K).homEquiv _ _).injective (hM.eq_of_src _ _)

/-- In a braided monoidal closed category, `K ⊗ M` is a zero object if `K` is. -/
lemma isZero_tensorObj_of_isZero_left [BraidedCategory C] {K : C} (hK : IsZero K) (M : C) :
    IsZero (K ⊗ M) :=
  (isZero_tensorObj_of_isZero_right M hK).of_iso (β_ K M)

/-- In a braided monoidal closed category, the internal hom `[K, B]` out of a zero object `K`
is a zero object: maps `T ⟶ [K, B]` correspond to maps `K ⊗ T ⟶ B` out of a zero object. -/
lemma isZero_ihom_obj_of_isZero [BraidedCategory C] {K : C} (hK : IsZero K) (B : C) :
    IsZero ((ihom K).obj B) := by
  rw [IsZero.iff_id_eq_zero]
  exact ((ihom.adjunction K).homEquiv _ _).symm.injective
    ((isZero_tensorObj_of_isZero_left hK _).eq_of_src _ _)

end CategoryTheory.MonoidalCategory

namespace CategoryTheory.Functor.Monoidal

open MonoidalCategory

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
  [MonoidalClosed C] [MonoidalClosed D] (G : C ⥤ D) [G.Monoidal] [G.IsEquivalence]

/-- For a monoidal functor `G` which is an equivalence, the isomorphism
`(G A ⊗ -) ⋙ G⁻¹ ≅ G⁻¹ ⋙ (A ⊗ -)`, that is `G⁻¹ (G A ⊗ T) ≅ A ⊗ G⁻¹ T`, built from the
tensorator `G A ⊗ G (G⁻¹ T) ≅ G (A ⊗ G⁻¹ T)`. -/
noncomputable def tensorLeftCompInvIsoOfIsEquivalence (A : C) :
    tensorLeft (G.obj A) ⋙ G.inv ≅ G.inv ⋙ tensorLeft A :=
  isoWhiskerRight G.asEquivalence.counitIso.symm (tensorLeft (G.obj A) ⋙ G.inv) ≪≫
    isoWhiskerLeft G.inv (isoWhiskerRight (commTensorLeft G A) G.inv) ≪≫
    isoWhiskerLeft (G.inv ⋙ tensorLeft A) G.asEquivalence.unitIso.symm

/-- A monoidal functor `G` which is an equivalence between monoidal closed categories commutes
with internal homs: `ihom A ⋙ G ≅ G ⋙ ihom (G A)`. Both sides are right adjoints, of
`G⁻¹ ⋙ (A ⊗ -)` and of `(G A ⊗ -) ⋙ G⁻¹`, which are isomorphic by
`CategoryTheory.Functor.Monoidal.tensorLeftCompInvIsoOfIsEquivalence`. -/
noncomputable def ihomNatIsoOfIsEquivalence (A : C) :
    ihom A ⋙ G ≅ G ⋙ ihom (G.obj A) :=
  conjugateIsoEquiv (G.asEquivalence.symm.toAdjunction.comp (ihom.adjunction A))
    ((ihom.adjunction (G.obj A)).comp G.asEquivalence.symm.toAdjunction)
    (tensorLeftCompInvIsoOfIsEquivalence G A)

/-- A monoidal functor `G` which is an equivalence between monoidal closed categories preserves
internal homs: `G [A, B] ≅ [G A, G B]`. -/
noncomputable def ihomIsoOfIsEquivalence (A B : C) :
    G.obj ((ihom A).obj B) ≅ (ihom (G.obj A)).obj (G.obj B) :=
  (ihomNatIsoOfIsEquivalence G A).app B

end CategoryTheory.Functor.Monoidal
