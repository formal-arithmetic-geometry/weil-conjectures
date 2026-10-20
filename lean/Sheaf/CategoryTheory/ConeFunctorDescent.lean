/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J2
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.Plus

/-! # Descent of a cone-preserving functor to homotopy categories -/

@[expose] public section

universe u v u' v'

open CategoryTheory CategoryTheory.Limits CochainComplex

namespace CategoryTheory

/-- Source: Stacks Project, Derived Categories, Tag 014S and the definition of the homotopy
category (blueprint: lem-amb-cone-functor-descent).

A functor on complexes preserving homotopies descends through the quotient relation.
Additivity descends through the full, surjective quotient functor, and its shift comparison
descends by the quotient shift construction. A distinguished triangle is isomorphic to a
cone triangle. Apply the functor to that isomorphism, use the factorization isomorphism to
identify its value on the quotient cone triangle, and apply the supplied cone comparison.
This proves the descended functor triangulated. Its value on a quotient object is the
quotient of the original value, as an equality of objects. A strict lower bound on that
value therefore proves preservation of the property `HomotopyCategory.plus`, which is not
in general invariant under isomorphism. -/
theorem exists_coneFunctor_descent
    {C : Type u} [Category.{v} C] [Abelian C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    (F : CochainComplex C ℤ ⥤ CochainComplex D ℤ) [F.Additive] [F.CommShift ℤ]
    (hH : ∀ {I J : CochainComplex C ℤ} {f g : I ⟶ J},
      Homotopy f g → Nonempty (Homotopy (F.map f) (F.map g)))
    (hc : ∀ {I J : CochainComplex C ℤ} (f : I ⟶ J),
      Nonempty (F.mapTriangle.obj (mappingCone.triangle f) ≅
        mappingCone.triangle (F.map f)))
    (hb : ∀ (I : CochainComplex C ℤ) (N : ℤ),
      I.IsStrictlyGE N → (F.obj I).IsStrictlyGE N) :
    ∃ (G : HomotopyCategory C (.up ℤ) ⥤ HomotopyCategory D (.up ℤ))
      (_addG : G.Additive) (_shiftG : G.CommShift ℤ)
      (alpha : F ⋙ HomotopyCategory.quotient D (.up ℤ) ≅
        HomotopyCategory.quotient C (.up ℤ) ⋙ G),
      alpha.hom.CommShift ℤ ∧ G.IsTriangulated ∧
      (∀ K : HomotopyCategory C (.up ℤ),
        HomotopyCategory.plus C K → HomotopyCategory.plus D (G.obj K)) := by
  let qC := HomotopyCategory.quotient C (.up ℤ)
  let qD := HomotopyCategory.quotient D (.up ℤ)
  let hF : ∀ (I J : CochainComplex C ℤ) (f g : I ⟶ J),
      homotopic C (.up ℤ) f g → (F ⋙ qD).map f = (F ⋙ qD).map g := by
    rintro I J f g ⟨H⟩
    exact HomotopyCategory.eq_of_homotopy _ _ (hH H).some
  let G := Quotient.lift (homotopic C (.up ℤ)) (F ⋙ qD) hF
  let alpha : F ⋙ qD ≅ qC ⋙ G :=
    (Quotient.lift.isLift (homotopic C (.up ℤ)) (F ⋙ qD) hF).symm
  have : (qC ⋙ G).Additive := Functor.additive_of_iso alpha
  have : G.Additive := Functor.additive_of_full_essSurj_comp qC G
  let : G.CommShift ℤ := Quotient.liftCommShift _ _ _ _
  have : alpha.hom.CommShift ℤ := by
    change NatTrans.CommShift
      (Quotient.lift.isLift (homotopic C (.up ℤ)) (F ⋙ qD) hF).inv ℤ
    infer_instance
  refine ⟨G, inferInstance, inferInstance, alpha, inferInstance, ?_, ?_⟩
  · constructor
    rintro T ⟨I, J, f, ⟨e⟩⟩
    let beta : G.mapTriangle.obj (qC.mapTriangle.obj (mappingCone.triangle f)) ≅
        qD.mapTriangle.obj (F.mapTriangle.obj (mappingCone.triangle f)) :=
      ((Functor.mapTriangleCompIso qC G).app _).symm ≪≫
        ((Functor.mapTriangleIso alpha).app _).symm ≪≫
        (Functor.mapTriangleCompIso F qD).app _
    exact ⟨_, _, F.map f, ⟨G.mapTriangle.mapIso e ≪≫ beta ≪≫
      qD.mapTriangle.mapIso (hc f).some⟩⟩
  · intro K hK
    obtain ⟨I, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
    rw [HomotopyCategory.plus_quotient_obj_iff] at hK
    change HomotopyCategory.plus D (qD.obj (F.obj I))
    rw [HomotopyCategory.plus_quotient_obj_iff]
    obtain ⟨N, hN⟩ := hK
    exact ⟨N, hb I N hN⟩

end CategoryTheory
