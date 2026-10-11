/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Shift
public import WeilConjectures.Mathlib.CategoryTheory.Shift.CommShift

/-!
# The comparison isomorphisms of induced functors on derived categories commute with shifts

For exact functors `F`, `G` between abelian categories, the isomorphisms
`Functor.mapDerivedCategoryNatIso e : D(F) ≅ D(G)` induced by `e : F ≅ G` and
`Functor.mapDerivedCategoryCompIso F G : D(F ⋙ G) ≅ D(F) ⋙ D(G)` commute with the shifts. Both
are characterized by their restriction along the localization functor `DerivedCategory.Q`,
where they are built out of the factorizations `Functor.mapDerivedCategoryFactors` and the
levelwise maps of cochain complexes, all of which commute with the shifts.
-/

@[expose] public section

open CategoryTheory Category Limits

namespace CategoryTheory

variable {C D E : Type*} [Category* C] [Category* D] [Category* E] [Abelian C] [Abelian D]
  [Abelian E] [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]

/-- Every object of the derived category is isomorphic to the image of a cochain complex under
the localization functor, so its image under any functor is isomorphic to the image of such
an object. -/
lemma DerivedCategory.exists_isIso_map_Q_obj {F : DerivedCategory D ⥤ DerivedCategory E}
    (X : DerivedCategory D) : ∃ (Y : CochainComplex D ℤ) (f : X ⟶ DerivedCategory.Q.obj Y),
      IsIso (F.map f) :=
  ⟨_, (DerivedCategory.Q.objObjPreimageIso X).inv, inferInstance⟩

namespace Functor

attribute [local instance] Limits.comp_preservesFiniteLimits Limits.comp_preservesFiniteColimits

/-- The isomorphism `D(F) ≅ D(G)` induced by an isomorphism `F ≅ G` of exact functors commutes
with the shifts. -/
instance commShift_mapDerivedCategoryNatIso_hom {F G : C ⥤ D} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G) :
    NatTrans.CommShift (mapDerivedCategoryNatIso e).hom ℤ := by
  have : Functor.whiskerLeft DerivedCategory.Q (mapDerivedCategoryNatIso e).hom =
      F.mapDerivedCategoryFactors.hom ≫
        Functor.whiskerRight (NatTrans.mapHomologicalComplex e.hom (ComplexShape.up ℤ))
          DerivedCategory.Q ≫ G.mapDerivedCategoryFactors.inv := by
    ext K
    simp [← mapDerivedCategoryNatIso_fac_assoc]
  have : NatTrans.CommShift
      (Functor.whiskerLeft DerivedCategory.Q (mapDerivedCategoryNatIso e).hom) ℤ := by
    rw [this]
    infer_instance
  exact NatTrans.CommShift.of_whiskerLeft _ DerivedCategory.Q
    fun X ↦ DerivedCategory.exists_isIso_map_Q_obj X

/-- The composition isomorphism `D(F ⋙ G) ≅ D(F) ⋙ D(G)` of exact functors commutes with the
shifts. -/
instance commShift_mapDerivedCategoryCompIso_hom (F : C ⥤ D) (G : D ⥤ E) [F.Additive]
    [G.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] :
    NatTrans.CommShift (mapDerivedCategoryCompIso F G).hom ℤ := by
  have : Functor.whiskerLeft DerivedCategory.Q (mapDerivedCategoryCompIso F G).hom =
      (F ⋙ G).mapDerivedCategoryFactors.hom ≫
        Functor.whiskerRight (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G))
          (ComplexShape.up ℤ)).inv DerivedCategory.Q ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (F.mapHomologicalComplex (ComplexShape.up ℤ))
          G.mapDerivedCategoryFactors.inv ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight F.mapDerivedCategoryFactors.inv G.mapDerivedCategory ≫
        (Functor.associator _ _ _).hom := by
    ext K
    simp [← mapDerivedCategoryCompIso_fac]
  have : NatTrans.CommShift
      (Functor.whiskerLeft DerivedCategory.Q (mapDerivedCategoryCompIso F G).hom) ℤ := by
    rw [this]
    infer_instance
  exact NatTrans.CommShift.of_whiskerLeft _ DerivedCategory.Q
    fun X ↦ DerivedCategory.exists_isIso_map_Q_obj X

end Functor

end CategoryTheory
