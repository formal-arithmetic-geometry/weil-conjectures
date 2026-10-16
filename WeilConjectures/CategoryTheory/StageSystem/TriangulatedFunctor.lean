/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.StageSystem.Triangulated

/-!
# Descended functors are triangulated

Let `F : S.Morphism S'` be a morphism of stage systems of triangulated categories: functors
`Φ_i : C i ⥤ D i` with isomorphisms `β_{j/i} : Φ_i ⋙ T'_{j/i} ≅ T_{j/i} ⋙ Φ_j`. If the `Φ_i`
commute with the shifts and the `β` are compatible with the shift comparisons
(`CategoryTheory.StageSystem.Morphism.ShiftCompatible`), then the descended functor
`F.functor : S.PairCategory ⥤ S'.PairCategory` commutes with the shifts, with comparison
isomorphisms induced by those of the `Φ_i`. If moreover the `Φ_i` are triangulated, so is the
descended functor. A compatible family of natural transformations commuting with the shifts
descends to a natural transformation commuting with the shifts.

This is the exactness part of blueprint `prop-weil-pbc-descent-functors`: exact functors and
exact natural transformations descend.

## Main definitions

- `CategoryTheory.StageSystem.Morphism.ShiftCompatible`: the compatibility of the `β` with the
  shifts.
- `CategoryTheory.StageSystem.Morphism.commShiftFunctor`: the descended functor commutes with the
  shifts.

## Main statements

- `CategoryTheory.StageSystem.Morphism.isTriangulated_functor`: the descended functor is
  triangulated.
- `CategoryTheory.StageSystem.Morphism.commShift_descNatTrans`: descended natural
  transformations commute with the shifts.
-/

@[expose] public section

universe w v u v' u'

namespace CategoryTheory

open Category Limits Pretriangulated

namespace StageSystem

variable {I : Type w} [Preorder I] {C : I → Type u} [∀ i, Category.{v} (C i)]
  {D : I → Type u'} [∀ i, Category.{v'} (D i)]
  [∀ i, HasShift (C i) ℤ] [∀ i, HasShift (D i) ℤ]
  {S : StageSystem C} {S' : StageSystem D}
  [∀ ⦃i j : I⦄ (h : i ≤ j), (S.T h).CommShift ℤ] [∀ ⦃i j : I⦄ (h : i ≤ j), (S'.T h).CommShift ℤ]
  [S.ShiftCompatible ℤ] [S'.ShiftCompatible ℤ]

namespace Morphism

variable (F : Morphism S S') [∀ i, (F.Φ i).CommShift ℤ]

/-- The compatibility isomorphisms `β` of a morphism of stage systems commute with the shifts
(blueprint `prop-weil-pbc-descent-functors`, the "shift equations" of the `β`). -/
class ShiftCompatible : Prop where
  commShift_β ⦃i j : I⦄ (h : i ≤ j) : NatTrans.CommShift (F.β h).hom ℤ

attribute [instance] ShiftCompatible.commShift_β

variable [F.ShiftCompatible]

/-- The shift comparisons of the stage functors, as a compatible family of isomorphisms
`(S.shiftMorphism a).comp F ⟶ F.comp (S'.shiftMorphism a)`. -/
@[simps]
noncomputable def shiftHom (a : ℤ) :
    Hom ((S.shiftMorphism ℤ a).comp F) (F.comp (S'.shiftMorphism ℤ a)) where
  τ i := ((F.Φ i).commShiftIso a).hom
  comm h x := by
    simpa [Functor.commShiftIso_comp_hom_app] using NatTrans.shift_app_comm (F.β h).hom a x

variable [IsDirectedOrder I]

open PairCategory

/-- The shift comparison `Φ((i, K)[a]) ≅ Φ(i, K)[a]` of a descended functor, with components
the images under the stage inclusions of the shift comparisons of the stage functors. -/
noncomputable def functorCommShiftIso (a : ℤ) :
    shiftFunctor S.PairCategory a ⋙ F.functor ≅ F.functor ⋙ shiftFunctor S'.PairCategory a :=
  NatIso.ofComponents
    (fun X ↦ (S'.ι X.stage).mapIso (((F.Φ X.stage).commShiftIso a).app X.obj))
    (fun {X Y} f ↦ by
      have := ((functorCompIso _ _).inv ≫ descNatTrans (F.shiftHom a) ≫
        (functorCompIso _ _).hom).naturality f
      simp only [NatTrans.comp_app, functorCompIso_hom_app, functorCompIso_inv_app, comp_id,
        id_comp, descNatTrans_app, shiftHom_τ] at this
      exact this)

@[simp]
lemma functorCommShiftIso_hom_app (a : ℤ) (X : S.PairCategory) :
    (F.functorCommShiftIso a).hom.app X =
      (S'.ι X.stage).map (((F.Φ X.stage).commShiftIso a).hom.app X.obj) := rfl

@[simp]
lemma functorCommShiftIso_inv_app (a : ℤ) (X : S.PairCategory) :
    (F.functorCommShiftIso a).inv.app X =
      (S'.ι X.stage).map (((F.Φ X.stage).commShiftIso a).inv.app X.obj) := rfl

/-- Blueprint `prop-weil-pbc-descent-functors`: the descended functor commutes with the shifts. -/
noncomputable instance commShiftFunctor : F.functor.CommShift ℤ where
  commShiftIso a := F.functorCommShiftIso a
  commShiftIso_zero := by
    ext X
    rw [Functor.CommShift.isoZero_hom_app, functorCommShiftIso_hom_app,
      PairCategory.shiftFunctorZero_hom_app, PairCategory.shiftFunctorZero_inv_app,
      functor_map_ι, ← Functor.map_comp, Functor.commShiftIso_zero,
      Functor.CommShift.isoZero_hom_app]
    rfl
  commShiftIso_add a b := by
    ext X
    rw [Functor.CommShift.isoAdd_hom_app, functorCommShiftIso_hom_app, functorCommShiftIso_hom_app,
      functorCommShiftIso_hom_app, PairCategory.shiftFunctorAdd_hom_app,
      PairCategory.shiftFunctorAdd_inv_app, functor_map_ι]
    erw [PairCategory.shiftFunctor_map_ι]
    simp only [← Functor.map_comp]
    rw [Functor.commShiftIso_add, Functor.CommShift.isoAdd_hom_app]
    rfl

lemma functor_commShiftIso_hom_app (a : ℤ) (X : S.PairCategory) :
    (F.functor.commShiftIso a).hom.app X =
      (S'.ι X.stage).map (((F.Φ X.stage).commShiftIso a).hom.app X.obj) := rfl

/-- The compatibility `j_i ⋙ Φ ≅ Φ_i ⋙ j_i` of a descended functor with the stage inclusions
commutes with the shifts. -/
instance commShift_ιCompFunctorIso_hom (i : I) :
    NatTrans.CommShift (F.ιCompFunctorIso i).hom ℤ := ⟨fun a ↦ by
  ext x
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.commShiftIso_comp_hom_app, ι_commShiftIso_hom_app, functor_commShiftIso_hom_app]
  erw [Functor.map_id, Functor.map_id, id_comp, id_comp, comp_id, comp_id]
  rfl⟩

/-- A compatible family of natural transformations commuting with the shifts descends to a
natural transformation commuting with the shifts. -/
instance commShift_descNatTrans {G : Morphism S S'} [∀ i, (G.Φ i).CommShift ℤ]
    [G.ShiftCompatible] (τ : Hom F G) [∀ i, NatTrans.CommShift (τ.τ i) ℤ] :
    NatTrans.CommShift (descNatTrans τ) ℤ := ⟨fun a ↦ by
  ext X
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    functor_commShiftIso_hom_app, descNatTrans_app]
  erw [PairCategory.shiftFunctor_map_ι]
  simp only [← Functor.map_comp]
  congr 1
  exact NatTrans.shift_app_comm (τ.τ X.stage) a X.obj⟩

variable [∀ i, Preadditive (C i)] [∀ i, HasZeroObject (C i)]
  [∀ (i : I) (n : ℤ), (shiftFunctor (C i) n).Additive] [∀ i, Pretriangulated (C i)]
  [∀ ⦃i j : I⦄ (h : i ≤ j), (S.T h).Additive] [∀ ⦃i j : I⦄ (h : i ≤ j), (S.T h).IsTriangulated]
  [∀ i, Preadditive (D i)] [∀ i, HasZeroObject (D i)]
  [∀ (i : I) (n : ℤ), (shiftFunctor (D i) n).Additive] [∀ i, Pretriangulated (D i)]
  [∀ ⦃i j : I⦄ (h : i ≤ j), (S'.T h).Additive] [∀ ⦃i j : I⦄ (h : i ≤ j), (S'.T h).IsTriangulated]
  [Nonempty I]

/-- Blueprint `prop-weil-pbc-descent-functors`: the functor descended from a family of
triangulated functors is triangulated. -/
instance isTriangulated_functor [∀ i, (F.Φ i).IsTriangulated] : F.functor.IsTriangulated where
  map_distinguished T hT := by
    obtain ⟨k, T', hT', ⟨e⟩⟩ := hT
    exact ⟨k, (F.Φ k).mapTriangle.obj T', (F.Φ k).map_distinguished _ hT',
      ⟨F.functor.mapTriangle.mapIso e ≪≫ ((Functor.mapTriangleCompIso _ _).symm ≪≫
        Functor.mapTriangleIso (F.ιCompFunctorIso k) ≪≫ Functor.mapTriangleCompIso _ _).app T'⟩⟩

end Morphism

end StageSystem

end CategoryTheory
