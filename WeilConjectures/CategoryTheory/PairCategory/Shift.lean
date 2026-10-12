/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.PairCategory.Functor
public import Mathlib.CategoryTheory.Shift.CommShift

/-!
# The shift on the pair category

Let `F` be a pseudofunctor from a directed preorder to categories whose stages carry shifts by
an additive monoid `A`, whose transition functors `T_{j/i}` commute with the shifts (with
comparisons `σ_{j/i} : T_{j/i}(K[a]) ≅ (T_{j/i} K)[a]`), and whose unit and composition
isomorphisms commute with the shifts (`PairCategory.ShiftCompatible`). Then the pair category
`PairCategory F` carries a shift: `(i, K)[a] = (i, K[a])`, and a morphism represented by
`u : T_{k/i} K ⟶ T_{k/j} L` is sent to the morphism represented by
`σ_{k/j}⁻¹ ∘ u[a] ∘ σ_{k/i}`. It is the descent (`CompatibleFamily.descent`) of the compatible
family of the stage shifts. The stage inclusions `j_i` commute with the shifts.

This is the shift part of blueprint `prop-weil-pbc-common-stage-calculus`.

## Main definitions

- `CategoryTheory.PairCategory.ShiftCompatible F A` : the compatibility of the unit and
  composition isomorphisms of `F` with the shifts.
- `CategoryTheory.PairCategory.shiftFamily F a` : the compatible family of shifts by `a`.
- `CategoryTheory.PairCategory.hasShift` : the shift on `PairCategory F`.
- `CategoryTheory.PairCategory.commShiftIncl` : the stage inclusions commute with the shifts.
-/

@[expose] public section

universe w' w v u

open CategoryTheory Category Limits Pseudofunctor

namespace CategoryTheory.PairCategory

variable {ι : Type w} [Preorder ι] (F : Pseudofunctor (LocallyDiscrete ι) Cat.{v, u})
  (A : Type w') [AddMonoid A] [∀ i : ι, HasShift (F.obj ⟨i⟩) A]
  [∀ ⦃i j : ι⦄ (h : i ≤ j), (F.transition h).CommShift A]

/-- The unit and composition isomorphisms of a pseudofunctor `F` from a preorder to categories
with shifts commute with the shifts, i.e. the shift comparisons of the transition functors are
compatible with the unit and associator data of `F`. -/
class ShiftCompatible : Prop where
  comp ⦃i j k : ι⦄ (h₁ : i ≤ j) (h₂ : j ≤ k) (h : i ≤ k) :
    NatTrans.CommShift (F.transitionComp h₁ h₂ h).hom A
  id (i : ι) (h : i ≤ i) : NatTrans.CommShift (F.transitionId i h).hom A

variable [ShiftCompatible F A]

attribute [instance] ShiftCompatible.comp ShiftCompatible.id

variable {A} in
/-- The compatible family of the shift functors by `a` of the stages of `F`, with the shift
comparisons `σ_{j/i}` of the transition functors. -/
@[simps functor]
noncomputable def shiftFamily (a : A) : CompatibleFamily F F where
  functor i := shiftFunctor _ a
  iso _ _ h := ((F.transition h).commShiftIso a).symm
  iso_comp i j k h₁ h₂ h X := by
    have e := NatTrans.shift_app_comm (F.transitionComp h₁ h₂ h).hom a X
    rw [Functor.commShiftIso_comp_hom_app] at e
    dsimp
    rw [← cancel_epi (((F.transition h).commShiftIso a).hom.app X), Iso.hom_inv_id_app_assoc,
      reassoc_of% e]
    simp [← Functor.map_comp]
  iso_id i h X := by
    have e := NatTrans.shift_app_comm (F.transitionId i h).hom a X
    rw [Functor.commShiftIso_id_hom_app] at e
    erw [comp_id] at e
    simp only [Iso.symm_hom]
    rw [← cancel_epi (((F.transition h).commShiftIso a).hom.app X), Iso.hom_inv_id_app_assoc,
      e]

variable {A} in
lemma shiftFamily_iso (a : A) {i j : ι} (h : i ≤ j) :
    (shiftFamily F a).iso h = ((F.transition h).commShiftIso a).symm := rfl

variable [IsDirected ι (· ≤ ·)]

variable {F A}

/-- The compatible family of isomorphisms `K[0] ≅ K`. -/
@[simps]
noncomputable def shiftFamilyZero : CompatibleFamily.Hom (shiftFamily F (0 : A))
    (CompatibleFamily.id F) where
  app i := (shiftFunctorZero _ A).hom
  comm i j h X := by
    simp [shiftFamily_iso, Functor.commShiftIso_zero, ← Functor.map_comp]
    erw [comp_id]

/-- The compatible family of isomorphisms `K[a + b] ≅ K[a][b]`. -/
@[simps]
noncomputable def shiftFamilyAdd (a b : A) : CompatibleFamily.Hom (shiftFamily F (a + b))
    ((shiftFamily F a).comp (shiftFamily F b)) where
  app i := (shiftFunctorAdd _ a b).hom
  comm i j h X := by
    rw [CompatibleFamily.comp_iso_hom_app]
    simp [shiftFamily_iso, Functor.commShiftIso_add, ← Functor.map_comp]

lemma incl_map_eqToHom (i : ι) {X Y : F.obj ⟨i⟩} (p : X = Y)
    (h : (⟨i, X⟩ : PairCategory F) = ⟨i, Y⟩) :
    eqToHom h = (incl F i).map (eqToHom p) := by
  subst p
  rw [eqToHom_refl, eqToHom_refl, Functor.map_id]
  rfl

variable (F A) in
/-- The isomorphism `(i, K)[0] ≅ (i, K)`. -/
noncomputable def shiftZeroIso : (shiftFamily F (0 : A)).descent ≅ 𝟭 (PairCategory F) :=
  NatIso.ofComponents (fun X ↦ (incl F X.idx).mapIso ((shiftFunctorZero _ A).app X.obj))
    (fun {X Y} f ↦ by
      have := (shiftFamilyZero (F := F) (A := A)).descent.naturality f
      rw [CompatibleFamily.descent_id_map] at this
      exact this)

variable {A} in
/-- The isomorphism `(i, K)[a + b] ≅ (i, K)[a][b]`. -/
noncomputable def shiftAddIso (a b : A) :
    (shiftFamily F (a + b)).descent ≅ (shiftFamily F a).descent ⋙ (shiftFamily F b).descent :=
  NatIso.ofComponents (fun X ↦ (incl F X.idx).mapIso ((shiftFunctorAdd _ a b).app X.obj))
    (fun {X Y} f ↦ by
      have := (shiftFamilyAdd (F := F) a b).descent.naturality f
      rw [CompatibleFamily.descent_comp_map] at this
      exact this)

lemma shiftFamily_descent_map_incl_map (a : A) (i : ι) {X Y : F.obj ⟨i⟩} (u : X ⟶ Y) :
    (shiftFamily F a).descent.map ((incl F i).map u) = (incl F i).map (u⟦a⟧') :=
  CompatibleFamily.descent_map_incl_map _ i u

variable (F A) in
/-- The shift data of the pair category: `(i, K)[a] = (i, K[a])`. -/
noncomputable def shiftMkCore : ShiftMkCore (PairCategory F) A where
  F a := (shiftFamily F a).descent
  zero := shiftZeroIso F A
  add a b := shiftAddIso F a b
  assoc_hom_app m₁ m₂ m₃ X := by
    change (incl F X.idx).map _ ≫ (shiftFamily F m₃).descent.map ((incl F X.idx).map _) =
      _ ≫ (incl F X.idx).map _ ≫ (incl F X.idx).map _
    rw [shiftFamily_descent_map_incl_map, incl_map_eqToHom X.idx (by simp [add_assoc]),
      ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
    congr 1
    simpa [shiftFunctorAdd'] using shiftFunctorAdd_assoc_hom_app (C := F.obj ⟨X.idx⟩) m₁ m₂ m₃
      X.obj
  zero_add_hom_app n X := by
    change (incl F X.idx).map _ = _ ≫ (shiftFamily F n).descent.map ((incl F X.idx).map _)
    rw [shiftFamily_descent_map_incl_map, incl_map_eqToHom X.idx (by simp),
      ← Functor.map_comp]
    congr 1
    exact shiftFunctorAdd_zero_add_hom_app (C := F.obj ⟨X.idx⟩) n X.obj
  add_zero_hom_app n X := by
    change (incl F X.idx).map _ = _ ≫ (incl F X.idx).map _
    rw [incl_map_eqToHom X.idx (by simp), ← Functor.map_comp]
    congr 1
    exact shiftFunctorAdd_add_zero_hom_app (C := F.obj ⟨X.idx⟩) n X.obj

/-- Blueprint `prop-weil-pbc-common-stage-calculus`: the shift on the pair category,
`(i, K)[a] = (i, K[a])`, with `[M, u][a] = [M, σ⁻¹ ∘ u[a] ∘ σ]`. -/
noncomputable instance hasShift : HasShift (PairCategory F) A := hasShiftMk _ A (shiftMkCore F A)

lemma shiftFunctor_eq (a : A) : shiftFunctor (PairCategory F) a = (shiftFamily F a).descent :=
  rfl

lemma shiftFunctor_obj (a : A) (X : PairCategory F) :
    (shiftFunctor (PairCategory F) a).obj X = ⟨X.idx, X.obj⟦a⟧⟩ :=
  rfl

/-- The value of the shift on a representative `u : T_{k/i} K ⟶ T_{k/j} L`:
`σ_{k/j}⁻¹ ∘ u[a] ∘ σ_{k/i}`. -/
lemma shiftFunctor_map_homMk (a : A) {X Y : PairCategory F} {k : ι} (hX : X.idx ≤ k)
    (hY : Y.idx ≤ k) (u : X.at_ hX ⟶ Y.at_ hY) :
    (shiftFunctor (PairCategory F) a).map (homMk hX hY u) =
      homMk (X := (shiftFunctor (PairCategory F) a).obj X)
        (Y := (shiftFunctor (PairCategory F) a).obj Y) hX hY
        (((F.transition hX).commShiftIso a).hom.app X.obj ≫ u⟦a⟧' ≫
          ((F.transition hY).commShiftIso a).inv.app Y.obj) :=
  rfl

lemma shiftFunctorZero_hom_app (X : PairCategory F) :
    (shiftFunctorZero (PairCategory F) A).hom.app X =
      (incl F X.idx).map ((shiftFunctorZero _ A).hom.app X.obj) :=
  rfl

lemma shiftFunctorZero_inv_app (X : PairCategory F) :
    (shiftFunctorZero (PairCategory F) A).inv.app X =
      (incl F X.idx).map ((shiftFunctorZero _ A).inv.app X.obj) :=
  rfl

lemma shiftFunctorAdd_hom_app (a b : A) (X : PairCategory F) :
    (shiftFunctorAdd (PairCategory F) a b).hom.app X =
      (incl F X.idx).map ((shiftFunctorAdd _ a b).hom.app X.obj) :=
  rfl

lemma shiftFunctorAdd_inv_app (a b : A) (X : PairCategory F) :
    (shiftFunctorAdd (PairCategory F) a b).inv.app X =
      (incl F X.idx).map ((shiftFunctorAdd _ a b).inv.app X.obj) :=
  rfl

variable (F) in
/-- Blueprint `prop-weil-pbc-common-stage-calculus`: the stage inclusion `j_i` commutes with
the shifts, through the identity comparison `j_i(K[a]) = (i, K[a]) = (i, K)[a]`. -/
noncomputable instance commShiftIncl (i : ι) : (incl F i).CommShift A where
  commShiftIso a := ((shiftFamily F a).inclCompDescentIso i).symm
  commShiftIso_zero := by
    ext X
    simp [CompatibleFamily.inclCompDescentIso, shiftFunctorZero_inv_app, ← Functor.map_comp]
  commShiftIso_add a b := by
    ext X
    simp [CompatibleFamily.inclCompDescentIso, shiftFunctorAdd_inv_app,
      shiftFamily_descent_map_incl_map, ← Functor.map_comp]

instance (a : A) [∀ i : ι, Preadditive (F.obj ⟨i⟩)]
    [∀ ⦃i j : ι⦄ (h : i ≤ j), (F.transition h).Additive]
    [∀ i : ι, (shiftFunctor (F.obj ⟨i⟩) a).Additive] :
    (shiftFunctor (PairCategory F) a).Additive :=
  CompatibleFamily.descent_additive _

end CategoryTheory.PairCategory
