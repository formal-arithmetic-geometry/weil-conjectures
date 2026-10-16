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
    rfl

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

lemma shiftZeroIso_hom_app (X : PairCategory F) :
    (shiftZeroIso F A).hom.app X =
      (incl F X.idx).map ((shiftFunctorZero (F.obj ⟨X.idx⟩) A).hom.app X.obj) :=
  rfl

lemma shiftZeroIso_inv_app (X : PairCategory F) :
    (shiftZeroIso F A).inv.app X =
      (incl F X.idx).map ((shiftFunctorZero (F.obj ⟨X.idx⟩) A).inv.app X.obj) :=
  rfl

lemma shiftAddIso_hom_app (a b : A) (X : PairCategory F) :
    (shiftAddIso a b).hom.app X =
      (incl F X.idx).map ((shiftFunctorAdd (F.obj ⟨X.idx⟩) a b).hom.app X.obj) :=
  rfl

lemma shiftAddIso_inv_app (a b : A) (X : PairCategory F) :
    (shiftAddIso a b).inv.app X =
      (incl F X.idx).map ((shiftFunctorAdd (F.obj ⟨X.idx⟩) a b).inv.app X.obj) :=
  rfl
/-- An `eqToHom` between two shifts of an object of the pair category is the image of the
corresponding `eqToHom` of its stage. -/
lemma eqToHom_shift (X : PairCategory F) {a b : A} (hab : a = b)
    (h : (shiftFamily F a).descent.obj X = (shiftFamily F b).descent.obj X) :
    eqToHom h = (incl F X.idx).map (eqToHom (by rw [hab]) :
      (shiftFunctor (F.obj ⟨X.idx⟩) a).obj X.obj ⟶ (shiftFunctor _ b).obj X.obj) := by
  subst hab
  rw [eqToHom_refl, eqToHom_refl, Functor.map_id]
  rfl

variable (F A) in
/-- The shift data of the pair category: `(i, K)[a] = (i, K[a])`. -/
noncomputable def shiftMkCore : ShiftMkCore (PairCategory F) A where
  F a := (shiftFamily F a).descent
  zero := shiftZeroIso F A
  add a b := shiftAddIso a b
  assoc_hom_app m₁ m₂ m₃ X := by
    rw [eqToHom_shift X (add_assoc m₁ m₂ m₃)]
    simp only [shiftAddIso_hom_app, shiftFamily_descent_map_incl_map]
    try dsimp only [CompatibleFamily.descent_obj]
    simp only [← Functor.map_comp]
    congr 1
    rw [shiftFunctorAdd_assoc_hom_app (C := F.obj ⟨X.idx⟩) m₁ m₂ m₃ X.obj]
    simp [shiftFunctorAdd']
    rfl
  zero_add_hom_app n X := by
    rw [eqToHom_shift X (zero_add n)]
    simp only [shiftAddIso_hom_app, shiftZeroIso_inv_app, shiftFamily_descent_map_incl_map]
    try dsimp only [CompatibleFamily.descent_obj]
    simp only [← Functor.map_comp]
    congr 1
    exact shiftFunctorAdd_zero_add_hom_app (C := F.obj ⟨X.idx⟩) n X.obj
  add_zero_hom_app n X := by
    rw [eqToHom_shift X (add_zero n)]
    simp only [shiftAddIso_hom_app, shiftZeroIso_inv_app]
    try dsimp only [CompatibleFamily.descent_obj]
    simp only [← Functor.map_comp]
    congr 1
    exact shiftFunctorAdd_add_zero_hom_app (C := F.obj ⟨X.idx⟩) n X.obj

variable (F A) in
/-- Blueprint `prop-weil-pbc-common-stage-calculus`: the shift on the pair category,
`(i, K)[a] = (i, K[a])`, a morphism represented by `u` being sent to the one represented by
`σ⁻¹ ∘ u[a] ∘ σ`. -/
noncomputable instance hasShift : HasShift (PairCategory F) A :=
  hasShiftMk _ _ (shiftMkCore F A)

lemma shiftFunctor_eq (a : A) : shiftFunctor (PairCategory F) a = (shiftFamily F a).descent :=
  rfl

@[simp]
lemma shiftFunctor_obj (a : A) (X : PairCategory F) :
    (shiftFunctor (PairCategory F) a).obj X = ⟨X.idx, (shiftFunctor _ a).obj X.obj⟩ :=
  rfl

/-- The value of the shift functor on a representative: `σ_{k/j} ∘ u[a] ∘ σ_{k/i}⁻¹`. -/
lemma shiftFunctor_map_homMk (a : A) {X Y : PairCategory F} {k : ι} (hX : X.idx ≤ k)
    (hY : Y.idx ≤ k) (u : X.at_ hX ⟶ Y.at_ hY) :
    (shiftFunctor (PairCategory F) a).map (homMk hX hY u) =
      homMk (X := ⟨X.idx, (shiftFunctor _ a).obj X.obj⟩)
        (Y := ⟨Y.idx, (shiftFunctor _ a).obj Y.obj⟩) hX hY
        (((F.transition hX).commShiftIso a).hom.app X.obj ≫ u⟦a⟧' ≫
          ((F.transition hY).commShiftIso a).inv.app Y.obj) :=
  rfl

lemma shiftFunctorZero_hom_app (X : PairCategory F) :
    (shiftFunctorZero (PairCategory F) A).hom.app X =
      (incl F X.idx).map ((shiftFunctorZero (F.obj ⟨X.idx⟩) A).hom.app X.obj) :=
  rfl

lemma shiftFunctorZero_inv_app (X : PairCategory F) :
    (shiftFunctorZero (PairCategory F) A).inv.app X =
      (incl F X.idx).map ((shiftFunctorZero (F.obj ⟨X.idx⟩) A).inv.app X.obj) :=
  rfl

lemma shiftFunctorAdd_hom_app (a b : A) (X : PairCategory F) :
    (shiftFunctorAdd (PairCategory F) a b).hom.app X =
      (incl F X.idx).map ((shiftFunctorAdd (F.obj ⟨X.idx⟩) a b).hom.app X.obj) :=
  rfl

lemma shiftFunctorAdd_inv_app (a b : A) (X : PairCategory F) :
    (shiftFunctorAdd (PairCategory F) a b).inv.app X =
      (incl F X.idx).map ((shiftFunctorAdd (F.obj ⟨X.idx⟩) a b).inv.app X.obj) :=
  rfl

instance [∀ i : ι, Preadditive (F.obj ⟨i⟩)] [∀ ⦃i j : ι⦄ (h : i ≤ j), (F.transition h).Additive]
    [∀ (i : ι) (a : A), (shiftFunctor (F.obj ⟨i⟩) a).Additive] (a : A) :
    (shiftFunctor (PairCategory F) a).Additive :=
  have : ∀ i, ((shiftFamily F a).functor i).Additive := fun i ↦
    inferInstanceAs (shiftFunctor (F.obj ⟨i⟩) a).Additive
  CompatibleFamily.descent_additive _

variable (F) in
/-- The isomorphisms `j_i(K[a]) ≅ j_i(K)[a]` (identities). -/
noncomputable def inclShiftIso (i : ι) (a : A) :
    shiftFunctor (F.obj ⟨i⟩) a ⋙ incl F i ≅ incl F i ⋙ shiftFunctor (PairCategory F) a :=
  ((shiftFamily F a).inclCompDescentIso i).symm

lemma inclShiftIso_hom_app (i : ι) (a : A) (K : F.obj ⟨i⟩) :
    (inclShiftIso F i a).hom.app K = 𝟙 _ :=
  rfl

lemma inclShiftIso_inv_app (i : ι) (a : A) (K : F.obj ⟨i⟩) :
    (inclShiftIso F i a).inv.app K = 𝟙 _ :=
  rfl

/-- Blueprint `prop-weil-pbc-common-stage-calculus`: the stage inclusions `j_i` commute with the
shifts, through the identity comparisons `j_i(K[a]) = j_i(K)[a]`. -/
noncomputable instance commShiftIncl (i : ι) : (incl F i).CommShift A where
  commShiftIso a := inclShiftIso F i a
  commShiftIso_zero := by
    ext K
    rw [Functor.CommShift.isoZero_hom_app, inclShiftIso_hom_app]
    change 𝟙 ((incl F i).obj ((shiftFunctor (F.obj ⟨i⟩) (0 : A)).obj K)) =
      (incl F i).map ((shiftFunctorZero (F.obj ⟨i⟩) A).hom.app K) ≫
        (incl F i).map ((shiftFunctorZero (F.obj ⟨i⟩) A).inv.app K)
    rw [← Functor.map_comp, Iso.hom_inv_id_app, Functor.map_id]
  commShiftIso_add a b := by
    ext K
    rw [Functor.CommShift.isoAdd_hom_app, inclShiftIso_hom_app, inclShiftIso_hom_app,
      inclShiftIso_hom_app]
    change 𝟙 ((incl F i).obj ((shiftFunctor (F.obj ⟨i⟩) (a + b)).obj K)) =
      (incl F i).map ((shiftFunctorAdd (F.obj ⟨i⟩) a b).hom.app K) ≫ 𝟙 _ ≫
        (shiftFunctor (PairCategory F) b).map
          (𝟙 ((incl F i).obj ((shiftFunctor (F.obj ⟨i⟩) a).obj K))) ≫
        (incl F i).map ((shiftFunctorAdd (F.obj ⟨i⟩) a b).inv.app K)
    rw [Functor.map_id, id_comp]
    erw [id_comp]
    rw [← Functor.map_comp, Iso.hom_inv_id_app, Functor.map_id]

lemma incl_commShiftIso_hom_app (i : ι) (a : A) (K : F.obj ⟨i⟩) :
    ((incl F i).commShiftIso a).hom.app K = 𝟙 _ :=
  rfl

lemma incl_commShiftIso_inv_app (i : ι) (a : A) (K : F.obj ⟨i⟩) :
    ((incl F i).commShiftIso a).inv.app K = 𝟙 _ :=
  rfl

end CategoryTheory.PairCategory
