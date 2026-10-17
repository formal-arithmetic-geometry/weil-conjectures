/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.StageSystem.Preadditive
public import Mathlib.CategoryTheory.Shift.CommShift

/-!
# The shift on the pair category of a stage system

Let `S` be a stage system on categories `C i` with shifts by an additive monoid `A`, whose
transition functors `T_{j/i}` commute with the shifts (comparisons
`σ_{j/i} : T_{j/i}(K[a]) ≅ (T_{j/i} K)[a]`, `Functor.commShiftIso`) and whose associators commute
with the shifts (`CategoryTheory.StageSystem.ShiftCompatible`). Then the shifts of the stages form
morphisms of stage systems `S.shiftMorphism A a` (with `β = σ`), and the pair category carries
the shift `(i, K)[a] = (i, K[a])`, a morphism represented by `u : T_{k/i} K ⟶ T_{k/j} L` being
sent to the one represented by `σ_{k/i} ≫ u[a] ≫ σ_{k/j}⁻¹`. The stage inclusions `j_i` commute
with the shifts (through identities), and so do the transport isomorphisms
`transIso h : T_{j/i} ⋙ j_j ≅ j_i`.

This is the shift part of blueprint `prop-weil-pbc-common-stage-calculus`.

## Main definitions

- `CategoryTheory.StageSystem.ShiftCompatible`: the associators commute with the shifts.
- `CategoryTheory.StageSystem.shiftMorphism`: the shift by `a` as a morphism of stage systems.
- `CategoryTheory.StageSystem.PairCategory.hasShift`: the shift on the pair category.

## Main statements

- `CategoryTheory.StageSystem.PairCategory.shiftFunctor_map_mkHom`: the shift of a morphism
  represented at a stage.
- `CategoryTheory.StageSystem.commShiftι`: the stage inclusions commute with the shifts.
- `CategoryTheory.StageSystem.commShift_transIso_hom`: the transport isomorphisms commute with
  the shifts.
-/

@[expose] public section

universe w' w v u

namespace CategoryTheory

open Category

namespace StageSystem

variable {I : Type w} [Preorder I] {C : I → Type u} [∀ i, Category.{v} (C i)]
  (S : StageSystem C) (A : Type w') [AddMonoid A] [∀ i, HasShift (C i) A]
  [∀ ⦃i j : I⦄ (h : i ≤ j), (S.T h).CommShift A]

/-- The associators of a stage system whose stages carry shifts and whose transition functors
commute with the shifts are compatible with the shifts (blueprint
`prop-weil-pbc-scalar-extension`: the shift comparisons `σ` commute with the associators). -/
class ShiftCompatible : Prop where
  commShift_assoc ⦃i j k : I⦄ (h : i ≤ j) (h' : j ≤ k) :
    NatTrans.CommShift (S.assoc h h').hom A

attribute [instance] ShiftCompatible.commShift_assoc

variable [S.ShiftCompatible A]

/-- The shift by `a` of the stages, as a morphism of stage systems, the compatibilities `β` with
the transition functors being the shift comparisons `σ` of the transition functors. -/
@[simps]
noncomputable def shiftMorphism (a : A) : Morphism S S where
  Φ i := shiftFunctor (C i) a
  β h := (S.T h).commShiftIso a
  coh h h' x := by
    have e := NatTrans.shift_app_comm (S.assoc h h').hom a x
    rw [Functor.commShiftIso_comp_hom_app] at e
    simpa only [Category.assoc] using e

/-- The isomorphisms `K[0] ≅ K` of the stages, as a compatible family. -/
@[simps]
noncomputable def shiftMorphismZero : Morphism.Hom (S.shiftMorphism A 0) (Morphism.id S) where
  τ i := ((shiftFunctorZero (C i) A).hom : shiftFunctor (C i) (0 : A) ⟶ 𝟭 (C i))
  comm h x := by
    simp only [shiftMorphism_β, Morphism.id_β, Functor.commShiftIso_zero,
      Functor.CommShift.isoZero_hom_app, Category.assoc]
    erw [Iso.inv_hom_id_app]
    rfl

omit [S.ShiftCompatible A] [∀ ⦃i j : I⦄ (h : i ≤ j), (S.T h).CommShift A] in
/-- The compatibility of the shift comparison of a functor with `shiftFunctorAdd`. -/
lemma commShiftIso_add_comm {i j : I} (F : C i ⥤ C j) [F.CommShift A] (a b : A) (x : C i) :
    F.map ((shiftFunctorAdd (C i) a b).hom.app x) ≫
      (F.commShiftIso b).hom.app ((shiftFunctor (C i) a).obj x) ≫
        ((F.commShiftIso a).hom.app x)⟦b⟧' =
      (F.commShiftIso (a + b)).hom.app x ≫ (shiftFunctorAdd (C j) a b).hom.app (F.obj x) := by
  simp [Functor.commShiftIso_add]

/-- The isomorphisms `K[a + b] ≅ K[a][b]` of the stages, as a compatible family. -/
@[simps]
noncomputable def shiftMorphismAdd (a b : A) :
    Morphism.Hom (S.shiftMorphism A (a + b)) ((S.shiftMorphism A a).comp (S.shiftMorphism A b))
    where
  τ i := ((shiftFunctorAdd (C i) a b).hom :
    shiftFunctor (C i) (a + b) ⟶ shiftFunctor (C i) a ⋙ shiftFunctor (C i) b)
  comm h x := by
    rw [Morphism.comp_β_hom_app]
    exact commShiftIso_add_comm A (S.T h) a b x

variable [IsDirectedOrder I]

open PairCategory

variable {S A}

lemma shiftMorphism_functor_map_ι (a : A) {i : I} {x y : C i} (f : x ⟶ y) :
    (S.shiftMorphism A a).functor.map ((S.ι i).map f) = (S.ι i).map (f⟦a⟧') :=
  Morphism.functor_map_ι _ f

variable (S A)

/-- The isomorphism `(i, K)[0] ≅ (i, K)`. -/
noncomputable def shiftZeroIso : (S.shiftMorphism A 0).functor ≅ 𝟭 S.PairCategory :=
  NatIso.ofComponents (fun X ↦ (S.ι X.stage).mapIso ((shiftFunctorZero (C X.stage) A).app X.obj))
    (fun {X Y} f ↦ by
      have := (Morphism.descNatTrans (S.shiftMorphismZero A) ≫
        (Morphism.functorIdIso (S := S)).hom).naturality f
      simp only [NatTrans.comp_app, Morphism.functorIdIso_hom_app,
        Morphism.descNatTrans_app] at this
      erw [Category.comp_id, Category.comp_id] at this
      exact this)

/-- The isomorphism `(i, K)[a + b] ≅ (i, K)[a][b]`. -/
noncomputable def shiftAddIso (a b : A) :
    (S.shiftMorphism A (a + b)).functor ≅
      (S.shiftMorphism A a).functor ⋙ (S.shiftMorphism A b).functor :=
  NatIso.ofComponents
    (fun X ↦ (S.ι X.stage).mapIso ((shiftFunctorAdd (C X.stage) a b).app X.obj))
    (fun {X Y} f ↦ by
      have := (Morphism.descNatTrans (S.shiftMorphismAdd A a b) ≫
        (Morphism.functorCompIso _ _).hom).naturality f
      simp only [NatTrans.comp_app, Morphism.functorCompIso_hom_app,
        Morphism.descNatTrans_app] at this
      erw [Category.comp_id, Category.comp_id] at this
      exact this)

variable {S A}

lemma shiftZeroIso_hom_app (X : S.PairCategory) :
    (S.shiftZeroIso A).hom.app X =
      (S.ι X.stage).map ((shiftFunctorZero (C X.stage) A).hom.app X.obj) := rfl

lemma shiftZeroIso_inv_app (X : S.PairCategory) :
    (S.shiftZeroIso A).inv.app X =
      (S.ι X.stage).map ((shiftFunctorZero (C X.stage) A).inv.app X.obj) := rfl

lemma shiftAddIso_hom_app (a b : A) (X : S.PairCategory) :
    (S.shiftAddIso A a b).hom.app X =
      (S.ι X.stage).map ((shiftFunctorAdd (C X.stage) a b).hom.app X.obj) := rfl

/-- An `eqToHom` between two shifts of an object of the pair category is the image of the
corresponding `eqToHom` of its stage. -/
lemma eqToHom_shift (X : S.PairCategory) {a b : A} (hab : a = b)
    (h : (S.shiftMorphism A a).functor.obj X = (S.shiftMorphism A b).functor.obj X) :
    eqToHom h = (S.ι X.stage).map (eqToHom (by rw [hab]) :
      (shiftFunctor (C X.stage) a).obj X.obj ⟶ (shiftFunctor _ b).obj X.obj) := by
  subst hab
  rw [eqToHom_refl, eqToHom_refl, Functor.map_id]
  rfl

variable (S A)

/-- The shift data of the pair category: `(i, K)[a] = (i, K[a])`. -/
noncomputable def shiftMkCore : ShiftMkCore S.PairCategory A where
  F a := (S.shiftMorphism A a).functor
  zero := S.shiftZeroIso A
  add a b := S.shiftAddIso A a b
  assoc_hom_app m₁ m₂ m₃ X := by
    rw [eqToHom_shift X (add_assoc m₁ m₂ m₃)]
    simp only [shiftAddIso_hom_app, shiftMorphism_functor_map_ι]
    simp only [← Functor.map_comp]
    congr 1
    rw [shiftFunctorAdd_assoc_hom_app (C := C X.stage) m₁ m₂ m₃ X.obj]
    simp [shiftFunctorAdd']
    rfl
  zero_add_hom_app n X := by
    rw [eqToHom_shift X (zero_add n)]
    simp only [shiftAddIso_hom_app, shiftZeroIso_inv_app, shiftMorphism_functor_map_ι]
    simp only [← Functor.map_comp]
    congr 1
    exact shiftFunctorAdd_zero_add_hom_app (C := C X.stage) n X.obj
  add_zero_hom_app n X := by
    rw [eqToHom_shift X (add_zero n), shiftAddIso_hom_app]
    erw [shiftZeroIso_inv_app, ← Functor.map_comp]
    congr 1
    exact shiftFunctorAdd_add_zero_hom_app (C := C X.stage) n X.obj

namespace PairCategory

/-- Blueprint `prop-weil-pbc-common-stage-calculus`: the shift on the pair category,
`(i, K)[a] = (i, K[a])`, a morphism represented by `u` being sent to the one represented by
`σ ≫ u[a] ≫ σ⁻¹`. -/
noncomputable instance hasShift : HasShift S.PairCategory A :=
  hasShiftMk _ _ (S.shiftMkCore A)

variable {S A}

lemma shiftFunctor_eq (a : A) :
    shiftFunctor S.PairCategory a = (S.shiftMorphism A a).functor := rfl

lemma shiftFunctor_obj (a : A) (X : S.PairCategory) :
    (shiftFunctor S.PairCategory a).obj X = ⟨X.stage, (shiftFunctor _ a).obj X.obj⟩ := rfl

/-- The value of the shift functor on a representative: `σ_{k/i} ≫ u[a] ≫ σ_{k/j}⁻¹`. -/
lemma shiftFunctor_map_mkHom (a : A) {X Y : S.PairCategory} {n : I} (hX : X.stage ≤ n)
    (hY : Y.stage ≤ n) (u : X.toStage hX ⟶ Y.toStage hY) :
    (shiftFunctor S.PairCategory a).map (mkHom n hX hY u) =
      mkHom (X := ⟨X.stage, (shiftFunctor _ a).obj X.obj⟩)
        (Y := ⟨Y.stage, (shiftFunctor _ a).obj Y.obj⟩) n hX hY
        (((S.T hX).commShiftIso a).hom.app X.obj ≫ u⟦a⟧' ≫
          ((S.T hY).commShiftIso a).inv.app Y.obj) := rfl

/-- The shift of the image of a stage morphism is the image of its shift. -/
lemma shiftFunctor_map_ι (a : A) {i : I} {x y : C i} (f : x ⟶ y) :
    (shiftFunctor S.PairCategory a).map ((S.ι i).map f) = (S.ι i).map (f⟦a⟧') :=
  Morphism.functor_map_ι _ f

lemma shiftFunctorZero_hom_app (X : S.PairCategory) :
    (shiftFunctorZero S.PairCategory A).hom.app X =
      (S.ι X.stage).map ((shiftFunctorZero (C X.stage) A).hom.app X.obj) := rfl

lemma shiftFunctorZero_inv_app (X : S.PairCategory) :
    (shiftFunctorZero S.PairCategory A).inv.app X =
      (S.ι X.stage).map ((shiftFunctorZero (C X.stage) A).inv.app X.obj) := rfl

lemma shiftFunctorAdd_hom_app (a b : A) (X : S.PairCategory) :
    (shiftFunctorAdd S.PairCategory a b).hom.app X =
      (S.ι X.stage).map ((shiftFunctorAdd (C X.stage) a b).hom.app X.obj) := rfl

lemma shiftFunctorAdd_inv_app (a b : A) (X : S.PairCategory) :
    (shiftFunctorAdd S.PairCategory a b).inv.app X =
      (S.ι X.stage).map ((shiftFunctorAdd (C X.stage) a b).inv.app X.obj) := rfl

instance [∀ i, Preadditive (C i)] [∀ ⦃i j : I⦄ (h : i ≤ j), (S.T h).Additive]
    [∀ (i : I) (a : A), (shiftFunctor (C i) a).Additive] (a : A) :
    (shiftFunctor S.PairCategory a).Additive :=
  have : ∀ i, ((S.shiftMorphism A a).Φ i).Additive := fun i ↦
    inferInstanceAs (shiftFunctor (C i) a).Additive
  Morphism.functor_additive _

end PairCategory

open PairCategory

variable {S A}

/-- Blueprint `prop-weil-pbc-common-stage-calculus`: the stage inclusions `j_i` commute with the
shifts, through the identity comparisons `j_i(K[a]) = j_i(K)[a]`. -/
noncomputable instance commShiftι (i : I) : (S.ι i).CommShift A where
  commShiftIso a := ((S.shiftMorphism A a).ιCompFunctorIso i).symm
  commShiftIso_zero := by
    ext K
    rw [Functor.CommShift.isoZero_hom_app]
    change 𝟙 ((S.ι i).obj ((shiftFunctor (C i) (0 : A)).obj K)) =
      (S.ι i).map ((shiftFunctorZero (C i) A).hom.app K) ≫
        (S.ι i).map ((shiftFunctorZero (C i) A).inv.app K)
    rw [← Functor.map_comp, Iso.hom_inv_id_app, Functor.map_id]
  commShiftIso_add a b := by
    ext K
    rw [Functor.CommShift.isoAdd_hom_app]
    change 𝟙 ((S.ι i).obj ((shiftFunctor (C i) (a + b)).obj K)) =
      (S.ι i).map ((shiftFunctorAdd (C i) a b).hom.app K) ≫ 𝟙 _ ≫
        (shiftFunctor S.PairCategory b).map
          (𝟙 ((S.ι i).obj ((shiftFunctor (C i) a).obj K))) ≫
        (S.ι i).map ((shiftFunctorAdd (C i) a b).inv.app K)
    rw [Functor.map_id, id_comp]
    erw [id_comp]
    rw [← Functor.map_comp, Iso.hom_inv_id_app, Functor.map_id]

lemma ι_commShiftIso_hom_app (i : I) (a : A) (K : C i) :
    ((S.ι i).commShiftIso a).hom.app K = 𝟙 _ := rfl

lemma ι_commShiftIso_inv_app (i : I) (a : A) (K : C i) :
    ((S.ι i).commShiftIso a).inv.app K = 𝟙 _ := rfl

/-- Blueprint `prop-weil-pbc-common-stage-calculus`: the transport isomorphisms
`T_{j/i} ⋙ j_j ≅ j_i` commute with the shifts. -/
instance commShift_transIso_hom {i j : I} (h : i ≤ j) :
    NatTrans.CommShift (S.transIso h).hom A where
  shift_comm a := by
    ext K
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.commShiftIso_comp_hom_app, ι_commShiftIso_hom_app, comp_id, transIso_hom_app,
      isoToStage]
    erw [comp_id, id_comp]
    rw [shiftFunctor_map_mkHom, ι_map_eq le_rfl, mkHom_comp_mkHom]
    dsimp only
    rw [mkHom_comp_mkHom]
    congr 1
    have e := NatTrans.shift_app_comm (S.assoc h (le_refl j)).hom a K
    rw [Functor.commShiftIso_comp_hom_app] at e
    rw [← cancel_epi (((S.assoc h le_rfl).hom.app K)⟦a⟧')]
    simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app, Functor.map_id, id_comp]
    rw [← cancel_epi ((S.T (le_refl j)).map (((S.T h).commShiftIso a).hom.app K) ≫
      ((S.T (le_refl j)).commShiftIso a).hom.app ((S.T h).obj K))]
    simp only [Category.assoc] at e
    rw [reassoc_of% e]
    simp [← Functor.map_comp_assoc]

end StageSystem

end CategoryTheory
