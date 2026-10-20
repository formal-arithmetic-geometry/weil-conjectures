/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J2
-/
module

public import Sheaf.CategoryTheory.SignedFibreComplex

/-! # Shift signs for the signed fibre complex

Source: Stacks Project, Derived Categories, Tags 014E and 014F, with the signed
calculation in step 3 of lem-amb-signed-fibre-triangulated
(blueprint: lem-amb-signed-fibre-shift).

In degree `n`, the comparison for shift `m` is `(a,b) ↦ (a,(-1)^m b)`, with
canonical transports of integer indices. Naturality of `r` proves it is a chain
map. Its inverse has the same sign. Naturality follows from the diagonal maps;
zero and addition coherence follow from transport composition and
`Int.negOnePow_add`. The construction provides every integer shift, as required by
`CommShift ℤ`, rather than only the comparison for shift one.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits CochainComplex

namespace CategoryTheory.SignedFibre

variable {C : Type u} [Category.{v} C] [Abelian C]
  (A B : C ⥤ AddCommGrpCat.{w}) [A.Additive] [B.Additive] (r : A ⟶ B)

/-- The degreewise shift comparison multiplies the second coordinate by `(-1)^m`. -/
def shiftXIso (I : CochainComplex C ℤ) (m n : ℤ) :
    X A B (I⟦m⟧) n ≅ X A B I (n + m) :=
  AddEquiv.toAddCommGrpIso
    { toFun := fun t ↦ (t.1, m.negOnePow •
        B.map (I.XIsoOfEq (show (n - 1) + m = (n + m) - 1 by omega)).hom t.2)
      invFun := fun t ↦ (t.1, m.negOnePow •
        B.map (I.XIsoOfEq (show (n - 1) + m = (n + m) - 1 by omega)).inv t.2)
      left_inv := by
        intro t
        apply Prod.ext
        · rfl
        · dsimp
          rcases Int.units_eq_one_or m.negOnePow with h | h <;>
            simp [h, ← ConcreteCategory.comp_apply, ← B.map_comp]
      right_inv := by
        intro t
        apply Prod.ext
        · rfl
        · dsimp
          rcases Int.units_eq_one_or m.negOnePow with h | h <;>
            simp [h, ← ConcreteCategory.comp_apply, ← B.map_comp]
      map_add' := by
        intro a b
        apply Prod.ext
        · rfl
        · dsimp
          simp only [map_add, smul_add] }

omit [A.Additive] [B.Additive] in
@[simp] lemma shiftXIso_hom_apply (I : CochainComplex C ℤ) (m n : ℤ)
    (t : X A B (I⟦m⟧) n) :
    (shiftXIso A B I m n).hom t =
      (t.1, m.negOnePow •
        B.map (I.XIsoOfEq (show (n - 1) + m = (n + m) - 1 by omega)).hom t.2) := rfl

/-- Evaluation of a unit multiple of an abelian-group morphism. -/
lemma units_smul_apply {X Y : AddCommGrpCat.{w}} (k : ℤˣ) (f : X ⟶ Y) (x : X) :
    (k • f).hom x = k • f.hom x := by
  rcases Int.units_eq_one_or k with h | h <;> simp [h, AddCommGrpCat.hom_neg]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The signed degreewise comparison is a chain isomorphism. -/
def shiftIso (I : CochainComplex C ℤ) (m : ℤ) :
    obj A B r (I⟦m⟧) ≅ (obj A B r I)⟦m⟧ :=
  HomologicalComplex.Hom.isoOfComponents (shiftXIso A B I m) (by
    intro i j hij
    obtain rfl : j = i + 1 := hij.symm
    change (shiftXIso A B I m i).hom ≫
        (m.negOnePow • (obj A B r I).d (i + m) (i + 1 + m)) =
      (obj A B r (I⟦m⟧)).d i (i + 1) ≫ (shiftXIso A B I m (i + 1)).hom
    apply AddCommGrpCat.ext
    intro t
    simp only [AddCommGrpCat.hom_comp, AddMonoidHom.comp_apply]
    rw [units_smul_apply]
    change m.negOnePow • ((obj A B r I).d (i + m) (i + 1 + m)
      ((shiftXIso A B I m i).hom t)) =
      (shiftXIso A B I m (i + 1)).hom ((obj A B r (I⟦m⟧)).d i (i + 1) t)
    rw [obj_d_apply A B r I (i + m) (i + 1 + m) (by omega),
      obj_d_apply A B r (I⟦m⟧) i (i + 1) rfl]
    apply Prod.ext
    · dsimp
      rw [Functor.map_units_smul]
      exact (units_smul_apply _ _ _).symm
    · change m.negOnePow •
          (B.map (I.XIsoOfEq (show i + m = (i + 1 + m) - 1 by omega)).hom
              (r.app (I.X (i + m)) t.1) -
            B.map (I.d (i + m - 1) (i + 1 + m - 1))
              (m.negOnePow • B.map
                (I.XIsoOfEq (show i - 1 + m = i + m - 1 by omega)).hom t.2)) =
        m.negOnePow • B.map
          (I.XIsoOfEq (show (i + 1 - 1) + m = (i + 1 + m) - 1 by omega)).hom
          (B.map ((I⟦m⟧).XIsoOfEq (show i = (i + 1) - 1 by omega)).hom
              (r.app (I.X (i + m)) t.1) -
            B.map ((I⟦m⟧).d (i - 1) (i + 1 - 1)) t.2)
      have h₁ :
          B.map (I.XIsoOfEq (show i + m = (i + 1 + m) - 1 by omega)).hom =
            B.map ((I⟦m⟧).XIsoOfEq (show i = (i + 1) - 1 by omega)).hom ≫
              B.map (I.XIsoOfEq
                (show (i + 1 - 1) + m = (i + 1 + m) - 1 by omega)).hom := by
        rw [XIsoOfEq_shift, ← B.map_comp,
          HomologicalComplex.XIsoOfEq_hom_comp_XIsoOfEq_hom]
      have h₂ :
          B.map (I.XIsoOfEq (show i - 1 + m = i + m - 1 by omega)).hom ≫
              B.map (I.d (i + m - 1) (i + 1 + m - 1)) =
            B.map (I.d (i - 1 + m) (i + 1 - 1 + m)) ≫
              B.map (I.XIsoOfEq
                (show (i + 1 - 1) + m = (i + 1 + m) - 1 by omega)).hom := by
        simp only [← B.map_comp, HomologicalComplex.XIsoOfEq_hom_comp_d,
          HomologicalComplex.d_comp_XIsoOfEq_hom]
      have ht₁ := congrArg (fun f ↦ f (r.app (I.X (i + m)) t.1)) h₁
      have ht₂ := congrArg (fun f ↦ f t.2) h₂
      simp only [AddCommGrpCat.hom_comp, AddMonoidHom.comp_apply] at ht₁ ht₂
      simp only [shiftFunctor_obj_d', B.map_units_smul, units_smul_apply, map_sub]
      rcases Int.units_eq_one_or m.negOnePow with h | h
      · simpa [h] using congrArg₂ (fun x y ↦ x - y) ht₁ ht₂
      · simpa [h] using congrArg₂ (fun x y ↦ -x + -y) ht₁ ht₂)

@[simp] lemma shiftIso_hom_f (I : CochainComplex C ℤ) (m n : ℤ) :
    (shiftIso A B r I m).hom.f n = (shiftXIso A B I m n).hom := rfl

/-- The shift comparisons are natural in complexes. -/
def shiftNatIso (m : ℤ) :
    shiftFunctor (CochainComplex C ℤ) m ⋙ functor A B r ≅
      functor A B r ⋙ shiftFunctor (CochainComplex AddCommGrpCat.{w} ℤ) m :=
  NatIso.ofComponents (fun I ↦ shiftIso A B r I m) (by
    intro I J f
    ext n t
    apply Prod.ext
    · rfl
    · change m.negOnePow • B.map
          (J.XIsoOfEq (show n - 1 + m = n + m - 1 by omega)).hom
          (B.map (f.f (n - 1 + m)) t.2) =
        B.map (f.f (n + m - 1))
          (m.negOnePow • B.map
            (I.XIsoOfEq (show n - 1 + m = n + m - 1 by omega)).hom t.2)
      have h := congrArg B.map (I.XIsoOfEq_hom_naturality f
        (show n - 1 + m = n + m - 1 by omega))
      simp only [B.map_comp] at h
      have ht := congrArg (fun k ↦ k t.2) h
      simp only [AddCommGrpCat.hom_comp, AddMonoidHom.comp_apply] at ht
      rcases Int.units_eq_one_or m.negOnePow with hs | hs
      · simpa [hs] using ht
      · simpa [hs] using congrArg Neg.neg ht)

/-- Transport in the signed fibre is coordinatewise transport. -/
lemma obj_XIsoOfEq_hom_apply (I : CochainComplex C ℤ) {i j : ℤ} (h : i = j)
    (t : X A B I i) :
    ((obj A B r I).XIsoOfEq h).hom t =
      (A.map (I.XIsoOfEq h).hom t.1,
        B.map (I.XIsoOfEq (congrArg (fun k ↦ k - 1) h)).hom t.2) := by
  subst j
  simp

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Source: Stacks Project, Tags 014E/014F, signed totalization calculation
(blueprint: lem-amb-signed-fibre-shift).

The signed comparisons commute coherently with integer shifts. Their naturality
is `shiftNatIso`; the zero comparison reduces to inverse index transports. For
addition, compose the transports and use `(-1)^(a+b)=(-1)^a(-1)^b`. -/
@[instance_reducible] noncomputable def commShift : (functor A B r).CommShift ℤ where
  commShiftIso := shiftNatIso A B r
  commShiftIso_zero := by
    ext I n t
    change A.obj (I.X (n + 0)) × B.obj (I.X (n - 1 + 0)) at t
    simp only [Functor.CommShift.isoZero_hom_app, HomologicalComplex.comp_f,
      AddCommGrpCat.hom_comp, AddMonoidHom.comp_apply, shiftFunctorZero_inv_app_f]
    change (shiftXIso A B I 0 n).hom t =
      ((obj A B r I).XIsoOfEq (show n = n + 0 by omega)).hom
        ((map A B r ((shiftFunctorZero (CochainComplex C ℤ) ℤ).hom.app I)).f n t)
    rw [shiftXIso_hom_apply, map_apply, obj_XIsoOfEq_hom_apply]
    simp only [shiftFunctorZero_hom_app_f, Int.negOnePow_zero, one_smul]
    dsimp
    simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp,
      HomologicalComplex.XIsoOfEq_hom_comp_XIsoOfEq_hom,
      HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Functor.map_id]
    rfl
  commShiftIso_add a b := by
    ext I n t
    change A.obj (I.X (n + (a + b))) × B.obj (I.X (n - 1 + (a + b))) at t
    simp only [Functor.CommShift.isoAdd_hom_app, HomologicalComplex.comp_f,
      AddCommGrpCat.hom_comp, AddMonoidHom.comp_apply, shiftFunctorAdd_inv_app_f,
      shiftFunctor_map_f']
    change (shiftXIso A B I (a + b) n).hom t =
      ((obj A B r I).XIsoOfEq (show (n + b) + a = n + (a + b) by omega)).hom
        ((shiftXIso A B I a (n + b)).hom
          ((shiftXIso A B (I⟦a⟧) b n).hom
            ((map A B r ((shiftFunctorAdd (CochainComplex C ℤ) a b).hom.app I)).f n t)))
    rw [map_apply, obj_XIsoOfEq_hom_apply]
    simp only [shiftFunctorAdd_hom_app_f]
    dsimp only [shiftXIso, AddEquiv.toAddCommGrpIso]
    dsimp
    simp only [XIsoOfEq_shift]
    rcases Int.units_eq_one_or a.negOnePow with ha | ha <;>
      rcases Int.units_eq_one_or b.negOnePow with hb | hb <;>
      simp only [Int.negOnePow_add, ha, hb] <;>
      simp only [mul_one, mul_neg, neg_neg, one_smul, Units.neg_smul,
        map_neg, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
        HomologicalComplex.XIsoOfEq_hom_comp_XIsoOfEq_hom,
        HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Functor.map_id] <;>
      rfl

end CategoryTheory.SignedFibre
