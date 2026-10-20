/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J2
-/
module

public import Mathlib.Algebra.Homology.CochainComplexPlus
public import Mathlib.Algebra.Category.Grp.Abelian

/-! # The signed fibre complex

Source: Stacks Project, Derived Categories, Tags 014E and 014F, with the explicit
signed two-term construction in steps 1, 2 and 8 of
lem-amb-signed-fibre-triangulated (blueprint: lem-amb-signed-fibre-complex).

The square of the displayed differential is zero: functoriality kills the two
squares, and naturality of `r` cancels the mixed terms. The same naturality makes
the diagonal maps chain maps. Identities, composition and additivity are
coordinatewise. For a homotopy the second component receives a minus sign, so
its mixed terms cancel as well. Finally additive functors preserve zero objects,
and `n<N` implies `n-1<N`, proving preservation of a strict lower bound.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits CochainComplex

namespace CategoryTheory.SignedFibre

variable {C : Type u} [Category.{v} C] [Abelian C]
  (A B : C ⥤ AddCommGrpCat.{w}) [A.Additive] [B.Additive] (r : A ⟶ B)

/-- The two coordinates in degree `n` of the signed fibre. -/
abbrev X (I : CochainComplex C ℤ) (n : ℤ) : AddCommGrpCat.{w} :=
  AddCommGrpCat.of (A.obj (I.X n) × B.obj (I.X (n - 1)))

/-- The signed differential `(a,b) ↦ (d_A a, r a - d_B b)`. -/
def d (I : CochainComplex C ℤ) (n : ℤ) : X A B I n ⟶ X A B I (n + 1) :=
  AddCommGrpCat.ofHom
    (((A.map (I.d n (n + 1))).hom.comp (AddMonoidHom.fst _ _)).prod
      ((((B.map (I.XIsoOfEq (Int.add_sub_cancel n 1).symm).hom).hom.comp
        (r.app (I.X n)).hom).comp (AddMonoidHom.fst _ _)) -
        ((B.map (I.d (n - 1) ((n + 1) - 1))).hom.comp (AddMonoidHom.snd _ _))))

/-- Naturality of `r` cancels the mixed terms in the square of the differential. -/
lemma d_sq (I : CochainComplex C ℤ) (n : ℤ) : d A B r I n ≫ d A B r I (n + 1) = 0 := by
  apply AddCommGrpCat.ext
  intro t
  apply Prod.ext
  · change A.map (I.d (n + 1) (n + 1 + 1)) (A.map (I.d n (n + 1)) t.1) = 0
    rw [← ConcreteCategory.comp_apply, ← A.map_comp, I.d_comp_d, A.map_zero]
    rfl
  · dsimp [d]
    simp only [map_sub]
    simp only [← ConcreteCategory.comp_apply, ← B.map_comp,
      HomologicalComplex.d_comp_d, B.map_zero]
    rw [r.naturality]
    simp only [Category.assoc, ← B.map_comp,
      HomologicalComplex.XIsoOfEq_hom_comp_d, HomologicalComplex.d_comp_XIsoOfEq_hom]
    simp

/-- The signed fibre of `r` on a cochain complex, constructed degree by degree. -/
abbrev obj (I : CochainComplex C ℤ) : CochainComplex AddCommGrpCat.{w} ℤ :=
  CochainComplex.of (X A B I) (d A B r I) (d_sq A B r I)

/-- The diagonal chain map on signed fibres. -/
def map {I J : CochainComplex C ℤ} (f : I ⟶ J) : obj A B r I ⟶ obj A B r J :=
  CochainComplex.ofHom
    (fun n ↦ AddCommGrpCat.ofHom
      (((A.map (f.f n)).hom.comp (AddMonoidHom.fst _ _)).prod
        ((B.map (f.f (n - 1))).hom.comp (AddMonoidHom.snd _ _)))) (by
      intro n
      simp only [obj, CochainComplex.of_d]
      apply AddCommGrpCat.ext
      intro t
      apply Prod.ext
      · change A.map (J.d n (n + 1)) (A.map (f.f n) t.1) =
          A.map (f.f (n + 1)) (A.map (I.d n (n + 1)) t.1)
        simp only [← ConcreteCategory.comp_apply, ← A.map_comp, f.comm]
      · dsimp [d]
        simp only [map_sub, ← ConcreteCategory.comp_apply, ← B.map_comp]
        rw [r.naturality]
        simp only [Category.assoc, ← B.map_comp, f.comm,
          HomologicalComplex.XIsoOfEq_hom_naturality])

/-- Source: Stacks Project, Tags 014E/014F, signed two-term construction
(blueprint: lem-amb-signed-fibre-complex).

The additive signed fibre functor on complexes. The preceding square-zero and
chain-map calculations construct its objects and morphisms. Identities and
composition follow on the two coordinates. The instance below proves additivity;
`homotopy` constructs its action on homotopies, and `obj_isStrictlyGE` proves
preservation of a strict lower bound. -/
abbrev functor : CochainComplex C ℤ ⥤ CochainComplex AddCommGrpCat.{w} ℤ where
  obj := obj A B r
  map := map A B r
  map_id I := by
    ext n t <;> simp [map, AddMonoidHom.prod_apply,
      AddMonoidHom.coe_fst, AddMonoidHom.coe_snd]
  map_comp f g := by
    ext n t <;> simp [map, AddMonoidHom.prod_apply,
      AddMonoidHom.comp_apply, AddMonoidHom.coe_fst, AddMonoidHom.coe_snd]

instance : (functor A B r).Additive where
  map_add := by
    intro I J f g
    ext n t <;>
    simp [functor, map, AddMonoidHom.prod_apply,
      AddMonoidHom.comp_apply, AddMonoidHom.coe_fst, AddMonoidHom.coe_snd]

omit [A.Additive] [B.Additive] in
/-- The displayed differential formula. -/
@[simp] lemma d_apply (I : CochainComplex C ℤ) (n : ℤ) (t : X A B I n) :
    d A B r I n t =
      (A.map (I.d n (n + 1)) t.1,
        B.map (I.XIsoOfEq (Int.add_sub_cancel n 1).symm).hom (r.app (I.X n) t.1) -
          B.map (I.d (n - 1) ((n + 1) - 1)) t.2) := rfl

/-- The displayed diagonal map formula. -/
@[simp] lemma map_apply {I J : CochainComplex C ℤ} (f : I ⟶ J)
    (n : ℤ) (t : X A B I n) :
    (map A B r f).f n t = (A.map (f.f n) t.1, B.map (f.f (n - 1)) t.2) := rfl

/-- The signed homotopy components. -/
def hom {I J : CochainComplex C ℤ} {f g : I ⟶ J}
    (H : Homotopy f g) (n m : ℤ) : X A B I n ⟶ X A B J m :=
  AddCommGrpCat.ofHom
    (((A.map (H.hom n m)).hom.comp (AddMonoidHom.fst _ _)).prod
      (-((B.map (H.hom (n - 1) (m - 1))).hom.comp (AddMonoidHom.snd _ _))))

/-- The coordinate formula for any adjacent differential. -/
lemma obj_d_apply (I : CochainComplex C ℤ) (i j : ℤ) (h : i + 1 = j)
    (t : X A B I i) :
    (obj A B r I).d i j t =
      (A.map (I.d i j) t.1,
        B.map (I.XIsoOfEq (show i = j - 1 by omega)).hom (r.app (I.X i) t.1) -
          B.map (I.d (i - 1) (j - 1)) t.2) := by
  subst j
  simp only [obj, CochainComplex.of_d]
  rfl

omit [A.Additive] [B.Additive] in
/-- The coordinate formula for the signed homotopy. -/
@[simp] lemma hom_apply {I J : CochainComplex C ℤ} {f g : I ⟶ J}
    (H : Homotopy f g) (n m : ℤ) (t : X A B I n) :
    hom A B H n m t =
      (A.map (H.hom n m) t.1, -B.map (H.hom (n - 1) (m - 1)) t.2) := rfl

/-- Transporting an index before a homotopy component preserves that component. -/
lemma homotopy_transport {I J : CochainComplex C ℤ} {f g : I ⟶ J}
    (H : Homotopy f g) {i j : ℤ} (h : i = j) (k : ℤ) :
    (I.XIsoOfEq h).hom ≫ H.hom j k = H.hom i k := by
  subst j
  simp

/-- Equal intermediate indices give the same differential-homotopy composite. -/
lemma homotopy_d_transport {I J : CochainComplex C ℤ} {f g : I ⟶ J}
    (H : Homotopy f g) {i j : ℤ} (h : i = j) (k l : ℤ) :
    I.d k i ≫ H.hom i l = I.d k j ≫ H.hom j l := by
  subst j
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Naturality of `r` makes the signed components a homotopy. -/
def homotopy {I J : CochainComplex C ℤ} {f g : I ⟶ J}
    (H : Homotopy f g) : Homotopy (map A B r f) (map A B r g) where
  hom := hom A B H
  zero n m h := by
    dsimp [hom]
    rw [H.zero n m h,
      H.zero (n - 1) (m - 1) (by simp only [ComplexShape.up_Rel] at h ⊢; omega)]
    simp only [Functor.map_zero, AddCommGrpCat.hom_zero, AddMonoidHom.zero_comp, neg_zero]
    ext t <;> rfl
  comm n := by
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel n (n + 1) from rfl),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel (n - 1) n from Int.sub_add_cancel n 1)]
    apply AddCommGrpCat.ext
    intro t
    simp only [AddCommGrpCat.hom_add, AddCommGrpCat.hom_comp,
      AddMonoidHom.add_apply, AddMonoidHom.comp_apply]
    dsimp only [map, hom]
    simp only [obj_d_apply A B r I n (n + 1) rfl,
      obj_d_apply A B r J (n - 1) n (by omega)]
    simp only [AddCommGrpCat.hom_ofHom, AddMonoidHom.prod_apply,
      AddMonoidHom.comp_apply, AddMonoidHom.coe_fst, AddMonoidHom.coe_snd,
      AddMonoidHom.neg_apply]
    apply Prod.ext
    · have h := congrArg A.map (H.comm n)
      rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel n (n + 1) from rfl),
        prevD_eq _ (show (ComplexShape.up ℤ).Rel (n - 1) n from Int.sub_add_cancel n 1)] at h
      simp only [A.map_add, A.map_comp] at h
      exact congrArg (fun k : A.obj (I.X n) ⟶ A.obj (J.X n) ↦ k t.1) h
    · dsimp only [Prod.snd_add, Prod.snd, Prod.fst]
      simp only [map_sub, map_neg, ← ConcreteCategory.comp_apply]
      simp only [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom,
        B.map_id, Category.comp_id, r.naturality]
      have h := congrArg B.map (H.comm (n - 1))
      rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel (n - 1) n from Int.sub_add_cancel n 1),
        prevD_eq _ (show (ComplexShape.up ℤ).Rel (n - 1 - 1) (n - 1)
          from Int.sub_add_cancel (n - 1) 1)] at h
      simp only [B.map_add, B.map_comp] at h
      have ht := congrArg (fun k : B.obj (I.X (n - 1)) ⟶ B.obj (J.X (n - 1)) ↦ k t.2) h
      simp only [AddCommGrpCat.hom_add_apply] at ht
      simp only [Category.assoc, ← B.map_comp, homotopy_transport]
      rw [homotopy_d_transport H (Int.add_sub_cancel n 1) (n - 1) (n - 1)]
      simp only [← B.map_comp] at ht
      rw [ht]
      abel

/-- The signed fibre preserves a strict lower bound. -/
lemma obj_isStrictlyGE (I : CochainComplex C ℤ) (N : ℤ) [I.IsStrictlyGE N] :
    (obj A B r I).IsStrictlyGE N := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro n hn
  have hA := A.map_isZero (I.isZero_of_isStrictlyGE N n)
  have hB := B.map_isZero (I.isZero_of_isStrictlyGE N (n - 1))
  rw [IsZero.iff_id_eq_zero]
  apply AddCommGrpCat.ext
  intro t
  apply Prod.ext
  · exact congrArg (fun k : A.obj (I.X n) ⟶ A.obj (I.X n) ↦ k t.1) (hA.eq_of_src (𝟙 _) 0)
  · exact congrArg (fun k : B.obj (I.X (n - 1)) ⟶ B.obj (I.X (n - 1)) ↦ k t.2)
      (hB.eq_of_src (𝟙 _) 0)

end CategoryTheory.SignedFibre
