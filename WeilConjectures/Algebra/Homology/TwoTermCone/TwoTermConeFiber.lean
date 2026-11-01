/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
public import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.SingleHomology

/-! # The shifted fiber of a two-term augmentation

Source: sk-lem-sp-tower, converse paragraph, coefficient error calculation
(blueprint: lem-sp-exact-row-two-term-fiber).
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
universe v u
namespace CochainComplex.TwoTermCone
variable {C : Type u} [Category.{v} C] [Abelian C]
/-- The degree-zero single complex. Source: sk-lem-sp-tower, coefficient calculation
(blueprint: lem-sp-exact-row-two-term-fiber). -/
abbrev single (X : C) := (CochainComplex.singleFunctor C 0).obj X
/-- The degree-zero image of the scalar differential.
Source: sk-lem-sp-tower, coefficient calculation
(blueprint: lem-sp-exact-row-two-term-fiber). -/
def arrow {X : C} (d : X ⟶ X) := (CochainComplex.singleFunctor C 0).map d
/-- The two-term cone in degrees -1 and zero. Source: sk-lem-sp-tower, coefficient calculation
(blueprint: lem-sp-exact-row-two-term-fiber). -/
abbrev complex {X : C} (d : X ⟶ X) := mappingCone (arrow d)
variable {X D : C} (d : X ⟶ X) (q : X ⟶ D)
/-- The quotient augmentation, zero on the shifted source summand.
Source: sk-lem-sp-tower, coefficient calculation
(blueprint: lem-sp-exact-row-two-term-fiber). -/
def augmentation (h : d ≫ q = 0) : complex d ⟶ single D :=
  mappingCone.desc (arrow d) 0 ((CochainComplex.singleFunctor C 0).map q) (by
    simp [arrow, ← Functor.map_comp, h])
/-- The augmentation retains the specified quotient map. Source: sk-lem-sp-tower,
coefficient calculation (blueprint: lem-sp-exact-row-two-term-fiber). -/
@[reassoc (attr := simp)]
lemma inr_augmentation (h : d ≫ q = 0) :
    mappingCone.inr (arrow d) ≫ augmentation d q h =
      (CochainComplex.singleFunctor C 0).map q := by
  simp [augmentation]
/-- The negative-degree coordinate of the two-term cone.
Source: sk-lem-sp-tower, coefficient calculation
(blueprint: lem-sp-exact-row-two-term-fiber). -/
def left : (complex d).X (-1) ⟶ X :=
  HomologicalComplex.homotopyCofiber.fstX (arrow d) (-1) 0 (by decide) ≫
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0 X).hom
/-- The degree-zero coordinate of the two-term cone.
Source: sk-lem-sp-tower, coefficient calculation
(blueprint: lem-sp-exact-row-two-term-fiber). -/
def right : (complex d).X 0 ⟶ X :=
  HomologicalComplex.homotopyCofiber.sndX (arrow d) 0 ≫
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0 X).hom
/-- The actual augmentation cone shifted by -1. Source: sk-lem-sp-tower, coefficient calculation
(blueprint: lem-sp-exact-row-two-term-fiber). -/
abbrev fiber (ε : complex d ⟶ single D) := (mappingCone ε)⟦(-1 : ℤ)⟧
/-- The negative-degree coefficient coordinate of the shifted fiber.
Source: sk-lem-sp-tower, coefficient calculation
(blueprint: lem-sp-exact-row-two-term-fiber). -/
def fiberLeft (ε : complex d ⟶ single D) : (fiber d ε).X (-1) ⟶ X :=
  (shiftFunctorObjXIso (mappingCone ε) (-1) (-1) (-2) rfl).hom ≫
    HomologicalComplex.homotopyCofiber.fstX ε (-2) (-1) (by decide) ≫ left d
/-- The middle coefficient coordinate of the shifted fiber.
Source: sk-lem-sp-tower, coefficient calculation
(blueprint: lem-sp-exact-row-two-term-fiber). -/
def fiberMiddle (ε : complex d ⟶ single D) : (fiber d ε).X 0 ⟶ X :=
  (shiftFunctorObjXIso (mappingCone ε) (-1) 0 (-1) rfl).hom ≫
    HomologicalComplex.homotopyCofiber.fstX ε (-1) 0 (by decide) ≫ right d
/-- The quotient coordinate of the shifted fiber. Source: sk-lem-sp-tower, coefficient calculation
(blueprint: lem-sp-exact-row-two-term-fiber). -/
def fiberRight (ε : complex d ⟶ single D) : (fiber d ε).X 1 ⟶ D :=
  (shiftFunctorObjXIso (mappingCone ε) (-1) 1 0 rfl).hom ≫
    HomologicalComplex.homotopyCofiber.sndX ε 0 ≫
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 D).hom
/-- A normalized comparison from a single object to the shifted quotient cone.
Source: sk-lem-sp-tower, coefficient comparison normalization
(blueprint: lem-sp-exact-row-two-term-fiber). -/
def normalizedComparison (s : X ⟶ X) (ε : complex d ⟶ single D) (a : D ⟶ X)
    (i : (CochainComplex.singleFunctor C (-1)).obj D ⟶ fiber d ε) : Prop :=
  mappingCone.inr (arrow d) ≫ ε = (CochainComplex.singleFunctor C 0).map q ∧
    q ≫ a = s ∧ Mono a ∧
    i.f (-1) ≫ fiberLeft d ε =
      (HomologicalComplex.singleObjXSelf (.up ℤ) (-1) D).hom ≫ a ∧ QuasiIso i

open HomologicalComplex
open HomologicalComplex.homotopyCofiber
open CategoryTheory.Preadditive

private lemma fst_iso {F G : CochainComplex C ℤ} (f : F ⟶ G) (n m : ℤ)
    (h : n + 1 = m) (hz : IsZero (G.X n)) :
    IsIso (fstX f n m h) := by
  refine ⟨⟨inlX f m n h, ?_, by simp⟩⟩
  apply ext_to_X f n m h
  · simp
  · exact hz.eq_of_tgt _ _

private lemma snd_iso {F G : CochainComplex C ℤ} (f : F ⟶ G) (n m : ℤ)
    (h : n + 1 = m) (hz : IsZero (F.X m)) : IsIso (sndX f n) := by
  refine ⟨⟨inrX f n, ?_, by simp⟩⟩
  apply ext_to_X f n m h
  · exact hz.eq_of_tgt _ _
  · simp

private instance left_iso : IsIso (left d) := by
  have := fst_iso (arrow d) (-1) 0 rfl
    (isZero_single_obj_X (.up ℤ) 0 X (-1) (by decide))
  dsimp only [left]
  infer_instance

private instance right_iso : IsIso (right d) := by
  have := snd_iso (arrow d) 0 1 rfl
    (isZero_single_obj_X (.up ℤ) 0 X 1 (by decide))
  dsimp only [right]
  infer_instance

private instance fiberLeft_iso (ε : complex d ⟶ single D) : IsIso (fiberLeft d ε) := by
  have := fst_iso ε (-2) (-1) rfl
    (isZero_single_obj_X (.up ℤ) 0 D (-2) (by decide))
  dsimp only [fiberLeft]
  infer_instance

private instance fiberMiddle_iso (ε : complex d ⟶ single D) :
    IsIso (fiberMiddle d ε) := by
  have := fst_iso ε (-1) 0 rfl
    (isZero_single_obj_X (.up ℤ) 0 D (-1) (by decide))
  dsimp only [fiberMiddle]
  infer_instance

private lemma complex_zero (n : ℤ) (hn : n ≠ -1) (hn' : n ≠ 0) :
    IsZero ((complex d).X n) := by
  apply (mappingCone.isZero_X_iff _ n).2
  exact ⟨isZero_single_obj_X (.up ℤ) 0 X (n + 1) (by omega),
    isZero_single_obj_X (.up ℤ) 0 X n hn'⟩

private instance fiberRight_iso (ε : complex d ⟶ single D) : IsIso (fiberRight d ε) := by
  have := snd_iso ε 0 1 rfl (complex_zero d 1 (by decide) (by decide))
  dsimp only [fiberRight]
  infer_instance

private lemma fiber_zero (ε : complex d ⟶ single D) (n : ℤ)
    (h₁ : n ≠ -1) (h₂ : n ≠ 0) (h₃ : n ≠ 1) : IsZero ((fiber d ε).X n) := by
  apply IsZero.of_iso _ (shiftFunctorObjXIso _ (-1) n (n - 1) (by omega))
  apply (mappingCone.isZero_X_iff _ _).2
  exact ⟨complex_zero d _ (by omega) (by omega),
    isZero_single_obj_X (.up ℤ) 0 D (n - 1) (by omega)⟩

private lemma left_d : (complex d).d (-1) 0 ≫ right d = left d ≫ d := by
  change homotopyCofiber.d (arrow d) (-1) 0 ≫ _ = _
  dsimp only [right, left]
  rw [← Category.assoc, d_sndX (arrow d) (-1) 0 (by decide)]
  simp [arrow, singleFunctor, singleFunctors, HomologicalComplex.single_map_f_self, Category.assoc]

private lemma fiber_d_left (ε : complex d ⟶ single D) :
    (fiber d ε).d (-1) 0 ≫ fiberMiddle d ε = fiberLeft d ε ≫ d := by
  change ((-1 : ℤ).negOnePow • homotopyCofiber.d ε (-2) (-1)) ≫
      (𝟙 _ ≫ fstX ε (-1) 0 (by decide) ≫ right d) =
    (𝟙 _ ≫ fstX ε (-2) (-1) (by decide) ≫ left d) ≫ d
  simp only [show (-1 : ℤ).negOnePow = -1 by decide, Units.neg_smul, one_smul,
    Category.id_comp, neg_comp, Category.assoc]
  rw [← Category.assoc, d_fstX ε (-2) (-1) 0 (by decide) (by decide)]
  simp only [neg_comp, neg_neg, Category.assoc, left_d]

private lemma fiber_d_right (ε : complex d ⟶ single D)
    (hε : mappingCone.inr (arrow d) ≫ ε = (singleFunctor C 0).map q) :
    (fiber d ε).d 0 1 ≫ fiberRight d ε = -(fiberMiddle d ε ≫ q) := by
  have hi : IsIso ((mappingCone.inr (arrow d)).f 0) := by
    have := snd_iso (arrow d) 0 1 rfl
      (isZero_single_obj_X (.up ℤ) 0 X 1 (by decide))
    change IsIso (inrX (arrow d) 0)
    have : inrX (arrow d) 0 = inv (sndX (arrow d) 0) := by
      rw [← cancel_mono (sndX (arrow d) 0)]; simp
    rw [this]; infer_instance
  have he : ε.f 0 ≫ (singleObjXSelf (.up ℤ) 0 D).hom = right d ≫ q := by
    rw [← cancel_epi ((mappingCone.inr (arrow d)).f 0)]
    have hh := congrArg (fun f ↦ f.f 0) hε
    simpa [right, mappingCone.inr, homotopyCofiber.inr,
      singleFunctor, singleFunctors, HomologicalComplex.single_map_f_self, Category.assoc] using
      congrArg (fun f ↦ f ≫ (singleObjXSelf (.up ℤ) 0 D).hom) hh
  change ((-1 : ℤ).negOnePow • homotopyCofiber.d ε (-1) 0) ≫
      (𝟙 _ ≫ sndX ε 0 ≫ (singleObjXSelf (.up ℤ) 0 D).hom) =
    -((𝟙 _ ≫ fstX ε (-1) 0 (by decide) ≫ right d) ≫ q)
  simp only [show (-1 : ℤ).negOnePow = -1 by decide, Units.neg_smul, one_smul,
    Category.id_comp, neg_comp, Category.assoc]
  rw [← Category.assoc, d_sndX ε (-1) 0 (by decide)]
  simp [Category.assoc, he]

private def kernelMap (K : CochainComplex C ℤ) (p : K.X (-1) ⟶ X) [IsIso p]
    (t : K.X 0 ⟶ X) [IsIso t] (w : K.d (-1) 0 ≫ t = p ≫ d)
    (a : D ⟶ X) (had : a ≫ d = 0) : (singleFunctor C (-1)).obj D ⟶ K :=
  mkHomFromSingle (a ≫ inv p) (by
    intro k hk
    have : k = 0 := by change (-1 : ℤ) + 1 = k at hk; omega
    subst k
    rw [← cancel_mono t]
    simp [Category.assoc, w, had])

private lemma kernelMap_coord (K : CochainComplex C ℤ) (p : K.X (-1) ⟶ X) [IsIso p]
    (t : K.X 0 ⟶ X) [IsIso t] (w : K.d (-1) 0 ≫ t = p ≫ d)
    (a : D ⟶ X) (had : a ≫ d = 0) :
    (kernelMap d K p t w a had).f (-1) ≫ p =
      (singleObjXSelf (.up ℤ) (-1) D).hom ≫ a := by
  simp [kernelMap, Category.assoc]

private lemma kernelMap_quasi (K : CochainComplex C ℤ) (p : K.X (-1) ⟶ X) [IsIso p]
    (t : K.X 0 ⟶ X) [IsIso t] (w : K.d (-1) 0 ≫ t = p ≫ d)
    (z : K.d (-2) (-1) = 0) (a : D ⟶ X) [Mono a] (had : a ≫ d = 0)
    (ha : (ShortComplex.mk a d had).Exact) :
    QuasiIsoAt (kernelMap d K p t w a had) (-1) := by
  rw [quasiIsoAt_iff' _ (-2) (-1) 0 (by simp) (by simp)]
  rw [ShortComplex.quasiIso_iff_of_zeros _ (by simp [singleFunctor, singleFunctors])
    (by simp [singleFunctor, singleFunctors]) z]
  constructor
  · apply (ShortComplex.exact_iff_of_iso (ShortComplex.isoMk
      (singleObjXSelf (.up ℤ) (-1) D) (asIso p) (asIso t)
      (kernelMap_coord d K p t w a had).symm w.symm)).2 ha
  · change Mono ((kernelMap d K p t w a had).f (-1))
    dsimp only [kernelMap]
    rw [mkHomFromSingle_f]
    infer_instance

private lemma augmentation_coord (h : d ≫ q = 0) :
    (augmentation d q h).f 0 ≫ (singleObjXSelf (.up ℤ) 0 D).hom = right d ≫ q := by
  dsimp [augmentation]
  rw [mappingCone.desc_f _ _ _ _ 0 1 rfl]
  simp [mappingCone.snd, right, singleFunctor, singleFunctors, HomologicalComplex.single_map_f_self,
    Category.assoc]

private lemma augmentation_quasiAt (h : d ≫ q = 0) [Epi q]
    (he : (ShortComplex.mk d q h).Exact) : QuasiIsoAt (augmentation d q h) 0 := by
  rw [quasiIsoAt_iff' _ (-1) 0 1 (by simp) (by simp)]
  rw [ShortComplex.quasiIso_iff_of_zeros' _
    ((complex_zero d 1 (by decide) (by decide)).eq_of_tgt _ _)
    (by simp) (by simp)]
  constructor
  · apply (ShortComplex.exact_iff_of_iso (ShortComplex.isoMk
      (asIso (left d)) (asIso (right d)) (singleObjXSelf (.up ℤ) 0 D)
      (left_d d).symm (augmentation_coord d q h).symm)).2 he
  · change Epi ((augmentation d q h).f 0)
    have hh := augmentation_coord d q h
    have : Epi ((augmentation d q h).f 0 ≫ (singleObjXSelf (.up ℤ) 0 D).hom) := by
      rw [hh]; infer_instance
    exact (epi_comp_iff_of_isIso _ (singleObjXSelf (.up ℤ) 0 D).hom).1 this

private lemma fiber_exact (ε : complex d ⟶ single D)
    (hε : mappingCone.inr (arrow d) ≫ ε = (singleFunctor C 0).map q)
    (h : d ≫ q = 0) [Epi q] (he : (ShortComplex.mk d q h).Exact)
    (n : ℤ) (hn : n ≠ -1) : (fiber d ε).ExactAt n := by
  by_cases hn0 : n = 0
  · subst n
    rw [HomologicalComplex.exactAt_iff' _ (-1) 0 1 (by simp) (by simp)]
    let e : (fiber d ε).X 1 ≅ D :=
      { hom := -fiberRight d ε
        inv := -inv (fiberRight d ε)
        hom_inv_id := by simp
        inv_hom_id := by simp }
    apply (ShortComplex.exact_iff_of_iso (ShortComplex.isoMk
      (asIso (fiberLeft d ε)) (asIso (fiberMiddle d ε)) e
      (fiber_d_left d ε).symm ?_)).2 he
    dsimp only [e]
    change fiberMiddle d ε ≫ q = (fiber d ε).d 0 1 ≫ (-fiberRight d ε)
    rw [comp_neg, fiber_d_right d q ε hε, neg_neg]
  · by_cases hn1 : n = 1
    · subst n
      rw [HomologicalComplex.exactAt_iff' _ 0 1 2 (by simp) (by simp)]
      apply (ShortComplex.exact_iff_epi _
        ((fiber_zero d ε 2 (by decide) (by decide) (by decide)).eq_of_tgt _ _)).2
      have : Epi ((fiber d ε).d 0 1 ≫ fiberRight d ε) := by
        rw [fiber_d_right d q ε hε]
        infer_instance
      exact (epi_comp_iff_of_isIso _ (fiberRight d ε)).1 this
    · exact HomologicalComplex.ExactAt.of_isZero (fiber_zero d ε n hn hn0 hn1)

private def rowMapF {X' : C} (d' : X' ⟶ X')
    (ε : complex d ⟶ single D) (ε' : complex d' ⟶ single D) (β : X' ⟶ X)
    (n : ℤ) : (fiber d' ε').X n ⟶ (fiber d ε).X n :=
  if h : n = -1 then
    ((fiber d' ε').XIsoOfEq h).hom ≫ fiberLeft d' ε' ≫ β ≫
      inv (fiberLeft d ε) ≫ ((fiber d ε).XIsoOfEq h).inv
  else if h : n = 0 then
    ((fiber d' ε').XIsoOfEq h).hom ≫ fiberMiddle d' ε' ≫ β ≫
      inv (fiberMiddle d ε) ≫ ((fiber d ε).XIsoOfEq h).inv
  else if h : n = 1 then
    ((fiber d' ε').XIsoOfEq h).hom ≫ fiberRight d' ε' ≫
      inv (fiberRight d ε) ≫ ((fiber d ε).XIsoOfEq h).inv
  else 0

private lemma rowMapF_left {X' : C} (d' : X' ⟶ X')
    (ε : complex d ⟶ single D) (ε' : complex d' ⟶ single D) (β : X' ⟶ X) :
    rowMapF d d' ε ε' β (-1) ≫ fiberLeft d ε = fiberLeft d' ε' ≫ β := by
  simp [rowMapF, Category.assoc]

private lemma rowMapF_middle {X' : C} (d' : X' ⟶ X')
    (ε : complex d ⟶ single D) (ε' : complex d' ⟶ single D) (β : X' ⟶ X) :
    rowMapF d d' ε ε' β 0 ≫ fiberMiddle d ε = fiberMiddle d' ε' ≫ β := by
  simp [rowMapF, Category.assoc]

private lemma rowMapF_right {X' : C} (d' : X' ⟶ X')
    (ε : complex d ⟶ single D) (ε' : complex d' ⟶ single D) (β : X' ⟶ X) :
    rowMapF d d' ε ε' β 1 ≫ fiberRight d ε = fiberRight d' ε' := by
  simp [rowMapF, Category.assoc]

private def rowMap {X' : C} (d' : X' ⟶ X') (q' : X' ⟶ D)
    (ε : complex d ⟶ single D) (ε' : complex d' ⟶ single D) (β : X' ⟶ X)
    (hβ : d' ≫ β = β ≫ d) (hq : β ≫ q = q')
    (hε : mappingCone.inr (arrow d) ≫ ε = (singleFunctor C 0).map q)
    (hε' : mappingCone.inr (arrow d') ≫ ε' = (singleFunctor C 0).map q') :
    fiber d' ε' ⟶ fiber d ε where
  f := rowMapF d d' ε ε' β
  comm' n m hnm := by
    have hnm' : n + 1 = m := hnm
    by_cases hn : n = -1
    · subst n
      have : m = 0 := by omega
      subst m
      change rowMapF d d' ε ε' β (-1) ≫ (fiber d ε).d (-1) 0 =
        (fiber d' ε').d (-1) 0 ≫ rowMapF d d' ε ε' β 0
      rw [← cancel_mono (fiberMiddle d ε)]
      simp only [Category.assoc, rowMapF_middle, fiber_d_left]
      rw [← Category.assoc, rowMapF_left, Category.assoc, ← hβ,
        ← Category.assoc, ← fiber_d_left, Category.assoc]
    · by_cases hn0 : n = 0
      · subst n
        have : m = 1 := by omega
        subst m
        change rowMapF d d' ε ε' β 0 ≫ (fiber d ε).d 0 1 =
          (fiber d' ε').d 0 1 ≫ rowMapF d d' ε ε' β 1
        rw [← cancel_mono (fiberRight d ε)]
        simp only [Category.assoc, rowMapF_right, fiber_d_right d q ε hε]
        rw [comp_neg, ← Category.assoc, rowMapF_middle, Category.assoc, hq]
        exact (fiber_d_right d' q' ε' hε').symm
      · by_cases hn1 : n = 1
        · subst n
          have : m = 2 := by omega
          subst m
          exact (fiber_zero d ε 2 (by decide) (by decide) (by decide)).eq_of_tgt _ _
        · exact (fiber_zero d' ε' n hn hn0 hn1).eq_of_src _ _

/-- The exact-row cone comparison. Source: sk-lem-sp-tower, coefficient fiber calculation
(blueprint: lem-sp-exact-row-two-term-fiber).

Proof: form the augmentation by the quotient map. The shifted mapping cone is the
three-term complex with terms X, X, D and differentials d and -q. Exactness of
(a,d) and (d,q), together with Mono a and Epi q, identify the homology of
this shifted fiber with D in degree -1 and zero elsewhere.
The two-term cone itself has negative homology D through a and degree-zero
homology D through q. The map D[1]
with the displayed left coordinate is therefore a quasi-isomorphism.
For naturality, identify the three nonzero terms by their coordinate isomorphisms.
Define the map with coordinates beta, beta and identity, and zero in all other degrees.
The differential equations follow from d' beta = beta d and beta q = q'. Maps from D in degree -1
are determined by that degree, and the negative term of the shifted cone is
identified with X by the left projection. Thus a' beta = alpha a proves the
last equality. The argument includes X=0, D=0 and d=0. -/
theorem exact_row_fiber (a : D ⟶ X) [Mono a] [Epi q]
    (had : a ≫ d = 0) (hdq : d ≫ q = 0)
    (hleft : (ShortComplex.mk a d had).Exact)
    (hright : (ShortComplex.mk d q hdq).Exact) :
    ∃ i : (CochainComplex.singleFunctor C (-1)).obj D ⟶
        fiber d (augmentation d q hdq),
      i.f (-1) ≫ fiberLeft d (augmentation d q hdq) =
        (HomologicalComplex.singleObjXSelf (.up ℤ) (-1) D).hom ≫ a ∧
      QuasiIso i ∧ Nonempty ((complex d).homology (-1) ≅ D) ∧
      Nonempty ((complex d).homology 0 ≅ D) ∧
      ∀ (X' : C) (d' : X' ⟶ X') (q' : X' ⟶ D) (a' : D ⟶ X')
        (α : D ⟶ D) (β : X' ⟶ X)
        (_hβ : d' ≫ β = β ≫ d) (_hq : β ≫ q = q')
        (_ha : a' ≫ β = α ≫ a)
        (ε' : complex d' ⟶ single D)
        (i' : (CochainComplex.singleFunctor C (-1)).obj D ⟶ fiber d' ε'),
        mappingCone.inr (arrow d') ≫ ε' =
          (CochainComplex.singleFunctor C 0).map q' →
        i'.f (-1) ≫ fiberLeft d' ε' =
          (HomologicalComplex.singleObjXSelf (.up ℤ) (-1) D).hom ≫ a' →
        ∃ r : fiber d' ε' ⟶ fiber d (augmentation d q hdq),
          r.f (-1) ≫ fiberLeft d (augmentation d q hdq) = fiberLeft d' ε' ≫ β ∧
          r.f 0 ≫ fiberMiddle d (augmentation d q hdq) = fiberMiddle d' ε' ≫ β ∧
          r.f 1 ≫ fiberRight d (augmentation d q hdq) = fiberRight d' ε' ∧
          i' ≫ r = (CochainComplex.singleFunctor C (-1)).map α ≫ i := by
  let ε := augmentation d q hdq
  let i := kernelMap d (fiber d ε) (fiberLeft d ε) (fiberMiddle d ε)
    (fiber_d_left d ε) a had
  have hi : i.f (-1) ≫ fiberLeft d ε =
      (singleObjXSelf (.up ℤ) (-1) D).hom ≫ a :=
    kernelMap_coord d _ _ _ _ a had
  have hqi : QuasiIso i := by
    rw [quasiIso_iff]
    intro n
    by_cases hn : n = -1
    · subst n
      exact kernelMap_quasi d _ _ _ _
        ((fiber_zero d ε (-2) (by decide) (by decide) (by decide)).eq_of_src _ _)
        a had hleft
    · exact (quasiIsoAt_iff_exactAt i n
        (exactAt_single_obj (.up ℤ) (-1) D n hn)).2
        (fiber_exact d q ε (inr_augmentation d q hdq) hdq hright n hn)
  let j := kernelMap d (complex d) (left d) (right d) (left_d d) a had
  have : QuasiIsoAt j (-1) := kernelMap_quasi d _ _ _ _
    ((complex_zero d (-2) (by decide) (by decide)).eq_of_src _ _) a had hleft
  have hm : Nonempty ((complex d).homology (-1) ≅ D) :=
    ⟨(isoOfQuasiIsoAt j (-1)).symm ≪≫ singleObjHomologySelfIso (.up ℤ) (-1) D⟩
  have : QuasiIsoAt ε 0 := augmentation_quasiAt d q hdq hright
  have hz : Nonempty ((complex d).homology 0 ≅ D) :=
    ⟨isoOfQuasiIsoAt ε 0 ≪≫ singleObjHomologySelfIso (.up ℤ) 0 D⟩
  refine ⟨i, hi, hqi, hm, hz, ?_⟩
  intro X' d' q' a' α β hβ hq ha ε' i' hε' hi'
  let r := rowMap d q d' q' ε ε' β hβ hq (inr_augmentation d q hdq) hε'
  have hl : r.f (-1) ≫ fiberLeft d ε = fiberLeft d' ε' ≫ β :=
    rowMapF_left d d' ε ε' β
  have ht : r.f 0 ≫ fiberMiddle d ε = fiberMiddle d' ε' ≫ β :=
    rowMapF_middle d d' ε ε' β
  have hr : r.f 1 ≫ fiberRight d ε = fiberRight d' ε' :=
    rowMapF_right d d' ε ε' β
  refine ⟨r, hl, ht, hr, ?_⟩
  apply from_single_hom_ext
  rw [comp_f, comp_f, ← cancel_mono (fiberLeft d ε)]
  simp only [Category.assoc]
  rw [hl, ← Category.assoc, hi', Category.assoc, ha]
  rw [← Category.assoc, hi]
  simp [singleFunctor, singleFunctors, HomologicalComplex.single_map_f_self,
    Category.assoc]

end CochainComplex.TwoTermCone
