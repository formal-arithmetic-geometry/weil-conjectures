/-
Copyright (c) 2026 Claude and the SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude, SHEAF group F4
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.Single
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Algebra.Ring.NegOnePow
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.HomComplex

/-! # Product Hom homotopies and normalized resolution changes

Source: Stacks Project, sites-cohomology.tex, Tag 0A8X, and derived.tex, Tag 070I.
(blueprint: lem-sf-equivariant-hom-resolution-calculus).

The projections below specify the construction without choosing objects from an existence
proof. All formulas are morphism identities in the output category; taking that category to
be a category of equivariant objects retains the additional structure on every map.
-/

@[expose] public section

set_option autoImplicit false

universe uA vA uB vB wA wB

open CategoryTheory CategoryTheory.Limits Opposite

namespace CochainComplex

/-- The componentwise action of a complex bifunctor, with its endpoints explicit.
Source: Stacks Project, Tag 0A8X, functoriality of Hom complexes.
(blueprint: lem-sf-equivariant-hom-resolution-calculus). -/
def productHomResolutionMap
    {A : Type uA} [Category.{vA} A] [HasZeroMorphisms A]
    {B : Type uB} [Category.{vB} B] [HasZeroMorphisms B]
    (F : (CochainComplex A ℤ)ᵒᵖ × CochainComplex A ℤ ⥤ CochainComplex B ℤ)
    {K K' I I' : CochainComplex A ℤ} (t : K' ⟶ K) (v : I ⟶ I') :
    F.obj (op K, I) ⟶ F.obj (op K', I') :=
  F.map (X := (op K, I)) (Y := (op K', I')) (t.op, v)

open CategoryTheory.Category
open HomComplex

/- The projection API follows `WeilConjectures.Algebra.Homology.BifunctorHomComplex`.
Here the differential uses the Stacks sign in the total degree, rather than its
source-degree sign; all constructions and identities are proved below. -/
section ProductConstruction

variable {C : Type uA} [Category.{vA} C] {D : Type uB} [Category.{vB} D]
  {E : Type wA} [Category.{wB} E] [Preadditive C] [Preadditive D] [Preadditive E]
  [HasCountableProducts E] (H : Cᵒᵖ ⥤ D ⥤ E)

namespace ResolutionProduct

/-- The differential of the hom complex `resolutionObj H K Y`. Use `resolutionObj_d_π`
instead of unfolding it. -/
private noncomputable def d (K : CochainComplex C ℤ) (Y : CochainComplex D ℤ) (n m : ℤ) :
    (∏ᶜ fun T : Triplet n ↦ (H.obj (op (K.X T.p))).obj (Y.X T.q)) ⟶
      ∏ᶜ fun T : Triplet m ↦ (H.obj (op (K.X T.p))).obj (Y.X T.q) :=
  Pi.lift fun T ↦ (Pi.π
      (fun T : Triplet n ↦ (H.obj (op (K.X T.p))).obj (Y.X T.q)) ⟨T.p, T.p + n, rfl⟩ ≫
        (H.obj _).map (Y.d (T.p + n) T.q) - n.negOnePow •
      (Pi.π (fun T : Triplet n ↦ (H.obj (op (K.X T.p))).obj (Y.X T.q))
          ⟨T.p + m - n, T.q, by grind [T.hpq]⟩ ≫
        (H.map (K.d T.p (T.p + m - n)).op).app _))

private lemma d_π (K : CochainComplex C ℤ) (Y : CochainComplex D ℤ) (n m p q : ℤ) (hpq : p + m = q)
    (q' p' : ℤ) (hq' : p + n = q') (hp' : p' + n = q) :
    d H K Y n m ≫ Pi.π _ (⟨p, q, hpq⟩ : Triplet m) =
      (Pi.π (fun T : Triplet n ↦ (H.obj (op (K.X T.p))).obj (Y.X T.q)) ⟨p, q', hq'⟩ ≫
          (H.obj _).map (Y.d q' q) - n.negOnePow •
        (Pi.π (fun T : Triplet n ↦ (H.obj (op (K.X T.p))).obj (Y.X T.q)) ⟨p', q, hp'⟩ ≫
          (H.map (K.d p p').op).app _)) := by
  subst hq'
  obtain rfl : p' = p + m - n := by lia
  simp only [d, Pi.lift_π]

variable [∀ X, (H.obj X).Additive] [H.Additive] (K : CochainComplex C ℤ)
  (Y : CochainComplex D ℤ)

private lemma shape (n m : ℤ) (hnm : ¬ n + 1 = m) : d H K Y n m = 0 := by
  refine Pi.hom_ext _ _ fun ⟨p, q, hpq⟩ ↦ ?_
  rw [d_π H K Y n m p q hpq (p + n) (p + m - n) rfl (by lia), Y.shape, K.shape]
  · simp
  all_goals
    simp only [ComplexShape.up_Rel]
    lia

private lemma d_comp_d (n₁ n₂ n₃ : ℤ) : d H K Y n₁ n₂ ≫ d H K Y n₂ n₃ = 0 := by
  by_cases h₁₂ : n₁ + 1 = n₂
  · by_cases h₂₃ : n₂ + 1 = n₃
    · refine Pi.hom_ext _ _ fun ⟨p, q, hpq⟩ ↦ ?_
      rw [assoc, d_π H K Y n₂ n₃ p q hpq (q - 1) (p + 1) (by lia) (by lia),
        Preadditive.comp_sub, Linear.comp_units_smul,
        reassoc_of% (d_π H K Y n₁ n₂ p (q - 1) (by lia) (q - 2) (p + 1) (by lia) (by lia)),
        reassoc_of% (d_π H K Y n₁ n₂ (p + 1) q (by lia) (q - 1) (p + 2) (by lia) (by lia))]
      simp only [Linear.units_smul_comp, Preadditive.sub_comp, assoc, ← Functor.map_comp,
        HomologicalComplex.d_comp_d, Functor.map_zero, comp_zero, ← NatTrans.comp_app,
        ← op_comp, op_zero, NatTrans.app_zero, zero_comp, NatTrans.naturality,
        zero_sub, smul_sub, smul_smul]
      subst h₁₂
      simp only [Int.negOnePow_succ, Units.neg_smul, smul_zero]
      abel
    · rw [shape H K Y n₂ n₃ h₂₃, comp_zero]
  · rw [shape H K Y n₁ n₂ h₁₂, zero_comp]

end ResolutionProduct

variable [∀ X, (H.obj X).Additive] [H.Additive] (K : CochainComplex C ℤ)
  (Y : CochainComplex D ℤ)

/-- The hom complex of a bifunctor `H`: in degree `n`, the product of the `H(K^p, Y^q)` for
`p + n = q`. -/
private noncomputable def resolutionObj : CochainComplex E ℤ where
  X n := ∏ᶜ fun T : Triplet n ↦ (H.obj (op (K.X T.p))).obj (Y.X T.q)
  d := ResolutionProduct.d H K Y
  shape n m h := ResolutionProduct.shape H K Y n m h
  d_comp_d' _ _ _ _ _ := ResolutionProduct.d_comp_d H K Y _ _ _

/-- The projection from the object of degree `n` of `resolutionObj H K Y` to the factor
`H(K^p, Y^q)`, for `p + n = q`. -/
private noncomputable def resolutionπ (n p q : ℤ) (h : p + n = q) :
    (resolutionObj H K Y).X n ⟶ (H.obj (op (K.X p))).obj (Y.X q) :=
  Pi.π _ (⟨p, q, h⟩ : Triplet n)

variable {H K Y} in
@[ext]
private lemma resolutionObj_hom_ext {A : E} {n : ℤ} {f g : A ⟶ (resolutionObj H K Y).X n}
    (h : ∀ p q hpq, f ≫ resolutionπ H K Y n p q hpq = g ≫ resolutionπ H K Y n p q hpq) :
    f = g :=
  Pi.hom_ext _ _ fun T ↦ h T.p T.q T.hpq

/-- A morphism into the object of degree `n` of the hom complex, from its components. -/
private noncomputable def resolutionLift {A : E} (n : ℤ)
    (f : ∀ p q (_ : p + n = q), A ⟶ (H.obj (op (K.X p))).obj (Y.X q)) :
    A ⟶ (resolutionObj H K Y).X n :=
  Pi.lift fun T ↦ f T.p T.q T.hpq

@[reassoc (attr := simp)]
private lemma resolutionLift_π {A : E} (n : ℤ)
    (f : ∀ p q (_ : p + n = q), A ⟶ (H.obj (op (K.X p))).obj (Y.X q)) (p q : ℤ)
    (hpq : p + n = q) :
    resolutionLift H K Y n f ≫ resolutionπ H K Y n p q hpq = f p q hpq :=
  Pi.lift_π _ _

/-- The components of the differential of the hom complex. -/
@[reassoc]
private lemma resolutionObj_d_π (n m p q : ℤ) (hpq : p + m = q) (q' p' : ℤ) (hq' : p + n = q')
    (hp' : p' + n = q) :
    (resolutionObj H K Y).d n m ≫ resolutionπ H K Y m p q hpq =
      (resolutionπ H K Y n p q' hq' ≫ (H.obj _).map (Y.d q' q) - n.negOnePow •
        (resolutionπ H K Y n p' q hp' ≫ (H.map (K.d p p').op).app _)) :=
  ResolutionProduct.d_π H K Y n m p q hpq q' p' hq' hp'


section Functoriality

variable {H K Y}

/-- The morphism of hom complexes induced by a morphism `g : Y ⟶ Y'` in the second variable. -/
private noncomputable def resolutionMapRight {Y' : CochainComplex D ℤ} (g : Y ⟶ Y') :
    resolutionObj H K Y ⟶ resolutionObj H K Y' where
  f n := resolutionLift H K Y' n fun p q hpq ↦
    resolutionπ H K Y n p q hpq ≫ (H.obj _).map (g.f q)
  comm' n m hnm := by
    ext p q hpq
    simp only [ComplexShape.up_Rel] at hnm
    rw [assoc, resolutionObj_d_π H K Y' n m p q hpq (q - 1) (p + 1) (by lia) (by lia), assoc,
      resolutionLift_π, resolutionObj_d_π_assoc H K Y n m p q hpq (q - 1) (p + 1) (by lia)
        (by lia)]
    simp only [Linear.comp_units_smul, Linear.units_smul_comp, Preadditive.comp_sub,
      Preadditive.sub_comp, assoc, resolutionLift_π_assoc, ← Functor.map_comp, g.comm,
      NatTrans.naturality]

@[reassoc (attr := simp)]
private lemma resolutionMapRight_f_π {Y' : CochainComplex D ℤ} (g : Y ⟶ Y') (n p q : ℤ)
    (hpq : p + n = q) :
    (resolutionMapRight (H := H) (K := K) g).f n ≫ resolutionπ H K Y' n p q hpq =
      resolutionπ H K Y n p q hpq ≫ (H.obj _).map (g.f q) :=
  by simp [resolutionMapRight]

/-- The morphism of hom complexes induced by a morphism `f : K' ⟶ K` in the first variable. -/
private noncomputable def resolutionMapLeft {K' : CochainComplex C ℤ} (f : K' ⟶ K) :
    resolutionObj H K Y ⟶ resolutionObj H K' Y where
  f n := resolutionLift H K' Y n fun p q hpq ↦
    resolutionπ H K Y n p q hpq ≫ (H.map (f.f p).op).app _
  comm' n m hnm := by
    ext p q hpq
    simp only [ComplexShape.up_Rel] at hnm
    rw [assoc, resolutionObj_d_π H K' Y n m p q hpq (q - 1) (p + 1) (by lia) (by lia), assoc,
      resolutionLift_π, resolutionObj_d_π_assoc H K Y n m p q hpq (q - 1) (p + 1) (by lia)
        (by lia)]
    simp only [Linear.comp_units_smul, Linear.units_smul_comp, Preadditive.comp_sub,
      Preadditive.sub_comp, assoc, resolutionLift_π_assoc, NatTrans.naturality,
      ← NatTrans.comp_app, ← Functor.map_comp, ← op_comp, f.comm]

@[reassoc (attr := simp)]
private lemma resolutionMapLeft_f_π {K' : CochainComplex C ℤ} (f : K' ⟶ K) (n p q : ℤ)
    (hpq : p + n = q) :
    (resolutionMapLeft (H := H) (Y := Y) f).f n ≫ resolutionπ H K' Y n p q hpq =
      resolutionπ H K Y n p q hpq ≫ (H.map (f.f p).op).app _ :=
  by simp [resolutionMapLeft]

private lemma resolutionMapRight_id : resolutionMapRight (H := H) (K := K) (𝟙 Y) = 𝟙 _ := by
  ext n p q hpq
  simp

private lemma resolutionMapRight_comp {Y' Y'' : CochainComplex D ℤ} (g : Y ⟶ Y') (g' : Y' ⟶ Y'') :
    resolutionMapRight (H := H) (K := K) (g ≫ g') =
      resolutionMapRight g ≫ resolutionMapRight g' := by
  ext n p q hpq
  simp

private lemma resolutionMapLeft_id : resolutionMapLeft (H := H) (Y := Y) (𝟙 K) = 𝟙 _ := by
  ext n p q hpq
  simp

private lemma resolutionMapLeft_comp {K' K'' : CochainComplex C ℤ}
    (f : K' ⟶ K) (f' : K'' ⟶ K') :
    resolutionMapLeft (H := H) (Y := Y) (f' ≫ f) =
      resolutionMapLeft f ≫ resolutionMapLeft f' := by
  ext n p q hpq
  simp [← NatTrans.comp_app, ← Functor.map_comp]

@[reassoc]
private lemma resolutionMap_exchange {K' : CochainComplex C ℤ}
    {Y' : CochainComplex D ℤ} (f : K' ⟶ K) (g : Y ⟶ Y') :
    resolutionMapLeft (H := H) (Y := Y) f ≫ resolutionMapRight g =
      resolutionMapRight g ≫ resolutionMapLeft f := by
  ext n p q hpq
  simp only [HomologicalComplex.comp_f, assoc, resolutionMapRight_f_π,
    resolutionMapLeft_f_π, resolutionMapRight_f_π_assoc, resolutionMapLeft_f_π_assoc,
    NatTrans.naturality]

variable (H) in
private noncomputable def resolutionFunctor :
    (CochainComplex C ℤ)ᵒᵖ × CochainComplex D ℤ ⥤ CochainComplex E ℤ where
  obj X := resolutionObj H X.1.unop X.2
  map f := resolutionMapLeft f.1.unop ≫ resolutionMapRight f.2
  map_id X := by simp [resolutionMapLeft_id, resolutionMapRight_id]
  map_comp f g := by
    dsimp
    rw [resolutionMapLeft_comp, resolutionMapRight_comp]
    simp only [assoc]
    rw [resolutionMap_exchange_assoc]

private lemma resolutionFunctor_map_f_π {K' : CochainComplex C ℤ}
    {Y' : CochainComplex D ℤ} (f : K' ⟶ K) (g : Y ⟶ Y') (n p q : ℤ)
    (hpq : p + n = q) :
    ((resolutionFunctor H).map (X := (op K, Y)) (Y := (op K', Y')) (f.op, g)).f n ≫
        resolutionπ H K' Y' n p q hpq =
      resolutionπ H K Y n p q hpq ≫ (H.map (f.f p).op).app (Y.X q) ≫
        (H.obj (op (K'.X p))).map (g.f q) := by
  simp [resolutionFunctor, assoc]

private noncomputable def resolutionIsLimit (n : ℤ) :
    IsLimit (Fan.mk ((resolutionObj H K Y).X n)
      (fun p : ℤ ↦ resolutionπ H K Y n p (p + n) rfl)) :=
  Fan.IsLimit.mk _
    (fun s ↦ resolutionLift H K Y n fun p q hpq ↦ s.proj p ≫
      (H.obj (op (K.X p))).map (eqToHom (congrArg Y.X hpq)))
    (by intro s p; simp)
    (by
      intro s m hm
      apply resolutionObj_hom_ext
      intro p q hpq
      subst q
      simpa using hm p)

private noncomputable def resolutionSourceHom {K' : CochainComplex C ℤ}
    {t t' : K' ⟶ K} (h : Homotopy t t') (n m : ℤ) :
    (resolutionObj H K Y).X n ⟶ (resolutionObj H K' Y).X m :=
  resolutionLift H K' Y m fun p q hpq ↦ n.negOnePow •
    (resolutionπ H K Y n (p + m - n) q (by lia) ≫
      (H.map (h.hom p (p + m - n)).op).app (Y.X q))

@[reassoc]
private lemma resolutionSourceHom_π {K' : CochainComplex C ℤ}
    {t t' : K' ⟶ K} (h : Homotopy t t') (n m p r q : ℤ)
    (hrq : r + n = q) (hpq : p + m = q) :
    resolutionSourceHom (H := H) (Y := Y) h n m ≫ resolutionπ H K' Y m p q hpq =
      n.negOnePow • (resolutionπ H K Y n r q hrq ≫
        (H.map (h.hom p r).op).app (Y.X q)) := by
  obtain rfl : r = p + m - n := by lia
  simp [resolutionSourceHom]

private noncomputable def resolutionSourceHomotopy {K' : CochainComplex C ℤ}
    {t t' : K' ⟶ K} (h : Homotopy t t') :
    Homotopy (resolutionMapLeft (H := H) (Y := Y) t) (resolutionMapLeft t') where
  hom := resolutionSourceHom h
  zero n m hnm := by
    apply resolutionObj_hom_ext
    intro p q hpq
    rw [resolutionSourceHom_π h n m p (p + m - n) q (by lia) hpq,
      h.zero p (p + m - n) (by simp only [ComplexShape.up_Rel] at *; omega)]
    simp
  comm n := by
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel n (n + 1) by simp),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel (n - 1) n by simp)]
    apply resolutionObj_hom_ext
    intro p q hpq
    rw [resolutionMapLeft_f_π]
    simp only [Preadditive.add_comp, assoc, resolutionMapLeft_f_π]
    rw [resolutionSourceHom_π h (n + 1) n p (p - 1) q (by lia) hpq,
      Linear.comp_units_smul,
      resolutionObj_d_π_assoc H K Y n (n + 1) (p - 1) q (by lia) (q - 1) p
        (by lia) (by lia),
      resolutionObj_d_π H K' Y (n - 1) n p q hpq (q - 1) (p + 1) (by lia) (by lia)]
    simp only [Preadditive.comp_sub, Linear.comp_units_smul,
      resolutionSourceHom_π_assoc h n (n - 1) p (p - 1) (q - 1) (by lia) (by lia),
      resolutionSourceHom_π_assoc h n (n - 1) (p + 1) p q (by lia) (by lia),
      Preadditive.sub_comp, Linear.units_smul_comp, assoc, NatTrans.naturality,
      ← NatTrans.comp_app, ← Functor.map_comp, ← op_comp,
      Int.negOnePow_succ, Int.negOnePow_sub, Int.negOnePow_one, Units.neg_smul,
      smul_sub, smul_smul]
    have hh := h.comm p
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel p (p + 1) by simp),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel (p - 1) p by simp)] at hh
    rw [hh]
    simp only [op_add, Functor.map_add, NatTrans.app_add, Preadditive.comp_add,
      op_comp, Functor.map_comp, NatTrans.comp_app]
    simp only [neg_mul, mul_neg, mul_one, Int.units_mul_self, Units.neg_smul,
      one_smul]
    abel

private noncomputable def resolutionTargetHom {Y' : CochainComplex D ℤ}
    {v v' : Y ⟶ Y'} (h : Homotopy v v') (n m : ℤ) :
    (resolutionObj H K Y).X n ⟶ (resolutionObj H K Y').X m :=
  resolutionLift H K Y' m fun p q _ ↦ resolutionπ H K Y n p (p + n) rfl ≫
    (H.obj (op (K.X p))).map (h.hom (p + n) q)

@[reassoc]
private lemma resolutionTargetHom_π {Y' : CochainComplex D ℤ}
    {v v' : Y ⟶ Y'} (h : Homotopy v v') (n m p q r : ℤ)
    (hpq : p + m = q) (hpr : p + n = r) :
    resolutionTargetHom (H := H) (K := K) h n m ≫ resolutionπ H K Y' m p q hpq =
      resolutionπ H K Y n p r hpr ≫ (H.obj (op (K.X p))).map (h.hom r q) := by
  subst r
  simp [resolutionTargetHom]

private noncomputable def resolutionTargetHomotopy {Y' : CochainComplex D ℤ}
    {v v' : Y ⟶ Y'} (h : Homotopy v v') :
    Homotopy (resolutionMapRight (H := H) (K := K) v) (resolutionMapRight v') where
  hom := resolutionTargetHom h
  zero n m hnm := by
    apply resolutionObj_hom_ext
    intro p q hpq
    rw [resolutionTargetHom_π h n m p q (p + n) hpq rfl,
      h.zero (p + n) q (by simp only [ComplexShape.up_Rel] at *; omega)]
    simp
  comm n := by
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel n (n + 1) by simp),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel (n - 1) n by simp)]
    apply resolutionObj_hom_ext
    intro p q hpq
    rw [resolutionMapRight_f_π]
    simp only [Preadditive.add_comp, assoc, resolutionMapRight_f_π]
    rw [resolutionTargetHom_π h (n + 1) n p q (q + 1) hpq (by lia),
      resolutionObj_d_π_assoc H K Y n (n + 1) p (q + 1) (by lia) q (p + 1)
        hpq (by lia),
      resolutionObj_d_π H K Y' (n - 1) n p q hpq (q - 1) (p + 1) (by lia) (by lia)]
    simp only [Preadditive.comp_sub, Linear.comp_units_smul,
      resolutionTargetHom_π_assoc h n (n - 1) p (q - 1) q (by lia) hpq,
      resolutionTargetHom_π_assoc h n (n - 1) (p + 1) q (q + 1) (by lia) (by lia),
      Preadditive.sub_comp, Linear.units_smul_comp, assoc, NatTrans.naturality,
      ← Functor.map_comp, Int.negOnePow_sub, Int.negOnePow_one]
    have hh := h.comm q
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel q (q + 1) by simp),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel (q - 1) q by simp)] at hh
    rw [hh]
    simp only [Functor.map_add, Preadditive.comp_add, Functor.map_comp]
    simp only [mul_neg, mul_one, Units.neg_smul]
    abel

private noncomputable def resolutionMapHomotopy {K' : CochainComplex C ℤ}
    {Y' : CochainComplex D ℤ} {t t' : K' ⟶ K} {v v' : Y ⟶ Y'}
    (ht : Homotopy t t') (hv : Homotopy v v') :
    Homotopy
      ((resolutionFunctor H).map (X := (op K, Y)) (Y := (op K', Y')) (t.op, v))
      ((resolutionFunctor H).map (X := (op K, Y)) (Y := (op K', Y')) (t'.op, v')) :=
  ((resolutionSourceHomotopy ht).compRight (resolutionMapRight v)).trans
    ((resolutionTargetHomotopy hv).compLeft (resolutionMapLeft t'))

variable (H) in
private noncomputable def resolutionHomotopyFunctor :
    (HomotopyCategory C (.up ℤ))ᵒᵖ × HomotopyCategory D (.up ℤ) ⥤
      HomotopyCategory E (.up ℤ) where
  obj X := (HomotopyCategory.quotient E (.up ℤ)).obj
    ((resolutionFunctor H).obj (op X.1.unop.as, X.2.as))
  map f := (HomotopyCategory.quotient E (.up ℤ)).map
    ((resolutionFunctor H).map (f.1.unop.out.op, f.2.out))
  map_id X := by
    rw [← (HomotopyCategory.quotient E (.up ℤ)).map_id]
    apply HomotopyCategory.eq_of_homotopy
    exact (resolutionMapHomotopy
      (HomotopyCategory.homotopyOfEq _ _ (by simp; rfl))
      (HomotopyCategory.homotopyOfEq _ _ (by simp; rfl))).trans
        (Homotopy.ofEq ((resolutionFunctor H).map_id _))
  map_comp f g := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    apply HomotopyCategory.eq_of_homotopy
    apply resolutionMapHomotopy
    · apply HomotopyCategory.homotopyOfEq
      simp
    · apply HomotopyCategory.homotopyOfEq
      simp

private noncomputable def resolutionHomotopyFactors :
    resolutionFunctor H ⋙ HomotopyCategory.quotient E (.up ℤ) ≅
      (HomotopyCategory.quotient C (.up ℤ)).op.prod
        (HomotopyCategory.quotient D (.up ℤ)) ⋙ resolutionHomotopyFunctor H :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro X Y f
    dsimp
    simp only [comp_id, id_comp]
    apply HomotopyCategory.eq_of_homotopy
    exact resolutionMapHomotopy
      (HomotopyCategory.homotopyOutMap f.1.unop).symm
      (HomotopyCategory.homotopyOutMap f.2).symm)

end Functoriality

section SingleSource

variable [HasZeroObject C] (X : C)

set_option backward.isDefEq.respectTransparency false in
private noncomputable def resolutionSingleMap :
    resolutionObj H ((HomologicalComplex.single C (.up ℤ) 0).obj X) Y ⟶
      ((H.obj (op X)).mapHomologicalComplex (.up ℤ)).obj Y where
  f n := resolutionπ H _ Y n 0 n (zero_add n) ≫
    (H.map (HomologicalComplex.singleObjXSelf (.up ℤ) 0 X).inv.op).app (Y.X n)
  comm' n m hnm := by
    change _ ≫ (H.obj (op X)).map (Y.d n m) = _
    rw [resolutionObj_d_π_assoc H _ Y n m 0 m (zero_add m) n (m - n)
      (zero_add n) (by lia)]
    simp only [HomologicalComplex.single_obj_d, op_zero, Functor.map_zero,
      NatTrans.app_zero, comp_zero, smul_zero, sub_zero, assoc, NatTrans.naturality]

private noncomputable def resolutionSingleInv (n : ℤ) :
    (H.obj (op X)).obj (Y.X n) ⟶
      (resolutionObj H ((HomologicalComplex.single C (.up ℤ) 0).obj X) Y).X n :=
  resolutionLift H _ Y n fun p q hpq ↦ if hp : p = 0 then
    (H.map (eqToHom (congrArg
      (fun i ↦ ((HomologicalComplex.single C (.up ℤ) 0).obj X).X i) hp) ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 X).hom).op).app (Y.X n) ≫
      (H.obj (op (((HomologicalComplex.single C (.up ℤ) 0).obj X).X p))).map
        (eqToHom (congrArg Y.X (show n = q by omega)))
  else 0

set_option backward.isDefEq.respectTransparency false in
private lemma resolutionSingleMap_isIso : IsIso (resolutionSingleMap H Y X) := by
  have (n : ℤ) : IsIso ((resolutionSingleMap H Y X).f n) := by
    refine ⟨⟨resolutionSingleInv H Y X n, ?_, ?_⟩⟩
    · apply resolutionObj_hom_ext
      intro p q hpq
      by_cases hp : p = 0
      · subst p
        simp only [zero_add] at hpq
        subst q
        change ((resolutionπ H _ Y n 0 n (zero_add n) ≫
            (H.map (HomologicalComplex.singleObjXSelf (.up ℤ) 0 X).inv.op).app
              (Y.X n)) ≫ resolutionSingleInv H Y X n) ≫
              resolutionπ H _ Y n 0 (0 + n) rfl =
                𝟙 _ ≫ resolutionπ H _ Y n 0 (0 + n) rfl
        simp only [resolutionSingleInv, resolutionLift_π, eqToHom_refl,
          id_comp, op_comp, Functor.map_comp, NatTrans.comp_app, op_id, assoc]
        simp only [dite_true]
        rw [H.map_id]
        simp only [NatTrans.id_app, id_comp]
        rw [eqToHom_map]
        have hi :
            (H.map (HomologicalComplex.singleObjXSelf (.up ℤ) 0 X).inv.op).app (Y.X n) ≫
              (H.map (HomologicalComplex.singleObjXSelf (.up ℤ) 0 X).hom.op).app (Y.X n) =
                𝟙 _ := by
          rw [← NatTrans.comp_app, ← H.map_comp, ← op_comp, Iso.hom_inv_id,
            op_id, H.map_id, NatTrans.id_app]
        rw [reassoc_of% hi]
        have e : (⟨0, n, zero_add n⟩ : Triplet n) = ⟨0, 0 + n, rfl⟩ := by
          congr 1
        exact limit.π_comp_eqToHom _ (congrArg Discrete.mk e)
      · apply ((H.flip.obj (Y.X q)).map_isZero
          (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 X p hp).op).eq_of_tgt
    · simp [resolutionSingleMap, resolutionSingleInv,
        ← NatTrans.comp_app, ← Functor.map_comp, ← op_comp]
      rfl
  exact HomologicalComplex.Hom.isIso_of_components _

set_option backward.isDefEq.respectTransparency false in
private noncomputable def resolutionSingleIso :
    resolutionObj H ((HomologicalComplex.single C (.up ℤ) 0).obj X) Y ≅
      ((H.obj (op X)).mapHomologicalComplex (.up ℤ)).obj Y := by
  have := resolutionSingleMap_isIso H Y X
  exact asIso (resolutionSingleMap H Y X)

set_option backward.isDefEq.respectTransparency false in
private lemma resolutionSingleIso_naturality (X' : C) (b : X' ⟶ X)
    (Y' : CochainComplex D ℤ) (v : Y ⟶ Y') (n : ℤ) :
    ((resolutionFunctor H).map
        (X := (op ((HomologicalComplex.single C (.up ℤ) 0).obj X), Y))
        (Y := (op ((HomologicalComplex.single C (.up ℤ) 0).obj X'), Y'))
        (((HomologicalComplex.single C (.up ℤ) 0).map b).op, v)).f n ≫
        (resolutionSingleIso H Y' X').hom.f n =
      (resolutionSingleIso H Y X).hom.f n ≫ (H.map b.op).app (Y.X n) ≫
        (H.obj (op X')).map (v.f n) := by
  change _ ≫ (resolutionSingleMap H Y' X').f n =
    (resolutionSingleMap H Y X).f n ≫ _ ≫ _
  dsimp only [resolutionSingleMap]
  rw [← assoc, resolutionFunctor_map_f_π]
  simp only [assoc, NatTrans.naturality, HomologicalComplex.single_map_f_self,
    op_comp, Functor.map_comp, NatTrans.comp_app]
  simp [← NatTrans.comp_app, ← Functor.map_comp, ← op_comp, ← assoc]

end SingleSource

end ProductConstruction

section DerivedRepresentatives

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]

private theorem resolution_exists_representative (K J : CochainComplex A ℤ)
    [J.IsKInjective] (q : DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj J) :
    ∃ u : K ⟶ J, DerivedCategory.Q.map u = q := by
  obtain ⟨h, hh⟩ := (IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient A (.up ℤ)).obj K) J).surjective
      ((DerivedCategory.quotientCompQhIso A).hom.app K ≫ q ≫
        (DerivedCategory.quotientCompQhIso A).inv.app J)
  refine ⟨h.out, ?_⟩
  apply (cancel_epi ((DerivedCategory.quotientCompQhIso A).hom.app K)).mp
  rw [← DerivedCategory.quotientCompQhIso_hom_naturality,
    HomotopyCategory.quotient_map_out, hh]
  simp

private noncomputable def resolution_homotopyOfQEq {K J : CochainComplex A ℤ}
    [J.IsKInjective] {f g : K ⟶ J} (h : DerivedCategory.Q.map f = DerivedCategory.Q.map g) :
    Homotopy f g := by
  apply HomotopyCategory.homotopyOfEq
  apply (IsKInjective.Qh_map_bijective _ J).injective
  apply (cancel_mono ((DerivedCategory.quotientCompQhIso A).hom.app J)).mp
  rw [DerivedCategory.quotientCompQhIso_hom_naturality,
    DerivedCategory.quotientCompQhIso_hom_naturality, h]

private theorem resolution_exists_homotopyEquiv (J J' : CochainComplex A ℤ)
    [J.IsKInjective] [J'.IsKInjective]
    (e : DerivedCategory.Q.obj J ≅ DerivedCategory.Q.obj J')
    (v : J ⟶ J') (hv : DerivedCategory.Q.map v = e.hom) :
    ∃ E : HomotopyEquiv J J', E.hom = v := by
  obtain ⟨w, hw⟩ := resolution_exists_representative J' J e.inv
  refine ⟨⟨v, w, resolution_homotopyOfQEq ?_, resolution_homotopyOfQEq ?_⟩, rfl⟩
  · simp [hv, hw]
  · simp [hv, hw]

end DerivedRepresentatives

private lemma productHomResolutionMap_id
    {A : Type uA} [Category.{vA} A] [HasZeroMorphisms A]
    {B : Type uB} [Category.{vB} B] [HasZeroMorphisms B]
    (F : (CochainComplex A ℤ)ᵒᵖ × CochainComplex A ℤ ⥤ CochainComplex B ℤ)
    (K I : CochainComplex A ℤ) : productHomResolutionMap F (𝟙 K) (𝟙 I) = 𝟙 _ :=
  F.map_id _

private lemma productHomResolutionMap_comp
    {A : Type uA} [Category.{vA} A] [HasZeroMorphisms A]
    {B : Type uB} [Category.{vB} B] [HasZeroMorphisms B]
    (F : (CochainComplex A ℤ)ᵒᵖ × CochainComplex A ℤ ⥤ CochainComplex B ℤ)
    {K K' K'' I I' I'' : CochainComplex A ℤ}
    (t : K' ⟶ K) (t' : K'' ⟶ K') (v : I ⟶ I') (v' : I' ⟶ I'') :
    productHomResolutionMap F t v ≫ productHomResolutionMap F t' v' =
      productHomResolutionMap F (t' ≫ t) (v ≫ v') :=
  (F.map_comp _ _).symm

/-- Product Hom calculus, including its signed homotopies and resolution normalization.
Source: Stacks Project, sites-cohomology.tex, Tag 0A8X, and derived.tex, Tag 070I.
(blueprint: lem-sf-equivariant-hom-resolution-calculus).

Proof: (1) Form degree n as the integer-indexed product of H(K^p,I^(p+n)). Define
its differential by the two displayed component maps. In its square the pure terms
are zero and the mixed terms cancel, since consecutive integer signs are opposite.
(2) Apply H to the components of the two chain maps. The chain-map equations give
commutation with the differential, and product uniqueness gives the bifunctor laws.
(3) For a source homotopy h, use the component (-1)^n f^(p-1) h^p. Expanding
DS+SD cancels its two target-differential terms and leaves f(t-t').
(4) For a target homotopy h', use h'^(p+n) f^p. The source-differential terms
cancel and the remaining sum is (v-v')f. Sum these homotopies for simultaneous
changes. (5) Thus the bifunctor descends through the two homotopy quotients.
Every calculation is an identity of morphisms in B, so it retains equivariance
when the input functor, maps and homotopies are equivariant; no unrelated functor
is required to preserve products.
(6) Additivity makes H(0,-) zero. For a single source only the degree-zero factor
survives. Projection and the family consisting of the identity at zero and zero
elsewhere are inverse chain maps. Their component formulas prove both naturalities.
(7) Use lem-weil-pbc-kinjective-hom-derived, namely the bijection on homotopy
classes into a K-injective complex, to represent Q(beta) Q(a) Q(alpha)^(-1).
Its injectivity gives alpha u homotopic to a beta and uniqueness up to homotopy.
(8) Apply the source homotopy formula to this homotopy. Bifunctoriality identifies
its endpoints with the two resolution-square composites. Localization makes them
equal, independently of u. (9) Represent an identification of K-injectives and its
inverse. Injectivity of the same bijection makes their composites homotopic to
identities. Target homotopies give the induced Hom homotopy equivalence. The
mixed squares commute strictly by bifunctoriality. (10) For identity and composite
changes, compare localized representatives, cancel the middle resolution, and use
uniqueness of homotopy classes. The same argument works for every derived arrow
between K-injectives, without invertibility. No quasi-isomorphism invariance for
general source complexes or derived-functor comparison is used. -/
theorem exists_equivariantHomResolutionCalculus
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
    [HasCountableProducts B]
    (H : Aᵒᵖ ⥤ A ⥤ B) [H.Additive] [∀ X : Aᵒᵖ, (H.obj X).Additive] :
    ∃ F : (CochainComplex A ℤ)ᵒᵖ × CochainComplex A ℤ ⥤ CochainComplex B ℤ,
    ∃ π : ∀ (K I : CochainComplex A ℤ) (n p q : ℤ), p + n = q →
      ((F.obj (op K, I)).X n ⟶ (H.obj (op (K.X p))).obj (I.X q)),
      (∀ (K I : CochainComplex A ℤ) (n : ℤ),
        Nonempty (IsLimit (Fan.mk ((F.obj (op K, I)).X n)
          (fun p : ℤ ↦ π K I n p (p + n) rfl)))) ∧
      (∀ (K I : CochainComplex A ℤ) (n m p q r s : ℤ)
        (_hnm : n + 1 = m) (hpq : p + m = q) (hpr : p + n = r) (hsq : s + n = q),
        (F.obj (op K, I)).d n m ≫ π K I m p q hpq =
          π K I n p r hpr ≫ (H.obj (op (K.X p))).map (I.d r q) -
            n.negOnePow • (π K I n s q hsq ≫ (H.map (K.d p s).op).app (I.X q))) ∧
      (∀ (K K' I I' : CochainComplex A ℤ) (t : K' ⟶ K) (v : I ⟶ I')
        (n p q : ℤ) (hpq : p + n = q),
        (productHomResolutionMap F t v).f n ≫ π K' I' n p q hpq =
          π K I n p q hpq ≫ (H.map (t.f p).op).app (I.X q) ≫
            (H.obj (op (K'.X p))).map (v.f q)) ∧
      (∀ (K K' I : CochainComplex A ℤ) (t t' : K' ⟶ K) (h : Homotopy t t'),
        ∃ S : Homotopy (productHomResolutionMap F t (𝟙 I)) (productHomResolutionMap F t' (𝟙 I)),
          ∀ (n m p r q : ℤ) (_hmn : m + 1 = n) (_hrp : r + 1 = p)
            (hrq : r + n = q) (hpq : p + m = q),
            S.hom n m ≫ π K' I m p q hpq =
              n.negOnePow • (π K I n r q hrq ≫ (H.map (h.hom p r).op).app (I.X q))) ∧
      (∀ (K I I' : CochainComplex A ℤ) (v v' : I ⟶ I') (h : Homotopy v v'),
        ∃ R : Homotopy (productHomResolutionMap F (𝟙 K) v) (productHomResolutionMap F (𝟙 K) v'),
          ∀ (n m p q r : ℤ) (_hmn : m + 1 = n)
            (hpq : p + m = q) (hpr : p + n = r),
            R.hom n m ≫ π K I' m p q hpq =
              π K I n p r hpr ≫ (H.obj (op (K.X p))).map (h.hom r q)) ∧
      (∃ G : (HomotopyCategory A (.up ℤ))ᵒᵖ × HomotopyCategory A (.up ℤ) ⥤
          HomotopyCategory B (.up ℤ),
        Nonempty (F ⋙ HomotopyCategory.quotient B (.up ℤ) ≅
          (HomotopyCategory.quotient A (.up ℤ)).op.prod
            (HomotopyCategory.quotient A (.up ℤ)) ⋙ G)) ∧
      (∃ e : ∀ (X : A) (I : CochainComplex A ℤ),
          F.obj (op ((HomologicalComplex.single A (.up ℤ) 0).obj X), I) ≅
            ((H.obj (op X)).mapHomologicalComplex (.up ℤ)).obj I,
        (∀ (X : A) (I : CochainComplex A ℤ) (n : ℤ),
          (e X I).hom.f n =
            π ((HomologicalComplex.single A (.up ℤ) 0).obj X) I n 0 n (zero_add n) ≫
              (H.map (HomologicalComplex.singleObjXSelf (.up ℤ) 0 X).inv.op).app (I.X n)) ∧
        (∀ (X X' : A) (b : X' ⟶ X) (I I' : CochainComplex A ℤ) (v : I ⟶ I')
          (n : ℤ),
          (productHomResolutionMap F ((HomologicalComplex.single A (.up ℤ) 0).map b) v).f n ≫
              (e X' I').hom.f n =
            (e X I).hom.f n ≫ (H.map b.op).app (I.X n) ≫
              (H.obj (op X')).map (v.f n))) ∧
      (∀ (K L J J' : CochainComplex A ℤ) [J.IsKInjective] [J'.IsKInjective]
        (α : K ⟶ J) (β : L ⟶ J') [QuasiIso α] [QuasiIso β] (a : K ⟶ L),
        ∃ u : J ⟶ J',
          DerivedCategory.Q.map u = inv (DerivedCategory.Q.map α) ≫
            DerivedCategory.Q.map a ≫ DerivedCategory.Q.map β ∧
          Nonempty (Homotopy (α ≫ u) (a ≫ β)) ∧
          (∀ u' : J ⟶ J', Nonempty (Homotopy (α ≫ u') (a ≫ β)) →
            Nonempty (Homotopy u u')) ∧
          (∀ I : CochainComplex A ℤ,
            Nonempty (Homotopy
              (productHomResolutionMap F u (𝟙 I) ≫ productHomResolutionMap F α (𝟙 I))
              (productHomResolutionMap F β (𝟙 I) ≫ productHomResolutionMap F a (𝟙 I))) ∧
            DerivedCategory.Q.map (productHomResolutionMap F u (𝟙 I)) ≫
                DerivedCategory.Q.map (productHomResolutionMap F α (𝟙 I)) =
              DerivedCategory.Q.map (productHomResolutionMap F β (𝟙 I)) ≫
                DerivedCategory.Q.map (productHomResolutionMap F a (𝟙 I)))) ∧
      (∀ (J J' : CochainComplex A ℤ) [J.IsKInjective] [J'.IsKInjective]
        (q : DerivedCategory.Q.obj J ⟶ DerivedCategory.Q.obj J'),
        ∃ u : J ⟶ J', DerivedCategory.Q.map u = q ∧
          (∀ u' : J ⟶ J', DerivedCategory.Q.map u' = q →
            Nonempty (Homotopy u u') ∧
            ∀ K : CochainComplex A ℤ,
              DerivedCategory.Q.map (productHomResolutionMap F u (𝟙 K)) =
                DerivedCategory.Q.map (productHomResolutionMap F u' (𝟙 K)) ∧
              DerivedCategory.Q.map (productHomResolutionMap F (𝟙 K) u) =
                DerivedCategory.Q.map (productHomResolutionMap F (𝟙 K) u'))) ∧
      (∀ (I I' : CochainComplex A ℤ) [I.IsKInjective] [I'.IsKInjective]
        (e : DerivedCategory.Q.obj I ≅ DerivedCategory.Q.obj I')
        (v : I ⟶ I') (_hv : DerivedCategory.Q.map v = e.hom),
        (∃ E : HomotopyEquiv I I', E.hom = v) ∧
        ∀ K : CochainComplex A ℤ,
          ∃ E : HomotopyEquiv (F.obj (op K, I)) (F.obj (op K, I')),
            E.hom = productHomResolutionMap F (𝟙 K) v) ∧
      (∀ (K K' I I' : CochainComplex A ℤ) (t : K' ⟶ K) (v : I ⟶ I'),
        productHomResolutionMap F t (𝟙 I) ≫ productHomResolutionMap F (𝟙 K') v =
          productHomResolutionMap F (𝟙 K) v ≫ productHomResolutionMap F t (𝟙 I')) ∧
      (∀ (J : CochainComplex A ℤ) [J.IsKInjective] (u : J ⟶ J)
        (_hu : DerivedCategory.Q.map u = 𝟙 _) (K : CochainComplex A ℤ),
        DerivedCategory.Q.map (productHomResolutionMap F u (𝟙 K)) = 𝟙 _ ∧
          DerivedCategory.Q.map (productHomResolutionMap F (𝟙 K) u) = 𝟙 _) ∧
      (∀ (J J' J'' : CochainComplex A ℤ)
        [J.IsKInjective] [J'.IsKInjective] [J''.IsKInjective]
        (u : J ⟶ J') (v : J' ⟶ J'') (w : J ⟶ J'')
        (_hw : DerivedCategory.Q.map w = DerivedCategory.Q.map u ≫ DerivedCategory.Q.map v)
        (K : CochainComplex A ℤ),
        DerivedCategory.Q.map (productHomResolutionMap F w (𝟙 K)) =
            DerivedCategory.Q.map (productHomResolutionMap F v (𝟙 K)) ≫
              DerivedCategory.Q.map (productHomResolutionMap F u (𝟙 K)) ∧
          DerivedCategory.Q.map (productHomResolutionMap F (𝟙 K) w) =
            DerivedCategory.Q.map
              (productHomResolutionMap F (𝟙 K) u) ≫
              DerivedCategory.Q.map
                (productHomResolutionMap F (𝟙 K) v)) := by
  let F := resolutionFunctor H
  let hs (K K' I : CochainComplex A ℤ) (t t' : K' ⟶ K) (h : Homotopy t t') :
      Homotopy (productHomResolutionMap F t (𝟙 I))
        (productHomResolutionMap F t' (𝟙 I)) := {
    hom := resolutionSourceHom h
    zero := (resolutionSourceHomotopy (H := H) (Y := I) h).zero
    comm n := by
      simpa [productHomResolutionMap, F, resolutionFunctor, resolutionMapRight_id,
        resolutionSourceHomotopy] using
        (resolutionSourceHomotopy (H := H) (Y := I) h).comm n }
  let ht (K I I' : CochainComplex A ℤ) (v v' : I ⟶ I') (h : Homotopy v v') :
      Homotopy (productHomResolutionMap F (𝟙 K) v)
        (productHomResolutionMap F (𝟙 K) v') := {
    hom := resolutionTargetHom h
    zero := (resolutionTargetHomotopy (H := H) (K := K) h).zero
    comm n := by
      simpa [productHomResolutionMap, F, resolutionFunctor, resolutionMapLeft_id,
        resolutionTargetHomotopy] using
        (resolutionTargetHomotopy (H := H) (K := K) h).comm n }
  have lc {K K' K'' I : CochainComplex A ℤ} (t : K' ⟶ K) (t' : K'' ⟶ K') :
      productHomResolutionMap F (t' ≫ t) (𝟙 I) =
        productHomResolutionMap F t (𝟙 I) ≫ productHomResolutionMap F t' (𝟙 I) := by
    rw [productHomResolutionMap_comp, id_comp]
  have rc {K I I' I'' : CochainComplex A ℤ} (v : I ⟶ I') (v' : I' ⟶ I'') :
      productHomResolutionMap F (𝟙 K) (v ≫ v') =
        productHomResolutionMap F (𝟙 K) v ≫ productHomResolutionMap F (𝟙 K) v' := by
    rw [productHomResolutionMap_comp, id_comp]
  refine ⟨F, resolutionπ H, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro K I n
    exact ⟨resolutionIsLimit (H := H) (K := K) (Y := I) n⟩
  · intro K I n m p q r s hnm hpq hpr hsq
    exact resolutionObj_d_π H K I n m p q hpq r s hpr hsq
  · intro K K' I I' t v n p q hpq
    exact resolutionFunctor_map_f_π t v n p q hpq
  · intro K K' I t t' h
    refine ⟨hs K K' I t t' h, ?_⟩
    intro n m p r q hmn hrp hrq hpq
    exact resolutionSourceHom_π (H := H) (Y := I) h n m p r q hrq hpq
  · intro K I I' v v' h
    refine ⟨ht K I I' v v' h, ?_⟩
    intro n m p q r hmn hpq hpr
    exact resolutionTargetHom_π (H := H) (K := K) h n m p q r hpq hpr
  · exact ⟨resolutionHomotopyFunctor H, ⟨resolutionHomotopyFactors⟩⟩
  · refine ⟨fun X I ↦ resolutionSingleIso H I X, ?_, ?_⟩
    · intros
      rfl
    · intro X X' b I I' v n
      exact resolutionSingleIso_naturality H I X X' b I' v n
  · intro K L J J' hJ hJ' α β hα hβ a
    obtain ⟨u, hu⟩ := resolution_exists_representative J J'
      (inv (DerivedCategory.Q.map α) ≫ DerivedCategory.Q.map a ≫ DerivedCategory.Q.map β)
    have h : Homotopy (α ≫ u) (a ≫ β) := resolution_homotopyOfQEq (by simp [hu])
    refine ⟨u, hu, ⟨h⟩, ?_, ?_⟩
    · intro u' hu'
      apply Nonempty.intro
      apply resolution_homotopyOfQEq
      rw [hu]
      apply (cancel_epi (DerivedCategory.Q.map α)).mp
      simpa [DerivedCategory.Q.map_comp, assoc] using
        (DerivedCategory.Q_map_eq_of_homotopy _ hu'.some).symm
    · intro I
      have hh : Homotopy
          (productHomResolutionMap F u (𝟙 I) ≫ productHomResolutionMap F α (𝟙 I))
          (productHomResolutionMap F β (𝟙 I) ≫ productHomResolutionMap F a (𝟙 I)) := by
        simpa only [lc] using hs J' K I (α ≫ u) (a ≫ β) h
      exact ⟨⟨hh⟩, by simpa using DerivedCategory.Q_map_eq_of_homotopy _ hh⟩
  · intro J J' hJ hJ' q
    obtain ⟨u, hu⟩ := resolution_exists_representative J J' q
    refine ⟨u, hu, ?_⟩
    intro u' hu'
    have h : Homotopy u u' := resolution_homotopyOfQEq (hu.trans hu'.symm)
    refine ⟨⟨h⟩, ?_⟩
    intro K
    exact ⟨DerivedCategory.Q_map_eq_of_homotopy _ (hs J' J K u u' h),
      DerivedCategory.Q_map_eq_of_homotopy _ (ht K J J' u u' h)⟩
  · intro I I' hI hI' e v hv
    obtain ⟨E, hE⟩ := resolution_exists_homotopyEquiv I I' e v hv
    refine ⟨⟨E, hE⟩, ?_⟩
    intro K
    refine ⟨{
      hom := productHomResolutionMap F (𝟙 K) E.hom
      inv := productHomResolutionMap F (𝟙 K) E.inv
      homotopyHomInvId := ?_
      homotopyInvHomId := ?_ }, by change productHomResolutionMap F (𝟙 K) E.hom = _; rw [hE]⟩
    · simpa only [rc, productHomResolutionMap_id] using
        ht K I I (E.hom ≫ E.inv) (𝟙 I) E.homotopyHomInvId
    · simpa only [rc, productHomResolutionMap_id] using
        ht K I' I' (E.inv ≫ E.hom) (𝟙 I') E.homotopyInvHomId
  · intro K K' I I' t v
    simp only [productHomResolutionMap_comp, id_comp, comp_id]
  · intro J hJ u hu K
    have h : Homotopy u (𝟙 J) := resolution_homotopyOfQEq (by simpa using hu)
    constructor
    · simpa [productHomResolutionMap_id] using
        DerivedCategory.Q_map_eq_of_homotopy _ (hs J J K u (𝟙 J) h)
    · simpa [productHomResolutionMap_id] using
        DerivedCategory.Q_map_eq_of_homotopy _ (ht K J J u (𝟙 J) h)
  · intro J J' J'' hJ hJ' hJ'' u v w hw K
    have h : Homotopy w (u ≫ v) := resolution_homotopyOfQEq (by simpa using hw)
    constructor
    · simpa only [lc, Functor.map_comp] using
        DerivedCategory.Q_map_eq_of_homotopy _ (hs J'' J K w (u ≫ v) h)
    · simpa only [rc, Functor.map_comp] using
        DerivedCategory.Q_map_eq_of_homotopy _ (ht K J J'' w (u ≫ v) h)

end CochainComplex
