/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q124
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Homology.RingedDerivedTensorNative
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Tactic.Ring

/-! # Signed coherence of total cochain tensors

Source: Stacks Project, Tag 0FPQ and More on Algebra, integer sign rules
(blueprint: lem-pur-total-tensor-signed-coherence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe c v u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory WeilConjectures
namespace CategoryTheory.RingedDerivedNative

section Formulas

universe uA vA
variable {A : Type uA} [Category.{vA} A] [Preadditive A] [HasZeroObject A]
  [MonoidalCategory A] [MonoidalPreadditive A] [BraidedCategory A]
  [∀ (X Y : GradedObject ℤ A), X.HasTensor Y]
  [∀ X : A, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).obj X)]
  [∀ X : A, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).flip.obj X)]
  [∀ (W X Y Z : GradedObject ℤ A), GradedObject.HasTensor₄ObjExt W X Y Z]
  [∀ (X Y Z : GradedObject ℤ A), GradedObject.HasGoodTensor₁₂Tensor X Y Z]
  [∀ (X Y Z : GradedObject ℤ A), GradedObject.HasGoodTensorTensor₂₃ X Y Z]

/-- The canonical extraction of two integer shifts, second factor first.
Source: Stacks 0FPQ and More on Algebra, item-shift-tensor, with shifted-degree normalization
(blueprint: lem-pur-total-tensor-signed-coherence). -/
def totalTensorShiftIso (E F : CochainComplex A ℤ) (a b : ℤ) :
    (E⟦a⟧) ⊗ (F⟦b⟧) ≅ (E ⊗ F)⟦a + b⟧ :=
  CochainComplex.mapBifunctorShift₂Iso (E⟦a⟧) F (curriedTensor _) b ≪≫
    (shiftFunctor _ b).mapIso (CochainComplex.mapBifunctorShift₁Iso E F (curriedTensor _) a) ≪≫
    ((shiftFunctorAdd _ a b).app (E ⊗ F)).symm

/-- The prescribed shifted-degree formula for a map extracting two shifts.
Source: Stacks 0FPQ and More on Algebra, item-shift-tensor, shifted-degree normalization
(blueprint: lem-pur-total-tensor-signed-coherence). -/
def totalTensorShiftFormula (E F : CochainComplex A ℤ) (a b : ℤ)
    (f : (E⟦a⟧) ⊗ (F⟦b⟧) ⟶ (E ⊗ F)⟦a + b⟧) : Prop :=
  ∀ (p q n : ℤ) (h : p + q = n) (h' : (p + a) + (q + b) = n + (a + b)),
    HomologicalComplex.ιTensorObj (E⟦a⟧) (F⟦b⟧) p q n h ≫ f.f n =
      (b * p).negOnePow •
        HomologicalComplex.ιTensorObj E F (p + a) (q + b) (n + (a + b)) h'

/-- The unsigned reassociation formula, as a predicate on an arbitrary chain map.
Source: Stacks 0FPQ, associativity hint
(blueprint: lem-pur-total-tensor-signed-coherence). -/
def totalTensorAssociatorFormula (E F G : CochainComplex A ℤ)
    (f : (E ⊗ F) ⊗ G ⟶ E ⊗ (F ⊗ G)) : Prop :=
  ∀ (p q r pq qr n : ℤ) (hpq : p + q = pq) (hqr : q + r = qr)
    (hn : pq + r = n) (hn' : p + qr = n),
    (HomologicalComplex.ιTensorObj E F p q pq hpq ▷ G.X r) ≫
      HomologicalComplex.ιTensorObj (E ⊗ F) G pq r n hn ≫ f.f n =
    (α_ (E.X p) (F.X q) (G.X r)).hom ≫
      (E.X p ◁ HomologicalComplex.ιTensorObj F G q r qr hqr) ≫
      HomologicalComplex.ιTensorObj E (F ⊗ G) p qr n hn'

/-- The Koszul symmetry formula, as a predicate on an arbitrary chain map.
Source: Stacks 0FPQ and More on Algebra, item-flip-tensor-product
(blueprint: lem-pur-total-tensor-signed-coherence). -/
def totalTensorSymmetryFormula (E F : CochainComplex A ℤ)
    (f : E ⊗ F ⟶ F ⊗ E) : Prop :=
  ∀ (p q n : ℤ) (h : p + q = n) (h' : q + p = n),
    HomologicalComplex.ιTensorObj E F p q n h ≫ f.f n =
      (p * q).negOnePow • ((β_ (E.X p) (F.X q)).hom ≫
        HomologicalComplex.ιTensorObj F E q p n h')

/-- The shift formula clause of signed total-tensor coherence.
Source: Stacks 0FPQ and More on Algebra, integer sign rules
(blueprint: lem-pur-total-tensor-signed-coherence). -/
def totalTensorCoherence_shift_formula : Prop :=
  ∀ (E F : CochainComplex A ℤ) (a b : ℤ),
  totalTensorShiftFormula (A := A) E F a b (totalTensorShiftIso (A := A) E F a b).hom

/-- The associator formula clause of signed total-tensor coherence.
Source: Stacks 0FPQ and More on Algebra, integer sign rules
(blueprint: lem-pur-total-tensor-signed-coherence). -/
def totalTensorCoherence_associator_formula : Prop :=
  ∀ (E F G : CochainComplex A ℤ),
  totalTensorAssociatorFormula (A := A) E F G (α_ E F G).hom

/-- The symmetry formula clause of signed total-tensor coherence.
Source: Stacks 0FPQ and More on Algebra, integer sign rules
(blueprint: lem-pur-total-tensor-signed-coherence). -/
def totalTensorCoherence_symmetry_formula : Prop :=
  ∀ (E F : CochainComplex A ℤ),
  totalTensorSymmetryFormula (A := A) E F (β_ E F).hom

/-- The shift inverse clause of signed total-tensor coherence.
Source: Stacks 0FPQ and More on Algebra, integer sign rules
(blueprint: lem-pur-total-tensor-signed-coherence). -/
def totalTensorCoherence_shift_inverse : Prop :=
  ∀ (E F : CochainComplex A ℤ) (a b p q n : ℤ)
    (h : p + q = n) (h' : (p + a) + (q + b) = n + (a + b)),
    HomologicalComplex.ιTensorObj E F (p + a) (q + b) (n + (a + b)) h' ≫
      (totalTensorShiftIso (A := A) E F a b).inv.f n =
    (b * p).negOnePow • HomologicalComplex.ιTensorObj (E⟦a⟧) (F⟦b⟧) p q n h

/-- The associator inverse clause of signed total-tensor coherence.
Source: Stacks 0FPQ and More on Algebra, integer sign rules
(blueprint: lem-pur-total-tensor-signed-coherence). -/
def totalTensorCoherence_associator_inverse : Prop :=
  ∀ (E F G : CochainComplex A ℤ)
    (p q r pq qr n : ℤ) (hpq : p + q = pq) (hqr : q + r = qr)
    (hn : pq + r = n) (hn' : p + qr = n),
    (E.X p ◁ HomologicalComplex.ιTensorObj F G q r qr hqr) ≫
      HomologicalComplex.ιTensorObj E (F ⊗ G) p qr n hn' ≫ (α_ E F G).inv.f n =
    (α_ (E.X p) (F.X q) (G.X r)).inv ≫
      (HomologicalComplex.ιTensorObj E F p q pq hpq ▷ G.X r) ≫
      HomologicalComplex.ιTensorObj (E ⊗ F) G pq r n hn

/-- The symmetry inverse clause of signed total-tensor coherence.
Source: Stacks 0FPQ and More on Algebra, integer sign rules
(blueprint: lem-pur-total-tensor-signed-coherence). -/
def totalTensorCoherence_symmetry_inverse : Prop :=
  ∀ (E F : CochainComplex A ℤ),
  (β_ E F).inv = (β_ F E).hom

/-- The shift natural clause of signed total-tensor coherence.
Source: Stacks 0FPQ and More on Algebra, integer sign rules
(blueprint: lem-pur-total-tensor-signed-coherence). -/
def totalTensorCoherence_shift_natural : Prop :=
  ∀ (E E' F F' : CochainComplex A ℤ)
  (f : E ⟶ E') (g : F ⟶ F') (a b : ℤ),
  ((f⟦a⟧') ⊗ₘ (g⟦b⟧')) ≫ (totalTensorShiftIso (A := A) E' F' a b).hom =
    (totalTensorShiftIso (A := A) E F a b).hom ≫ (f ⊗ₘ g)⟦a + b⟧'

/-- The associator natural clause of signed total-tensor coherence.
Source: Stacks 0FPQ and More on Algebra, integer sign rules
(blueprint: lem-pur-total-tensor-signed-coherence). -/
def totalTensorCoherence_associator_natural : Prop :=
  ∀ (E E' F F' G G' : CochainComplex A ℤ)
  (f : E ⟶ E') (g : F ⟶ F') (h : G ⟶ G'),
  ((f ⊗ₘ g) ⊗ₘ h) ≫ (α_ E' F' G').hom = (α_ E F G).hom ≫ (f ⊗ₘ (g ⊗ₘ h))

/-- The symmetry natural clause of signed total-tensor coherence.
Source: Stacks 0FPQ and More on Algebra, integer sign rules
(blueprint: lem-pur-total-tensor-signed-coherence). -/
def totalTensorCoherence_symmetry_natural : Prop :=
  ∀ (E E' F F' : CochainComplex A ℤ)
  (f : E ⟶ E') (g : F ⟶ F'),
  (f ⊗ₘ g) ≫ (β_ E' F').hom = (β_ E F).hom ≫ (g ⊗ₘ f)

/-- The shift unique clause of signed total-tensor coherence.
Source: Stacks 0FPQ and More on Algebra, integer sign rules
(blueprint: lem-pur-total-tensor-signed-coherence). -/
def totalTensorCoherence_shift_unique : Prop :=
  ∀ (E F : CochainComplex A ℤ) (a b : ℤ)
  (f : (E⟦a⟧) ⊗ (F⟦b⟧) ⟶ (E ⊗ F)⟦a + b⟧),
  totalTensorShiftFormula (A := A) E F a b f →
    f = (totalTensorShiftIso (A := A) E F a b).hom

/-- The associator unique clause of signed total-tensor coherence.
Source: Stacks 0FPQ and More on Algebra, integer sign rules
(blueprint: lem-pur-total-tensor-signed-coherence). -/
def totalTensorCoherence_associator_unique : Prop :=
  ∀ (E F G : CochainComplex A ℤ)
  (f : (E ⊗ F) ⊗ G ⟶ E ⊗ (F ⊗ G)),
  totalTensorAssociatorFormula (A := A) E F G f → f = (α_ E F G).hom

/-- The symmetry unique clause of signed total-tensor coherence.
Source: Stacks 0FPQ and More on Algebra, integer sign rules
(blueprint: lem-pur-total-tensor-signed-coherence). -/
def totalTensorCoherence_symmetry_unique : Prop :=
  ∀ (E F : CochainComplex A ℤ)
  (f : E ⊗ F ⟶ F ⊗ E), totalTensorSymmetryFormula (A := A) E F f → f = (β_ E F).hom

/-- The associativity clause of signed total-tensor coherence.
Source: Stacks 0FPQ and More on Algebra, integer sign rules
(blueprint: lem-pur-total-tensor-signed-coherence). -/
def totalTensorCoherence_associativity : Prop :=
  ∀ (E F G : CochainComplex A ℤ) (a b d : ℤ),
  ((totalTensorShiftIso (A := A) E F a b).hom ▷ (G⟦d⟧)) ≫
      (totalTensorShiftIso (A := A) (E ⊗ F) G (a + b) d).hom ≫
      (α_ E F G).hom⟦(a + b) + d⟧' =
    (α_ (E⟦a⟧) (F⟦b⟧) (G⟦d⟧)).hom ≫
      ((E⟦a⟧) ◁ (totalTensorShiftIso (A := A) F G b d).hom) ≫
      (totalTensorShiftIso (A := A) E (F ⊗ G) a (b + d)).hom ≫
      (eqToIso (congrArg (fun k : ℤ ↦ (E ⊗ (F ⊗ G))⟦k⟧)
        (Int.add_assoc a b d).symm)).hom

/-- The symmetry clause of signed total-tensor coherence.
Source: Stacks 0FPQ and More on Algebra, integer sign rules
(blueprint: lem-pur-total-tensor-signed-coherence). -/
def totalTensorCoherence_symmetry : Prop :=
  ∀ (E F : CochainComplex A ℤ) (a b : ℤ),
  (totalTensorShiftIso (A := A) E F a b).hom ≫ (β_ E F).hom⟦a + b⟧' =
    (a * b).negOnePow • ((β_ (E⟦a⟧) (F⟦b⟧)).hom ≫
      (totalTensorShiftIso (A := A) F E b a).hom ≫
      (eqToIso (congrArg (fun k : ℤ ↦ (F ⊗ E)⟦k⟧) (Int.add_comm b a))).hom)

/-- The associativity coefficients clause of signed total-tensor coherence.
Source: Stacks 0FPQ and More on Algebra, integer sign rules
(blueprint: lem-pur-total-tensor-signed-coherence). -/
def totalTensorCoherence_associativity_coefficients : Prop :=
  ∀ (b d p q : ℤ),
  (b * p + d * (p + q)).negOnePow = (d * q + (b + d) * p).negOnePow

/-- The symmetry coefficients clause of signed total-tensor coherence.
Source: Stacks 0FPQ and More on Algebra, integer sign rules
(blueprint: lem-pur-total-tensor-signed-coherence). -/
def totalTensorCoherence_symmetry_coefficients : Prop :=
  ∀ (a b p q : ℤ),
  (b * p + (p + a) * (q + b)).negOnePow = (a * b + p * q + a * q).negOnePow

/-- All summand, inverse, naturality, uniqueness and signed coherence identities.
The tensor, associator and symmetry are the native direct-sum total constructions;
`totalTensorShiftIso` is constructed from the recorded integer bifunctor comparisons.
Source: Stacks 0FPQ and More on Algebra, integer sign rules, with shifted-degree normalization
(blueprint: lem-pur-total-tensor-signed-coherence). -/
structure TotalTensorSignedCoherence : Prop where
  shift_formula : totalTensorCoherence_shift_formula (A := A)
  associator_formula : totalTensorCoherence_associator_formula (A := A)
  symmetry_formula : totalTensorCoherence_symmetry_formula (A := A)
  shift_inverse : totalTensorCoherence_shift_inverse (A := A)
  associator_inverse : totalTensorCoherence_associator_inverse (A := A)
  symmetry_inverse : totalTensorCoherence_symmetry_inverse (A := A)
  shift_natural : totalTensorCoherence_shift_natural (A := A)
  associator_natural : totalTensorCoherence_associator_natural (A := A)
  symmetry_natural : totalTensorCoherence_symmetry_natural (A := A)
  shift_unique : totalTensorCoherence_shift_unique (A := A)
  associator_unique : totalTensorCoherence_associator_unique (A := A)
  symmetry_unique : totalTensorCoherence_symmetry_unique (A := A)
  associativity : totalTensorCoherence_associativity (A := A)
  symmetry : totalTensorCoherence_symmetry (A := A)
  associativity_coefficients : totalTensorCoherence_associativity_coefficients
  symmetry_coefficients : totalTensorCoherence_symmetry_coefficients

omit [BraidedCategory A]
  [∀ (W X Y Z : GradedObject ℤ A), GradedObject.HasTensor₄ObjExt W X Y Z] in
private theorem tensorInclusionCast (E F : CochainComplex A ℤ)
    (p q n m : ℤ) (h : p + q = n) (e : n = m) :
    HomologicalComplex.ιTensorObj E F p q n h ≫
      eqToHom (congrArg (fun k ↦ (E ⊗ F).X k) e) =
        HomologicalComplex.ιTensorObj E F p q m (h.trans e) := by
  subst m
  simp

omit [BraidedCategory A]
  [∀ (W X Y Z : GradedObject ℤ A), GradedObject.HasTensor₄ObjExt W X Y Z] in
private theorem tripleInclusionCast (E F G : CochainComplex A ℤ)
    (p q r s s' n m : ℤ) (hs : q + r = s) (hs' : q + r = s')
    (hn : p + s = n) (hn' : p + s' = m) (e : n = m) :
    (E.X p ◁ HomologicalComplex.ιTensorObj F G q r s hs) ≫
      HomologicalComplex.ιTensorObj E (F ⊗ G) p s n hn ≫
        eqToHom (congrArg (fun k ↦ (E ⊗ (F ⊗ G)).X k) e) =
    (E.X p ◁ HomologicalComplex.ιTensorObj F G q r s' hs') ≫
      HomologicalComplex.ιTensorObj E (F ⊗ G) p s' m hn' := by
  have es : s = s' := hs.symm.trans hs'
  cases e
  cases es
  simp only [eqToHom_refl, Category.comp_id]

omit [BraidedCategory A]
  [∀ (W X Y Z : GradedObject ℤ A), GradedObject.HasTensor₄ObjExt W X Y Z] in
@[reassoc]
private theorem shiftFormula (E F : CochainComplex A ℤ) (a b : ℤ) :
    totalTensorShiftFormula E F a b (totalTensorShiftIso E F a b).hom := by
  intro p q n h h'
  dsimp only [totalTensorShiftIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, Iso.app_inv, HomologicalComplex.comp_f]
  erw [CochainComplex.ι_mapBifunctorShift₂Iso_hom_f_assoc
    _ _ _ _ _ _ _ h (q + b) (n + b) rfl rfl]
  simp only [CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq,
    eqToIso_refl, Iso.refl_hom, Iso.refl_inv, CochainComplex.shiftFunctor_map_f',
    Category.comp_id, Linear.units_smul_comp, Category.assoc]
  erw [CochainComplex.ι_mapBifunctorShift₁Iso_hom_f_assoc
    _ _ _ _ _ _ _ (by omega) (p + a) ((n + b) + a) rfl rfl]
  simp only [CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq,
    eqToIso_refl, Iso.refl_hom, Iso.refl_inv, Category.id_comp,
    CochainComplex.shiftFunctorAdd_inv_app_f, eqToIso.hom]
  erw [tensorInclusionCast E F (p + a) (q + b) ((n + b) + a)
    (n + (a + b)) (by omega) (by omega)]
  simp only [curriedTensor_obj_map, curriedTensor_map_app, Int.mul_comm]
  erw [whiskerLeft_id, id_whiskerRight, Category.id_comp, Category.id_comp]

omit [BraidedCategory A]
  [∀ (W X Y Z : GradedObject ℤ A), GradedObject.HasTensor₄ObjExt W X Y Z] in
@[reassoc]
private theorem associatorFormula (E F G : CochainComplex A ℤ) :
    totalTensorAssociatorFormula E F G (α_ E F G).hom := by
  intro p q r pq qr n hpq hqr hn hn'
  simpa only [CochainComplex.Monoidal.ι₁₂_eq E F G p q r pq n hpq hn,
    CochainComplex.Monoidal.ι₂₃_eq E F G p q r qr n hqr hn', Category.assoc] using
    CochainComplex.Monoidal.ι₁₂_associator_hom E F G p q r n (by omega)

@[reassoc]
private theorem symmetryFormula (E F : CochainComplex A ℤ) :
    totalTensorSymmetryFormula E F (β_ E F).hom := by
  intro p q n h h'
  exact CochainComplex.Monoidal.ι_braiding_hom p q n h

omit [BraidedCategory A]
  [∀ (W X Y Z : GradedObject ℤ A), GradedObject.HasTensor₄ObjExt W X Y Z] in
private theorem shiftUnique : totalTensorCoherence_shift_unique (A := A) := by
  intro E F a b f hf
  ext n : 1
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  change p + q = n at h
  exact (hf p q n h (by omega)).trans (shiftFormula E F a b p q n h (by omega)).symm

private theorem symmetryUnique : totalTensorCoherence_symmetry_unique (A := A) := by
  intro E F f hf
  ext n : 1
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  change p + q = n at h
  exact (hf p q n h (by omega)).trans (symmetryFormula E F p q n h (by omega)).symm

omit [BraidedCategory A]
  [∀ (W X Y Z : GradedObject ℤ A), GradedObject.HasTensor₄ObjExt W X Y Z] in
private theorem associatorUnique : totalTensorCoherence_associator_unique (A := A) := by
  intro E F G f hf
  ext n : 1
  apply HomologicalComplex.mapBifunctor₁₂.hom_ext
  intro p q r h
  change p + q + r = n at h
  erw [CochainComplex.Monoidal.ι₁₂_eq E F G p q r (p + q) n rfl h]
  simp only [Category.assoc]
  exact (hf p q r (p + q) (q + r) n rfl rfl h (by omega)).trans
    (associatorFormula E F G p q r (p + q) (q + r) n rfl rfl h (by omega)).symm

omit [BraidedCategory A]
  [∀ (W X Y Z : GradedObject ℤ A), GradedObject.HasTensor₄ObjExt W X Y Z] in
private theorem shiftInverse : totalTensorCoherence_shift_inverse (A := A) := by
  intro E F a b p q n h h'
  apply (cancel_mono ((totalTensorShiftIso E F a b).hom.f n)).mp
  erw [Category.assoc, ← HomologicalComplex.comp_f, Iso.inv_hom_id,
    HomologicalComplex.id_f, Category.comp_id, Linear.units_smul_comp,
    shiftFormula E F a b p q n h h', smul_smul, Int.units_mul_self, one_smul]

omit [BraidedCategory A]
  [∀ (W X Y Z : GradedObject ℤ A), GradedObject.HasTensor₄ObjExt W X Y Z] in
private theorem associatorInverse : totalTensorCoherence_associator_inverse (A := A) := by
  intro E F G p q r pq qr n hpq hqr hn hn'
  simpa only [CochainComplex.Monoidal.ι₁₂_eq E F G p q r pq n hpq hn,
    CochainComplex.Monoidal.ι₂₃_eq E F G p q r qr n hqr hn', Category.assoc] using
    CochainComplex.Monoidal.ι₂₃_associator_inv E F G p q r n (by omega)

omit [BraidedCategory A] in
private theorem tensorMapFormula {E E' F F' : CochainComplex A ℤ}
    (f : E ⟶ E') (g : F ⟶ F') (p q n : ℤ) (h : p + q = n) :
    HomologicalComplex.ιTensorObj E F p q n h ≫ (f ⊗ₘ g).f n =
      (f.f p ⊗ₘ g.f q) ≫ HomologicalComplex.ιTensorObj E' F' p q n h := by
  simp only [tensorHom_def, HomologicalComplex.comp_f, Category.assoc]
  erw [CochainComplex.Monoidal.ι_whiskerRight_assoc,
    CochainComplex.ιTensorObj_whiskerLeft_f]

omit [BraidedCategory A] in
private theorem shiftNatural : totalTensorCoherence_shift_natural (A := A) := by
  intro E E' F F' f g a b
  ext n : 1
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  change p + q = n at h
  simp only [HomologicalComplex.comp_f]
  erw [← Category.assoc, tensorMapFormula, Category.assoc,
    shiftFormula E' F' a b p q n h (by omega)]
  erw [shiftFormula_assoc E F a b p q n h (by omega)]
  simp only [CochainComplex.shiftFunctor_map_f', Linear.comp_units_smul,
    Linear.units_smul_comp]
  erw [tensorMapFormula]

private theorem associativityCoefficients : totalTensorCoherence_associativity_coefficients := by
  intro b d p q
  congr 1
  ring

private theorem symmetryCoefficients : totalTensorCoherence_symmetry_coefficients := by
  intro a b p q
  erw [show b * p + (p + a) * (q + b) =
    2 * (b * p) + (a * b + p * q + a * q) by ring]
  erw [Int.negOnePow_add, Int.negOnePow_two_mul, one_mul]

private theorem symmetryCoherence : totalTensorCoherence_symmetry (A := A) := by
  intro E F a b
  ext n : 1
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  change p + q = n at h
  simp only [HomologicalComplex.comp_f, HomologicalComplex.units_smul_f_apply,
    CochainComplex.shiftFunctor_map_f']
  erw [← Category.assoc, shiftFormula E F a b p q n h (by omega)]
  erw [Linear.units_smul_comp, symmetryFormula E F (p + a) (q + b)
    (n + (a + b)) (by omega) (by omega)]
  erw [Linear.comp_units_smul, ← Category.assoc,
    symmetryFormula (E⟦a⟧) (F⟦b⟧) p q n h (by omega)]
  simp only [Linear.units_smul_comp, Category.assoc]
  erw [shiftFormula_assoc F E b a q p n (by omega) (by omega)]
  simp only [Linear.comp_units_smul, Linear.units_smul_comp, smul_smul,
    ← Int.negOnePow_add]
  erw [symmetryCoefficients]
  simp only [HomologicalComplex.eqToHom_f, eqToIso.hom, ← add_assoc]
  erw [tensorInclusionCast F E (q + b) (p + a) (n + (b + a))
    (n + (a + b)) (by omega) (by omega)]
  rfl

omit [BraidedCategory A]
  [∀ (W X Y Z : GradedObject ℤ A), GradedObject.HasTensor₄ObjExt W X Y Z] in
private theorem associativityCoherence : totalTensorCoherence_associativity (A := A) := by
  intro E F G a b d
  ext n : 1
  apply HomologicalComplex.mapBifunctor₁₂.hom_ext
  intro p q r h
  change p + q + r = n at h
  erw [CochainComplex.Monoidal.ι₁₂_eq (E⟦a⟧) (F⟦b⟧) (G⟦d⟧)
    p q r (p + q) n rfl h]
  simp only [HomologicalComplex.comp_f, CochainComplex.shiftFunctor_map_f', Category.assoc]
  erw [CochainComplex.Monoidal.ι_whiskerRight_assoc]
  erw [← comp_whiskerRight_assoc]
  erw [shiftFormula E F a b p q (p + q) rfl (by omega)]
  simp only [Units.smul_def, zsmul_whiskerRight, Preadditive.zsmul_comp]
  erw [shiftFormula_assoc (E ⊗ F) G (a + b) d (p + q) r n h (by omega)]
  simp only [Units.smul_def, Preadditive.comp_zsmul, Preadditive.zsmul_comp]
  erw [associatorFormula E F G (p + a) (q + b) (r + d)
    ((p + q) + (a + b)) ((q + b) + (r + d)) (n + ((a + b) + d))
    (by omega) rfl (by omega) (by omega)]
  erw [associatorFormula_assoc (E⟦a⟧) (F⟦b⟧) (G⟦d⟧) p q r
    (p + q) (q + r) n rfl rfl h (by omega)]
  erw [CochainComplex.ιTensorObj_whiskerLeft_f_assoc,
    ← whiskerLeft_comp_assoc]
  erw [shiftFormula F G b d q r (q + r) rfl (by omega)]
  simp only [Units.smul_def, whiskerLeft_zsmul, Preadditive.zsmul_comp,
    Preadditive.comp_zsmul]
  erw [shiftFormula_assoc E (F ⊗ G) a (b + d) p (q + r) n (by omega) (by omega)]
  simp only [Units.smul_def, Preadditive.comp_zsmul, Preadditive.zsmul_comp,
    smul_smul, ← Units.val_mul, ← Int.negOnePow_add]
  erw [associativityCoefficients]
  simp only [eqToIso.hom, HomologicalComplex.eqToHom_f]
  congr 2
  exact (tripleInclusionCast E F G (p + a) (q + b) (r + d)
    ((q + r) + (b + d)) ((q + b) + (r + d)) (n + (a + (b + d)))
    (n + ((a + b) + d)) (by omega) rfl (by omega) (by omega) (by omega)).symm

end Formulas

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
  (R : Sheaf J CommRingCat.{max c v u})

/-- Signed coherence for arbitrary unbounded complexes on a small ringed site.
Source: Stacks 0FPQ; More on Algebra, item-shift-tensor and item-flip-tensor-product
(blueprint: lem-pur-total-tensor-signed-coherence).

Proof:
1. In the module universe max(c,v,u), the site is small. Additive sheafification exists
and has locally bijective equivalences. Set sheafification preserves finite products;
lifting its adjunction to abelian group objects identifies its underlying set functor
with abelian sheafification (the three sheafification nodes in the DAG).
2. By the sheaf-tensor bilinear universal property, maps agree if they agree on local
pure tensors. Tensor preserves coproducts in each variable. Apply this in each total
degree to obtain equality tests for double and triple tensors. For nested tensors,
use product-preserving set sheafification on the inner tensor, rather than assuming
that global sections are generated by global pure tensors. No boundedness is needed.
3. Apply lem-sf-ringed-tensor-complex-constraints: the native associator is unsigned
and the braiding has coefficient (-1)^(pq). Reassociation preserves the differential's
three coefficients 1, (-1)^p, (-1)^(p+q). The flip commutes with the differential since
(p+1)q=pq+q and p+p(q+1) is congruent to pq modulo 2. Reverse reassociation is inverse;
the two flips multiply to (-1)^(pq+qp)=1. Step 2 gives uniqueness.
4. Apply lem-weil-pbc-total-tensor-integer-shifts to the additive tensor bifunctor.
Extract b from the second factor of E[a] tensor F[b], then a from the first factor,
then identify [a][b] with [a+b]. This is the actual definition above, with coefficient
(-1)^(bp) on shifted first degree p.
5. In the chain-map square for this extraction the dx coefficients have exponents
a+b(p+1) and bp+a+b; the dy exponents are p+b+bp and bp+a+b+p+a, equal modulo 2.
Reverse reindexing uses the same bp, not b(p+a); composing gives (-1)^(2bp)=1.
6. Chain maps preserve degree. Both naturality routes on pure sections therefore
produce (-1)^(bp) f(x) tensor g(y), or (-1)^(pq) g(y) tensor f(x), or
f(x) tensor (g(y) tensor h(z)), respectively. Step 2 proves the naturality identities.
7. For triple shifted degrees p,q,r, the left extraction has exponent bp+d(p+q),
whereas the right extraction has exponent dq+(b+d)p. These are equal as integers.
The underlying output is x tensor (y tensor z), so step 2 proves associativity.
8. The symmetry square has exponents bp+(p+a)(q+b) and ab+pq+aq; they differ by
2bp. Hence their signs agree, and step 2 proves the signed symmetry identity.
9. Integer negOnePow is parity for every integer. Reindexing by negative integers
is still bijective; coproducts and all calculations apply to unbounded complexes.
No flatness, localization or degree-zero restriction is involved. -/
theorem totalTensor_signed_coherence :
    TotalTensorSignedCoherence (A := Modules.{c, v, u} J R) := by
  refine
    { shift_formula := shiftFormula
      associator_formula := associatorFormula
      symmetry_formula := symmetryFormula
      shift_inverse := shiftInverse
      associator_inverse := associatorInverse
      symmetry_inverse := ?_
      shift_natural := shiftNatural
      associator_natural := fun _ _ _ _ _ _ f g h ↦ associator_naturality f g h
      symmetry_natural := fun _ _ _ _ f g ↦ BraidedCategory.braiding_naturality f g
      shift_unique := shiftUnique
      associator_unique := associatorUnique
      symmetry_unique := symmetryUnique
      associativity := associativityCoherence
      symmetry := symmetryCoherence
      associativity_coefficients := associativityCoefficients
      symmetry_coefficients := symmetryCoefficients }
  intro E F
  apply (cancel_epi (β_ E F).hom).mp
  erw [Iso.hom_inv_id]
  exact (complex_symmetry E F).symm

end CategoryTheory.RingedDerivedNative
