/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q119
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.CategoryTheory.StrictRoosModel
public import Sheaf.Algebra.Homology.PrincipalKoszulQuotientTowers
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic

/-! # Signed double Roos interchange and tensor augmentation coherence

Source: blueprint sec-smooth-purity/sk-lem-sp-tower, completeness calculation;
Stacks Tags 014E, 012Z, 03EK and 0941
(blueprint: lem-sp-signed-double-roos-tensor-exchange).

The Koszul index j denotes the positive exponent j+1. The tensor is the existing
unbounded total tensor. Its standard signed symmetry transports the published
left-tensor Koszul augmentation to the right-tensor presentation used here.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

universe uC vC r w

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

namespace CategoryTheory.SignedDoubleRoos

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  (R : Sheaf J CommRingCat.{r})

/-- The existing module category, with its coefficient universe explicit.
Source: Stacks 03EK (blueprint: lem-sp-signed-double-roos-tensor-exchange). -/
abbrev Modules := ringedSiteModules.{r}
  ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)

/-- Unbounded complexes in the existing module category.
Source: Stacks 014E (blueprint: lem-sp-signed-double-roos-tensor-exchange). -/
abbrev Complex := CochainComplex (Modules R) ℤ

/-- Strict inverse sequences, indexed by the nonnegative integers.
Source: Stacks 0941 (blueprint: lem-sp-signed-double-roos-tensor-exchange). -/
abbrev Tower := ℕᵒᵖ ⥤ Complex R

/-- The published degreewise rearrangement, made functorial using its published map.
Source: Stacks 0941 (blueprint: lem-sp-signed-double-roos-tensor-exchange). -/
def towerComplex : Tower R ⥤ CochainComplex (ℕᵒᵖ ⥤ Modules R) ℤ where
  obj := koszulTowerComplex R
  map := koszulTowerComplexMap R
  map_id X := by ext k n; rfl
  map_comp f g := by ext k n; rfl

/-- The existing strict Roos functor in the tower-of-complexes presentation.
Source: Stacks 0941 (blueprint: lem-sp-signed-double-roos-tensor-exchange). -/
abbrev roos : Tower R ⥤ Complex R := towerComplex R ⋙ roosF

/-- Evaluation in Roos degree zero, using the published cone evaluation.
Source: Stacks 0941 (blueprint: lem-sp-signed-double-roos-tensor-exchange). -/
def evaluation (X : Tower R) (n : ℕ) : (roos R).obj X ⟶ X.obj (op n) :=
  roosEval (koszulTowerComplex R X) n

/-- The integral degree of a Roos coordinate (false = unshifted, true = shifted).
Source: Stacks 014E (blueprint: lem-sp-signed-double-roos-tensor-exchange). -/
def degree (p : Bool) : ℤ := if p then 1 else 0

/-- Projection onto one of the two specified Roos coordinates and one product factor.
Source: Stacks 014E (blueprint: lem-sp-signed-double-roos-tensor-exchange). -/
def coordinate (X : Tower R) (p : Bool) (k : ℤ) (n : ℕ) :
    ((roos R).obj X).X k ⟶ (X.obj (op n)).X (k - degree p) := by
  cases p
  · simpa only [degree, Bool.false_eq_true, ↓reduceIte, sub_zero] using
      (evaluation R X n).f k
  · exact (CochainComplex.mappingCocone.snd (roosU (koszulTowerComplex R X))).v
      k (k - 1) (by omega) ≫
      (Pi.π (fun n : ℕ ↦ (koszulTowerComplex R X).asFunctor.obj (op n)) n).f (k - 1)

/-- First take Roos in the inner index and then in the outer index.
Source: Stacks 014E, twice (blueprint: lem-sp-signed-double-roos-tensor-exchange). -/
abbrev rows : (ℕᵒᵖ ⥤ Tower R) ⥤ Complex R :=
  (Functor.whiskeringRight ℕᵒᵖ (Tower R) (Complex R)).obj (roos R) ⋙ roos R

/-- Reverse the indices before taking the same iterated Roos functor.
Source: Stacks 014E (blueprint: lem-sp-signed-double-roos-tensor-exchange). -/
abbrev columns : (ℕᵒᵖ ⥤ Tower R) ⥤ Complex R :=
  flipFunctor _ _ _ ⋙ rows R

/-- The four row coordinates, in the order (0,0), (0,1), (1,0), (1,1).
Source: Stacks 014E (blueprint: lem-sp-signed-double-roos-tensor-exchange). -/
def rowCoordinate (X : ℕᵒᵖ ⥤ Tower R) (p q : Bool) (k : ℤ) (n j : ℕ) :
    ((rows R).obj X).X k ⟶ ((X.obj (op n)).obj (op j)).X
      (k - degree p - degree q) :=
  coordinate R (X ⋙ roos R) p k n ≫
    coordinate R (X.obj (op n)) q (k - degree p) j

/-- The column coordinates with output indexed in the original n,j order.
Source: Stacks 014E (blueprint: lem-sp-signed-double-roos-tensor-exchange). -/
def columnCoordinate (X : ℕᵒᵖ ⥤ Tower R) (p q : Bool) (k : ℤ) (n j : ℕ) :
    ((columns R).obj X).X k ⟶ ((X.obj (op n)).obj (op j)).X
      (k - degree p - degree q) :=
  rowCoordinate R X.flip q p k j n ≫
    eqToHom (congrArg (fun a : ℤ ↦ ((X.obj (op n)).obj (op j)).X a)
      (by omega))

/-- Evaluate the inner Roos coordinate, naturally in the remaining index.
Source: Stacks 0941 (blueprint: lem-sp-signed-double-roos-tensor-exchange). -/
def innerEvaluation (X : ℕᵒᵖ ⥤ Tower R) (j : ℕ) :
    X ⋙ roos R ⟶ X.flip.obj (op j) where
  app n := evaluation R (X.obj n) j
  naturality n m f := by
    exact roosEval_natural (koszulTowerComplexMap R (X.map f)) j

/-- The induced derived interchange, conjugated by the chosen normalized comparisons.
In particular, taking both comparisons from strictRoosComparison gives the signed
isomorphism of the two iterated total derived limits, with their prescribed evaluations.
Source: Stacks 0941 (blueprint: lem-sp-signed-double-roos-tensor-exchange). -/
def derivedInterchange [HasDerivedCategory.{w} (Modules R)]
    (X : ℕᵒᵖ ⥤ Tower R) (β : (rows R).obj X ≅ (columns R).obj X)
    {Dnj Djn : DerivedCategory.{w} (Modules R)}
    (ρnj : DerivedCategory.Q.obj ((rows R).obj X) ≅ Dnj)
    (ρjn : DerivedCategory.Q.obj ((columns R).obj X) ≅ Djn) : Dnj ≅ Djn :=
  ρnj.symm ≪≫ DerivedCategory.Q.mapIso β ≪≫ ρjn

/-- The published principal Koszul tower, tensored on the right of its input.
Source: Stacks 012Z, 03EK (blueprint: lem-sp-signed-double-roos-tensor-exchange). -/
def tensorTower (t : (SheafOfModules.unit
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)).sections) :
    Complex R ⥤ Tower R :=
  curriedTensor (Complex R) ⋙
    (Functor.whiskeringLeft ℕᵒᵖ (Complex R) (Complex R)).obj (principalKoszulTower R t)

/-- Transport the published 1 tensor x augmentation by the standard signed symmetry.
Its degree-zero component is x tensor 1.
Source: Stacks 012Z, 03EK (blueprint: lem-sp-signed-double-roos-tensor-exchange). -/
def strictAugmentation (P : Complex R) (t : (SheafOfModules.unit
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)).sections) :
    (Functor.const ℕᵒᵖ).obj P ⟶ (tensorTower R t).obj P :=
  koszulStrictAugmentation R P t ≫
    Functor.whiskerLeft (principalKoszulTower R t)
      (BraidedCategory.tensorLeftIsoTensorRight P).inv

/-- Completion in the strict Roos model, using the actual total tensor tower.
Source: Stacks 0941, 012Z (blueprint: lem-sp-signed-double-roos-tensor-exchange). -/
abbrev completion (t : (SheafOfModules.unit
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)).sections) :
    Complex R ⥤ Complex R := tensorTower R t ⋙ roos R

/-- The strict unit with the prescribed degree-zero inclusion and zero shifted component.
Source: Stacks 0941 (blueprint: lem-sp-signed-double-roos-tensor-exchange). -/
def augmentation (P : Complex R) (t : (SheafOfModules.unit
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)).sections) :
    P ⟶ (completion R t).obj P :=
  roosAugment (X := koszulTowerComplex R ((tensorTower R t).obj P))
    (fun j ↦ (strictAugmentation R P t).app (op j))
    (fun j ↦ ((strictAugmentation R P t).naturality
      (homOfLE (Nat.le_succ j)).op).symm.trans (Category.id_comp _))

end CategoryTheory.SignedDoubleRoos
