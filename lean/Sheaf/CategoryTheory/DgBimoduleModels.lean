/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q73
-/
module

public import Sheaf.CategoryTheory.DgAlgebraDerivedCategory
public import Mathlib.CategoryTheory.Monoidal.Bimod
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import Mathlib.CategoryTheory.Functor.KanExtension.Basic

/-!
# Coordinate models for balanced DG tensor and DG Hom

Source: Stacks Project, `dga.tex`, Sections tensor products and bimodule Hom,
Tags 09LN and 09LT (blueprint: def-sfb-dg-bimodule-models).

The structures specify ordinary constructions by their universal property or by
all homogeneous coordinates. They select no object from an existence theorem.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalOpposite

namespace CategoryTheory.DgAlgebra

/-- The actual right action of a right DG module, as a morphism of complexes.
Source: Stacks, definition-dgm (blueprint: def-sfb-dg-bimodule-models). -/
def rightAction (A : Algebra.{u}) (M : RightModule A) :
    (underlying A).obj M ⊗ A.X ⟶ (underlying A).obj M :=
  (ModObj.smul (M := mop A.X) (X := M.X)).unmop

/-- Evaluate a complex action on homogeneous pure tensors. Chain-map compatibility
encodes its signed Leibniz identity.
Source: Stacks, definition-dgm (blueprint: def-sfb-dg-bimodule-models). -/
def homogeneousAction (X R : Complex.{u}) (a : X ⊗ R ⟶ X) (p q : ℤ)
    (x : X.X p) (r : R.X q) : X.X (p + q) :=
  (a.f (p + q)) ((HomologicalComplex.ιTensorObj X R p q (p + q) rfl)
    (TensorProduct.tmul (ULift.{u} ℤ) x r))

/-- Homogeneous right linearity has no Koszul sign in the right-module convention.
Source: Stacks, bimodule Hom, Tag 09LN (blueprint: def-sfb-dg-bimodule-models). -/
def IsRightLinearCochain (B : Algebra.{u}) (X : Complex.{u})
    (a : X ⊗ B.X ⟶ X) (Y : RightModule B) (r : ℤ)
    (f : CochainComplex.HomComplex.Cochain X ((underlying B).obj Y) r) : Prop :=
  ∀ (p q : ℤ) (x : X.X p) (b : B.X.X q),
    HEq ((f.v (p + q) (p + q + r) rfl) (homogeneousAction X B.X a p q x b))
      (act B Y (p + r) q ((f.v p (p + r) rfl) x) b)

/-- The acyclic-source DG Hom test for homotopical injectivity. Every closed
homogeneous right-linear cochain is a boundary, in every integer degree.
Source: Stacks, Tags 09KU and 09KY (blueprint: def-sfb-dg-bimodule-models). -/
def IsHomotopicallyInjective (B : Algebra.{u}) (I : RightModule B) : Prop :=
  ∀ (C : RightModule B), ((underlying B).obj C).Acyclic →
    ∀ (r : ℤ)
      (f : CochainComplex.HomComplex.Cochain
        ((underlying B).obj C) ((underlying B).obj I) r),
      IsRightLinearCochain B ((underlying B).obj C) (rightAction B C) I r f →
      CochainComplex.HomComplex.δ r (r + 1) f = 0 →
      ∃ g : CochainComplex.HomComplex.Cochain
          ((underlying B).obj C) ((underlying B).obj I) (r - 1),
        IsRightLinearCochain B ((underlying B).obj C) (rightAction B C) I (r - 1) g ∧
        CochainComplex.HomComplex.δ (r - 1) r g = f

/-- The two balancing maps, acting first on the right-module factor.
Source: Stacks, tensor products (blueprint: def-sfb-dg-bimodule-models). -/
def tensorBalanceLeft {A B : Algebra.{u}} (N : Bimod A B) (M : RightModule A) :
    ((underlying A).obj M ⊗ A.X) ⊗ N.X ⟶ (underlying A).obj M ⊗ N.X :=
  rightAction A M ▷ N.X

/-- The other balancing map, acting on the bimodule factor after reassociation.
Source: Stacks, tensor products (blueprint: def-sfb-dg-bimodule-models). -/
def tensorBalanceRight {A B : Algebra.{u}} (N : Bimod A B) (M : RightModule A) :
    ((underlying A).obj M ⊗ A.X) ⊗ N.X ⟶ (underlying A).obj M ⊗ N.X :=
  (α_ _ _ _).hom ≫ (underlying A).obj M ◁ N.actLeft

/-- A functor is the balanced tensor functor precisely when its underlying
complex is this coequalizer, naturally in the input, and its right action is
induced by the right action on the second factor. The ambient cochain tensor
uses direct-sum totalization and the usual signed differential.
Source: Stacks, tensor products and Tag 09LN (blueprint: def-sfb-dg-bimodule-models). -/
structure BalancedTensorModel {A B : Algebra.{u}} (N : Bimod A B)
    (F : RightModule A ⥤ RightModule B) where
  π (M : RightModule A) : (underlying A).obj M ⊗ N.X ⟶ (underlying B).obj (F.obj M)
  balance (M : RightModule A) : tensorBalanceLeft N M ≫ π M =
    tensorBalanceRight N M ≫ π M
  colimit (M : RightModule A) : Nonempty (IsColimit (Cofork.ofπ (π M) (balance M)))
  naturality {M M' : RightModule A} (f : M ⟶ M') :
    ((underlying A).map f ▷ N.X) ≫ π M' = π M ≫ (underlying B).map (F.map f)
  right_action (M : RightModule A) :
    ((underlying A).obj M ◁ N.actRight) ≫ π M =
      (α_ _ _ _).inv ≫ (π M ▷ B.X) ≫ rightAction B (F.obj M)

/-- A functor is DG Hom from the fixed bimodule when every term is exactly the
space of homogeneous right-linear maps, with differential d f - (-1)^r f d,
precomposition A-action, and postcomposition on morphisms. Injectivity and the
range iff prohibit extra summands and missing homogeneous maps.
Source: Stacks, bimodule Hom, Tag 09LN (blueprint: def-sfb-dg-bimodule-models). -/
structure BimoduleHomModel {A B : Algebra.{u}} (N : Bimod A B)
    (G : RightModule B ⥤ RightModule A) where
  coordinate (Y : RightModule B) (r : ℤ) :
    ((underlying A).obj (G.obj Y)).X r →ₗ[ULift.{u} ℤ]
      CochainComplex.HomComplex.Cochain N.X ((underlying B).obj Y) r
  injective (Y : RightModule B) (r : ℤ) : Function.Injective (coordinate Y r)
  range (Y : RightModule B) (r : ℤ)
      (f : CochainComplex.HomComplex.Cochain N.X ((underlying B).obj Y) r) :
    (∃ z, coordinate Y r z = f) ↔ IsRightLinearCochain B N.X N.actRight Y r f
  differential (Y : RightModule B) (r : ℤ) (z : ((underlying A).obj (G.obj Y)).X r) :
    coordinate Y (r + 1) (((underlying A).obj (G.obj Y)).d r (r + 1) z) =
      CochainComplex.HomComplex.δ r (r + 1) (coordinate Y r z)
  action (Y : RightModule B) (r q p : ℤ)
      (z : ((underlying A).obj (G.obj Y)).X r) (a : A.X.X q) (n : N.X.X p) :
    HEq (((coordinate Y (r + q) (act A (G.obj Y) r q z a)).v p (p + (r + q)) rfl) n)
      (((coordinate Y r z).v (q + p) (q + p + r) rfl)
        ((N.actLeft.f (q + p))
          ((HomologicalComplex.ιTensorObj A.X N.X q p (q + p) rfl)
            (TensorProduct.tmul (ULift.{u} ℤ) a n))))
  naturality {Y Y' : RightModule B} (f : Y ⟶ Y') (r p : ℤ)
      (z : ((underlying A).obj (G.obj Y)).X r) (n : N.X.X p) :
    ((coordinate Y' r (((underlying A).map (G.map f)).f r z)).v p (p + r) rfl) n =
      (((underlying B).map f).f (p + r)) (((coordinate Y r z).v p (p + r) rfl) n)

/-- Ordinary currying is fixed on every pure tensor. Together with the Hom
coordinate isomorphism and tensor coequalizer this pins the actual adjunction.
Source: Stacks, Tag 09LN (blueprint: def-sfb-dg-bimodule-models). -/
def IsBimoduleCurrying {A B : Algebra.{u}} (N : Bimod A B)
    {F : RightModule A ⥤ RightModule B} {G : RightModule B ⥤ RightModule A}
    (t : BalancedTensorModel N F) (h : BimoduleHomModel N G) (a : F ⊣ G) : Prop :=
  ∀ (M : RightModule A) (Y : RightModule B) (g : F.obj M ⟶ Y)
    (p q : ℤ) (m : ((underlying A).obj M).X p) (n : N.X.X q),
    HEq
      (((h.coordinate Y p ((((underlying A).map (a.homEquiv M Y g)).f p) m)).v
        q (q + p) rfl) n)
      ((((underlying B).map g).f (p + q)) ((t.π M).f (p + q)
        ((HomologicalComplex.ιTensorObj ((underlying A).obj M) N.X p q (p + q) rfl)
          (TensorProduct.tmul (ULift.{u} ℤ) m n))))

/-- Read an element of a DG shift in the corresponding original degree.
Source: Stacks, definition-shift (blueprint: def-sfb-dg-bimodule-models). -/
def shiftedElement {A : Algebra.{u}} (k : ℤ) (M S : RightModule A)
    (e : ShiftComparison A k M S) (p : ℤ) (z : ((underlying A).obj S).X p) :
    ((underlying A).obj M).X (p + k) :=
  (((underlying A).obj M).shiftFunctorObjXIso k p (p + k) rfl).hom (e.iso.hom.f p z)

/-- The tensor shift comparison is sign free on homogeneous pure tensors.
Source: Stacks, Tag 0FQN (blueprint: def-sfb-dg-bimodule-models). -/
def IsTensorShift {A B : Algebra.{u}} (N : Bimod A B)
    {F : RightModule A ⥤ RightModule B} (t : BalancedTensorModel N F)
    (k : ℤ) (M S : RightModule A) (e : ShiftComparison A k M S)
    (eF : ShiftComparison B k (F.obj M) (F.obj S)) : Prop :=
  ∀ (p q : ℤ) (m : ((underlying A).obj S).X p) (n : N.X.X q),
    HEq
      (shiftedElement k (F.obj M) (F.obj S) eF (p + q)
        ((t.π S).f (p + q)
          ((HomologicalComplex.ιTensorObj ((underlying A).obj S) N.X p q (p + q) rfl)
            (TensorProduct.tmul (ULift.{u} ℤ) m n))))
      ((t.π M).f ((p + k) + q)
        ((HomologicalComplex.ιTensorObj ((underlying A).obj M) N.X (p + k) q
          ((p + k) + q) rfl)
          (TensorProduct.tmul (ULift.{u} ℤ) (shiftedElement k M S e p m) n)))

/-- The target shift comparison for Hom is sign free on every homogeneous map.
Source: Stacks, Tag 0FQR (blueprint: def-sfb-dg-bimodule-models). -/
def IsHomShift {A B : Algebra.{u}} (N : Bimod A B)
    {G : RightModule B ⥤ RightModule A} (h : BimoduleHomModel N G)
    (k : ℤ) (Y S : RightModule B) (e : ShiftComparison B k Y S)
    (eG : ShiftComparison A k (G.obj Y) (G.obj S)) : Prop :=
  ∀ (r p : ℤ) (z : ((underlying A).obj (G.obj S)).X r) (n : N.X.X p),
    HEq
      (((h.coordinate Y (r + k)
        (shiftedElement k (G.obj Y) (G.obj S) eG r z)).v p (p + (r + k)) rfl) n)
      (shiftedElement k Y S e (p + r) (((h.coordinate S r z).v p (p + r) rfl) n))

end CategoryTheory.DgAlgebra
