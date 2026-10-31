/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.DirectSum.Basic
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import Mathlib.CategoryTheory.Enriched.EnrichedCat
public import Mathlib.CategoryTheory.Presentable.Finite
public import Mathlib.CategoryTheory.Presentable.LocallyPresentable
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal

/-!
# Small dg categories

The plain notion of a small cochain dg category and its homogeneous composition, used by the
Stacks 09QJ situation-ABC nodes (blueprint: def-coef-small-dg-category).
Two presentations are kept as they were:
`CategoryTheory.IntegralDGCategory` (integral, explicit composition) and `CategoryTheory.Dg.Cat`
(Mathlib enrichment over cochain complexes of modules).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

section IntegralPresentation

open CategoryTheory CochainComplex DirectSum

namespace CategoryTheory

set_option linter.checkUnivs false in
/-- A small dg category over the integers, with composition in the order `b ⊗ a ↦ b a`.
The identities are closed and composition satisfies the graded Leibniz rule.
Source: Drinfeld, §§2.1, 14.1
(blueprint: def-coef-small-dg-category). -/
structure IntegralDGCategory where
  /-- The set of objects. -/
  Obj : Type u
  /-- The complex of morphisms. -/
  hom : Obj → Obj → CochainComplex AddCommGrpCat.{v} ℤ
  /-- Bilinear graded composition. -/
  comp {U V W : Obj} (p q : ℤ) :
    (hom V W).X p →+ ((hom U V).X q →+ (hom U W).X (p + q))
  /-- The identity in degree zero. -/
  unit (U : Obj) : (hom U U).X 0
  /-- Identities are cycles. -/
  d_unit (U : Obj) : (hom U U).d 0 1 (unit U) = 0
  /-- Left identity. -/
  unit_comp {U V : Obj} (p : ℤ) (a : (hom U V).X p) :
    HEq (comp 0 p (unit V) a) a
  /-- Right identity. -/
  comp_unit {U V : Obj} (p : ℤ) (a : (hom U V).X p) :
    HEq (comp p 0 a (unit U)) a
  /-- Associativity, with the canonical degree identification. -/
  assoc {T U V W : Obj} (p q r : ℤ)
      (a : (hom V W).X p) (b : (hom U V).X q) (c : (hom T U).X r) :
    HEq (comp (p + q) r (comp p q a b) c) (comp p (q + r) a (comp q r b c))
  /-- Composition is a chain map from the tensor product complex. -/
  d_comp {U V W : Obj} (p q : ℤ) (a : (hom V W).X p) (b : (hom U V).X q) :
    (hom U W).d (p + q) (p + q + 1) (comp p q a b) =
      AddEquiv.cast (M := fun i ↦ (hom U W).X i) (by omega)
        (comp (p + 1) q ((hom V W).d p (p + 1) a) b) +
      p.negOnePow • AddEquiv.cast (M := fun i ↦ (hom U W).X i) (by omega)
        (comp p (q + 1) a ((hom U V).d q (q + 1) b))

end CategoryTheory

end IntegralPresentation

section EnrichedPresentation

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace CategoryTheory.Dg

variable (R : Type u) [CommRing R]

/-- Small cochain dg categories, using Mathlib's enrichment and cochain tensor product.
Source: Tabuada §1.2 (blueprint: def-coef-small-dg-category).
The right-to-left composition is the opposite-order tensor composition, with the
Koszul interchange; thus its Leibniz sign is the degree of the left factor. -/
abbrev Cat :=
  EnrichedCat.{u, u + 1, u} (CochainComplex (ModuleCat.{u} R) ℤ)

/-- Dg functors are enriched functors (chain maps on every morphism complex).
Source: Tabuada §1.2 (blueprint: def-coef-small-dg-category). -/
abbrev Fun (C D : Cat R) :=
  EnrichedFunctor (CochainComplex (ModuleCat.{u} R) ℤ) C D

/-- The strict unit laws for dg functors.
Source: the finite-limit-sketch identification, proof steps 1--2 of
(blueprint: def-coef-small-dg-category).
Proof: the object functions are identities and the complex maps compose with identities. -/
theorem fun_unit_laws (C D : Cat R) (F : Fun R C D) :
    (EnrichedFunctor.id _ C).comp _ F = F ∧
      F.comp _ (EnrichedFunctor.id _ D) = F := by
  sorry

/-- Strict associativity of dg functors.
Source: proof steps 1--2 (blueprint: def-coef-small-dg-category).
Proof: functions compose associatively and so do maps of complexes. -/
theorem fun_assoc (B C D E : Cat R) (F : Fun R B C) (G : Fun R C D) (H : Fun R D E) :
    (F.comp _ G).comp _ H = F.comp _ (G.comp _ H) := by
  sorry

/-- The ordinary category of strict dg functors, not its enriched bicategory.
Source: Tabuada §1.2 (blueprint: def-coef-small-dg-category). -/
instance catCategory : Category (Cat R) where
  Hom := Fun R
  id C := EnrichedFunctor.id _ C
  comp F G := F.comp _ G
  id_comp F := (fun_unit_laws R _ _ F).1
  comp_id F := (fun_unit_laws R _ _ F).2
  assoc F G H := fun_assoc R _ _ _ _ F G H

/-- The morphism cochain complex.
Source: Tabuada §1.2 (blueprint: def-coef-small-dg-category). -/
abbrev hom (C : Cat R) (x y : C) : CochainComplex (ModuleCat.{u} R) ℤ :=
  x ⟶[CochainComplex (ModuleCat.{u} R) ℤ] y

/-- Forget a dg category to its object set.
Source: the object sort in proof steps 1--3
(blueprint: def-coef-small-dg-category). -/
def objects : Cat R ⥤ Type u where
  obj C := C
  map F := ↾F.obj

/-- Right-to-left cochain composition, with the Koszul interchange.
Source: Tabuada Definition 1.1 (blueprint: def-coef-small-dg-category). -/
noncomputable def comp (C : Cat R) (x y z : C) :
    hom R C y z ⊗ hom R C x y ⟶ hom R C x z :=
  (β_ _ _).hom ≫ eComp _ x y z

/-- The homogeneous identity.
Source: Tabuada Definition 1.1 (blueprint: def-coef-small-dg-category). -/
noncomputable def unit (C : Cat R) (x : C) : (hom R C x x).X 0 :=
  ((eId (CochainComplex (ModuleCat.{u} R) ℤ) x).f 0)
    ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
      (ModuleCat.of R R)).inv 1)

/-- Composition of homogeneous arrows.
Source: Tabuada Definition 1.1 (blueprint: def-coef-small-dg-category). -/
noncomputable def mul (C : Cat R) {x y z : C} (p q : ℤ)
    (b : (hom R C y z).X p) (a : (hom R C x y).X q) :
    (hom R C x z).X (p + q) :=
  ((comp R C x y z).f (p + q))
    ((HomologicalComplex.ιTensorObj (hom R C y z) (hom R C x y) p q
      (p + q) rfl) (TensorProduct.tmul R b a))

/-- The signed Leibniz rule, with right-to-left composition and arbitrary integer degrees.
Source: Tabuada Definition 1.1 and proof step 9
(blueprint: def-coef-small-dg-category).
Proof: the reverse-order composition is a chain map from the cochain tensor product.
Apply its chain-map identity to the pure tensor b tensor a and use the tensor
cochain differential. Its second summand has sign (-1)^p. -/
theorem mul_d (C : Cat R) {x y z : C} (p q : ℤ)
    (b : (hom R C y z).X p) (a : (hom R C x y).X q) :
    (hom R C x z).d (p + q) (p + q + 1) (mul R C p q b a) =
      ((hom R C x z).XIsoOfEq (by omega : (p + 1) + q = p + q + 1)).hom
        (mul R C (p + 1) q ((hom R C y z).d p (p + 1) b) a) +
      (p.negOnePow : ℤ) •
        ((hom R C x z).XIsoOfEq (by omega : p + (q + 1) = p + q + 1)).hom
          (mul R C p (q + 1) b ((hom R C x y).d q (q + 1) a)) := by
  sorry

/-- Composition `b a` of homogeneous arrows of opposite degrees, read in degree zero.
Source: Tabuada, arXiv:0710.4303, Chapter 1, §1.3.1, definition of K, printed p. 27
(composition `gf`, `fg` in the differentials of `r₀,r₁`); right-to-left composition
(blueprint: def-coef-small-dg-category). -/
noncomputable def mulAt {C : Cat R} {x y z : C} {p q : ℤ}
    (hpq : p + q = 0) (b : (hom R C y z).X p) (a : (hom R C x y).X q) :
    (hom R C x z).X 0 :=
  (hom R C x z).XIsoOfEq (by omega : p + q = 0) |>.hom (mul R C p q b a)

/-- Composition `b a` of homogeneous arrows, read in a prescribed degree `n = p + q`.
Source: Tabuada, arXiv:0710.4303, Chapter 1, §1.3.1, definition of K, printed p. 27
(the composites `f r₀` and `r₁ f` in the differential of `t`)
(blueprint: def-coef-small-dg-category). -/
noncomputable def mulAtDegree {C : Cat R} {x y z : C} {p q n : ℤ}
    (b : (hom R C y z).X p) (a : (hom R C x y).X q) (h : p + q = n) :
    (hom R C x z).X n :=
  (hom R C x z).XIsoOfEq h |>.hom (mul R C p q b a)

/-- The class of a degree-zero arrow `u` is invertible in `H⁰`: a closed degree-zero `v` and
degree `-1` arrows `a,b` with `da = vu - 1` and `db = uv - 1`.
Source: Tabuada, arXiv:0710.4303, Chapter 1, Proposition 1.7 and Proposition 1.13,
printed pp. 27 and 32 (blueprint: def-coef-small-dg-category). -/
def IsH0Iso {C : Cat R} {x y : C} (u : (hom R C x y).X 0) : Prop :=
  ∃ (v : (hom R C y x).X 0) (a : (hom R C x x).X (-1))
    (b : (hom R C y y).X (-1)),
    (hom R C y x).d 0 1 v = 0 ∧
      (hom R C x x).d (-1) 0 a = mulAt R rfl v u - unit R C x ∧
      (hom R C y y).d (-1) 0 b = mulAt R rfl u v - unit R C y

end CategoryTheory.Dg

end EnrichedPresentation
