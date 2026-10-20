/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q118
-/
module

public import Sheaf.CategoryTheory.Filtration
public import WeilConjectures.Algebra.Homology.FilteredComplexSubquotients
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Category.Grp.Abelian
public import Sheaf.CategoryTheory.FiniteFiltrationInduction
public import Mathlib.Algebra.Homology.QuasiIso
import Sheaf.CategoryTheory.InjectiveTargetHomSymbol
import WeilConjectures.CategoryTheory.Abelian.Filtration

/-!
# Homotopy and graded quasi-isomorphism invariance of the shift-filtered Hom complex

Source: Varshavsky, §5.1.5, pp. 40–41; Stacks Project, Tags 05TP, 05TY, 070I and 070J
(blueprint: lem-trf-filtered-hom-complex-invariance).

The concrete Hom-complex, its shift filtration, filtered pre- and post-composition,
the two filtered homotopy invariance assertions and, for a target with injective graded
terms, the graded quasi-isomorphism invariance are stated here. The proof is postponed
to the named theorem below.
-/

@[expose] public section

set_option autoImplicit false

universe v u

open CategoryTheory CategoryTheory.Limits
open CochainComplex
open CochainComplex.HomComplex

namespace CategoryTheory

/-- A filtered homotopy between maps of filtered cochain complexes.

Source: Stacks Project, Derived Categories, before Tag 05S1 (blueprint:
lem-trf-filtered-hom-complex-invariance). -/
def FilteredHomotopy {C : Type u} [Category.{v} C] [Abelian C]
    {A B : FilteredObject (CochainComplex C ℤ)} (f g : A ⟶ B) : Prop :=
  ∃ h : Homotopy f.hom g.hom,
    ∀ i n m : ℤ, ∃ lift :
      (A.filtration.F i : CochainComplex C ℤ).X n ⟶
        (B.filtration.F i : CochainComplex C ℤ).X m,
      lift ≫ (B.filtration.F i).arrow.f m =
        (A.filtration.F i).arrow.f n ≫ h.hom n m

/-- The componentwise shift-filtration condition on a Hom-complex cochain.

Source: Varshavsky, §5.1.5 (blueprint: lem-trf-filtered-hom-complex-invariance). -/
def ShiftFilteredHomCondition {C : Type u} [Category.{v} C] [Abelian C]
    (P I : FilteredObject (CochainComplex C ℤ)) (r n : ℤ)
    (f : Cochain P.obj I.obj n) : Prop :=
  ∀ (a p q : ℤ) (hpq : p + n = q),
    ∃ lift :
      (P.filtration.F a : CochainComplex C ℤ).X p ⟶
        (I.filtration.F (a + r) : CochainComplex C ℤ).X q,
      lift ≫ (I.filtration.F (a + r)).arrow.f q =
        (P.filtration.F a).arrow.f p ≫ f.v p q hpq

/-- The filtration on a Hom-complex is exactly the shift filtration.

Source: Varshavsky, §5.1.5 (blueprint: lem-trf-filtered-hom-complex-invariance). -/
def IsShiftFilteredHomFiltration {C : Type u} [Category.{v} C] [Abelian C]
    (P I : FilteredObject (CochainComplex C ℤ))
    (F : DecreasingFiltration (HomComplex P.obj I.obj)) : Prop :=
  ∀ (r n : ℤ) (f : Cochain P.obj I.obj n),
    ((∃ x : ((Subobject.underlying.obj (F.F r)).X n : Type v),
        ((F.F r).arrow.f n).hom x = f) ↔
      ShiftFilteredHomCondition P I r n f)

/-- The component formula `(s^*f)^i = f^i s^i` for precomposition by a filtered chain map.

Source: Varshavsky, §5.1.5, pp. 40–41 (blueprint: lem-trf-filtered-hom-complex-invariance). -/
def IsPrecompositionMap {C : Type u} [Category.{v} C] [Abelian C]
    {P P' I : FilteredObject (CochainComplex C ℤ)} (s : P' ⟶ P)
    {F : DecreasingFiltration (HomComplex P.obj I.obj)}
    {G : DecreasingFiltration (HomComplex P'.obj I.obj)}
    (φ : FilteredObject.mk (HomComplex P.obj I.obj) F ⟶
      FilteredObject.mk (HomComplex P'.obj I.obj) G) : Prop :=
  ∀ (n p q : ℤ) (hpq : p + n = q) (f : Cochain P.obj I.obj n),
    ((φ.hom.f n).hom f).v p q hpq = s.hom.f p ≫ f.v p q hpq

/-- The component formula `(u_*f)^i = u^(i+n) f^i` for postcomposition by a filtered chain map.

Source: Varshavsky, §5.1.5, pp. 40–41 (blueprint: lem-trf-filtered-hom-complex-invariance). -/
def IsPostcompositionMap {C : Type u} [Category.{v} C] [Abelian C]
    {P I J : FilteredObject (CochainComplex C ℤ)} (u : I ⟶ J)
    {F : DecreasingFiltration (HomComplex P.obj I.obj)}
    {G : DecreasingFiltration (HomComplex P.obj J.obj)}
    (φ : FilteredObject.mk (HomComplex P.obj I.obj) F ⟶
      FilteredObject.mk (HomComplex P.obj J.obj) G) : Prop :=
  ∀ (n p q : ℤ) (hpq : p + n = q) (f : Cochain P.obj I.obj n),
    ((φ.hom.f n).hom f).v p q hpq = f.v p q hpq ≫ u.hom.f q

/-- A given filtered map is a filtered homotopy equivalence: it has a filtered inverse up to
filtered homotopy on both sides.

Source: Stacks Project, Derived Categories, before Tag 05S1
(blueprint: lem-trf-filtered-hom-complex-invariance). -/
def IsFilteredHomotopyEquivalenceMap {C : Type u} [Category.{v} C] [Abelian C]
    {A B : FilteredObject (CochainComplex C ℤ)} (f : A ⟶ B) : Prop :=
  ∃ g : B ⟶ A,
    FilteredHomotopy (f ≫ g) (𝟙 A) ∧ FilteredHomotopy (g ≫ f) (𝟙 B)

/-- Homotopy and graded quasi-isomorphism invariance of the shift-filtered Hom complex.

Source: Varshavsky, §5.1.5, pp. 40–41; Stacks Project, Tags 05TP, 05TY, 070I and
070J (blueprint: lem-trf-filtered-hom-complex-invariance).

Proof. The Hom-complex differential squares to zero by the componentwise formula. Uniform
finite filtration bounds follow from the finite bounds on the two input filtrations. The
componentwise pre- and post-composition formulas commute with the differential and preserve
all shift steps; associativity gives the identity and composition laws. A filtered homotopy
between source maps gives the signed homotopy `(-1)^n f h`, and a filtered homotopy between
target maps gives `k f`. The associated-graded symbol sequence for a finite filtered target
with injective graded pieces identifies each graded Hom-complex with the finite direct sum of
ordinary graded Hom-complexes. Ordinary Hom-complex cohomology is homotopy-category Hom,
and bounded-below injective targets are K-injective, so precomposition by each graded
quasi-isomorphism is a quasi-isomorphism. -/
theorem filtered_hom_complex_invariance
    {C : Type u} [Category.{v} C] [Abelian C]
    (P P' I J : FilteredObject (CochainComplex C ℤ))
    (hP : P.filtration.IsFinite ∧
      ∃ a b : ℤ, (∀ n : ℤ, n < a → IsZero (P.obj.X n)) ∧
        (∀ n : ℤ, b < n → IsZero (P.obj.X n)))
    (hP' : P'.filtration.IsFinite ∧
      ∃ a b : ℤ, (∀ n : ℤ, n < a → IsZero (P'.obj.X n)) ∧
        (∀ n : ℤ, b < n → IsZero (P'.obj.X n)))
    (hI : I.filtration.IsFinite ∧
      ∃ a : ℤ, ∀ n : ℤ, n < a → IsZero (I.obj.X n))
    (hJ : J.filtration.IsFinite ∧
      ∃ a : ℤ, ∀ n : ℤ, n < a → IsZero (J.obj.X n)) :
    ∃ FPI : DecreasingFiltration (HomComplex P.obj I.obj),
      ∃ FP'I : DecreasingFiltration (HomComplex P'.obj I.obj),
      ∃ FPIJ : DecreasingFiltration (HomComplex P.obj J.obj),
      IsShiftFilteredHomFiltration P I FPI ∧
      IsShiftFilteredHomFiltration P' I FP'I ∧
      IsShiftFilteredHomFiltration P J FPIJ ∧
      (FPI.IsFinite ∧ FP'I.IsFinite ∧ FPIJ.IsFinite) ∧
      (∃ a : ℤ, ∀ n : ℤ, n < a → IsZero ((HomComplex P.obj I.obj).X n)) ∧
      (∃ a : ℤ, ∀ n : ℤ, n < a → IsZero ((HomComplex P'.obj I.obj).X n)) ∧
      (∃ a : ℤ, ∀ n : ℤ, n < a → IsZero ((HomComplex P.obj J.obj).X n)) ∧
      (∀ (s : P' ⟶ P),
        ∃ φ :
          (FilteredObject.mk (HomComplex P.obj I.obj) FPI) ⟶
            (FilteredObject.mk (HomComplex P'.obj I.obj) FP'I),
          IsPrecompositionMap s φ) ∧
      (∀ (u : I ⟶ J),
        ∃ φ :
          (FilteredObject.mk (HomComplex P.obj I.obj) FPI) ⟶
            (FilteredObject.mk (HomComplex P.obj J.obj) FPIJ),
          IsPostcompositionMap u φ) ∧
      (∀ (s t : P' ⟶ P), FilteredHomotopy s t →
        ∃ φ ψ :
          (FilteredObject.mk (HomComplex P.obj I.obj) FPI) ⟶
            (FilteredObject.mk (HomComplex P'.obj I.obj) FP'I),
          IsPrecompositionMap s φ ∧ IsPrecompositionMap t ψ ∧ FilteredHomotopy φ ψ) ∧
      (∀ (u v : I ⟶ J), FilteredHomotopy u v →
        ∃ φ ψ :
          (FilteredObject.mk (HomComplex P.obj I.obj) FPI) ⟶
            (FilteredObject.mk (HomComplex P.obj J.obj) FPIJ),
          IsPostcompositionMap u φ ∧ IsPostcompositionMap v ψ ∧ FilteredHomotopy φ ψ) ∧
      (∀ (s : P' ⟶ P), IsFilteredHomotopyEquivalenceMap s →
        ∃ φ :
          (FilteredObject.mk (HomComplex P.obj I.obj) FPI) ⟶
            (FilteredObject.mk (HomComplex P'.obj I.obj) FP'I),
          IsPrecompositionMap s φ ∧ IsFilteredHomotopyEquivalenceMap φ) ∧
      (∀ (u : I ⟶ J), IsFilteredHomotopyEquivalenceMap u →
        ∃ φ :
          (FilteredObject.mk (HomComplex P.obj I.obj) FPI) ⟶
            (FilteredObject.mk (HomComplex P.obj J.obj) FPIJ),
          IsPostcompositionMap u φ ∧ IsFilteredHomotopyEquivalenceMap φ) ∧
      ((∀ a n : ℤ, Injective ((I.filtration.gradedPiece a).X n)) →
        ∀ (s : P' ⟶ P),
        (∀ a : ℤ, QuasiIso (FilteredObject.gradedMapSteps s a)) →
        ∃ φ :
          (FilteredObject.mk (HomComplex P.obj I.obj) FPI) ⟶
            (FilteredObject.mk (HomComplex P'.obj I.obj) FP'I),
          IsPrecompositionMap s φ ∧
          ∀ a : ℤ, QuasiIso (FilteredObject.gradedMapSteps φ a)) := by
  sorry

end CategoryTheory
