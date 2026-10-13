/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C3
-/
module

public import Mathlib.Algebra.Homology.HomologySequence
public import Sheaf.CategoryTheory.FilteredComplexPageDifferential
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
/-!
# The first quotient-page differential as a connecting map

Source: Stacks Project, Tag 012K, Lemma 12.24.3(1).
(blueprint: lem-sp-filtered-quotient-first-connecting).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe u v
open CategoryTheory.Limits
namespace CategoryTheory

/-- The representative differential on the first concrete quotient page is the
connecting homomorphism of the two-step filtration quotient sequence.
Source: Stacks Project, Tag 012K, Lemma 12.24.3(1).
(blueprint: lem-sp-filtered-quotient-first-connecting).

Proof. The cokernel universal properties for the inclusions F^(p+2) into
F^(p+1) into F^p construct i and j with the displayed projection squares.
The quotient-of-quotients exact sequence makes this sequence short exact.
Lift a first-page cycle representative in F^p to F^p/F^(p+2). Its differential
lies in F^(p+1), and its image in gr^(p+1) is a cycle. The homology connecting
map sends the original graded cycle to this differentiated cycle, by the
connecting-map representative formula. The two equations in hH identify
the original and differentiated quotient classes with these homology classes.
Precompose with the epic representative projection followed by the epic
boundary cokernel projection. The on_representatives equation of D then
makes both sides identical; cancellation of this epic composite proves the
stated equality. This calculation uses only one page, not a spectral sequence. -/
theorem filteredQuotient_first_connecting
    (C : Type u) [Category.{v} C] [Abelian C]
    (hBZ : ∀ (U : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite))
      (p q r : ℤ) (hr : 1 ≤ r),
      U.obj.filtration.complexBoundaries p (p + q) r ≤
        U.obj.filtration.complexCycles p (p + q) r)
    (eH : ∀ (U : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite)) (p q : ℤ),
      cokernel (Subobject.ofLE _ _ (hBZ U p q 1 (by omega))) ≅
        (U.obj.filtration.gradedPiece p).homology (p + q))
    (hH : ∀ (U : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite)) (p q : ℤ),
      ∃ (z : (U.obj.filtration.complexCycleRepresentatives p (p + q) 1 : C) ⟶
          (U.obj.filtration.complexCycles p (p + q) 1 : C))
        (g : (U.obj.filtration.complexCycleRepresentatives p (p + q) 1 : C) ⟶
          (U.obj.filtration.gradedPiece p).cycles (p + q)),
        z ≫ (U.obj.filtration.complexCycles p (p + q) 1).arrow =
          (U.obj.filtration.complexCycleRepresentatives p (p + q) 1).arrow ≫
            (U.obj.filtration.complexQuotientπ p (p + 1) (by omega)).f (p + q) ∧
        g ≫ (U.obj.filtration.gradedPiece p).iCycles (p + q) =
          (U.obj.filtration.complexCycleRepresentatives p (p + q) 1).arrow ≫
            (U.obj.filtration.complexQuotientπ p (p + 1) (by omega)).f (p + q) ∧
        Epi z ∧
        z ≫ cokernel.π (Subobject.ofLE _ _ (hBZ U p q 1 (by omega))) ≫
            (eH U p q).hom =
          g ≫ (U.obj.filtration.gradedPiece p).homologyπ (p + q))
    (U : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite))
    (D : FilteredComplexPageDifferential U.obj.obj U.obj.filtration 1) :
    ∀ p q : ℤ,
          ∃ (i : U.obj.filtration.gradedPiece (p + 1) ⟶
              U.obj.filtration.complexQuotient p (p + 2) (by omega))
            (j : U.obj.filtration.complexQuotient p (p + 2) (by omega) ⟶
              U.obj.filtration.gradedPiece p)
            (hij : i ≫ j = 0) (hS : (ShortComplex.mk i j hij).ShortExact),
            U.obj.filtration.complexQuotientπ (p + 1) (p + 1 + 1) (by omega) ≫ i =
              Subobject.ofLE (U.obj.filtration.step (p + 1))
                (U.obj.filtration.step p) (U.obj.filtration.antitone_step (by omega)) ≫
                  U.obj.filtration.complexQuotientπ p (p + 2) (by omega) ∧
            U.obj.filtration.complexQuotientπ p (p + 2) (by omega) ≫ j =
              U.obj.filtration.complexQuotientπ p (p + 1) (by omega) ∧
            D.d (p, q) (p + 1, q) ≫
                (eH U (p + 1) q).hom =
              (eH U p q).hom ≫
                hS.δ (p + q) (p + 1 + q) (by simp [ComplexShape.up]; omega) := by sorry

end CategoryTheory
