/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C3
-/
module

public import Sheaf.CategoryTheory.FilteredHomologyExactCouple
public import Sheaf.CategoryTheory.FilteredComplexPageDifferential
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
/-!
# Derived homology-couple pages as representative quotients

Source: Stacks Project, Tag 012K, Lemma 12.24.2; Tag 011R.
(blueprint: lem-sp-filtered-homology-couple-quotient-pages).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe u v
open CategoryTheory.Limits
namespace CategoryTheory

/-- Identify the derived pages of the concrete homology couple with cycles modulo
boundaries, including the base normalization and representative differentials.
Source: Stacks Project, Tag 012K, Lemma 12.24.2; Tag 011R.
(blueprint: lem-sp-filtered-homology-couple-quotient-pages).

Proof. At stage zero the E term is homology of the graded piece. The epic
representative normalization hH gives its inverse identification with the
first cycle-boundary quotient, and cancellation gives the base equation.
Induct on s. A representative in F^p has differential in F^(p+s+1); the
connecting map of the original short exact sequence followed by the derived
quotient map sends its class to the class of that differential. The derived
maps' restriction equations preserve this representative formula. The kernel
consists of classes whose differential becomes a current boundary. Subtract
a representative of that boundary to put the differential in F^(p+s+2).
Thus the kernel is the image of the successor cycles modulo current boundaries.
The incoming image consists exactly of differentials from F^(p-s-1), modulo
current boundaries, so is successor boundaries modulo current boundaries.
The abelian quotient-of-quotients isomorphism identifies homology with
Z_(s+2)/B_(s+2), giving the next comparison. Its differential differentiates
a lifted representative by the derived-couple restriction equations, hence
agrees with the specified D by cancellation of the epic representative cover.
This constructs the isomorphisms inductively; no arbitrary spectral sequence
or choices of its page-homology identifications occur. -/
theorem filteredHomologyCouple_quotient_pages
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
    (D : ∀ (r : ℤ) (hr : 1 ≤ r),
      FilteredComplexPageDifferential U.obj.obj U.obj.filtration r) :
    ∃ (eQ : ∀ (s : ℕ) (p q : ℤ),
        ((filteredHomologyExactCouple U.obj.obj U.obj.filtration).pageCouple s).E
            (2 * p + q) (-p) ≅
          cokernel (Subobject.ofLE _ _ (hBZ U p q (s + 1) (by omega)))),
      (∀ p q : ℤ, HEq (eQ 0 p q).hom
        (filteredHomologyEIso U.obj.obj U.obj.filtration p q ≪≫ (eH U p q).symm).hom) ∧
      (∀ (s : ℕ) (p q : ℤ),
        (eQ s p q).hom ≫ (D (s + 1) (by omega)).d (p, q)
            (p + (s + 1), q - (s + 1) + 1) =
          ((filteredHomologyExactCouple U.obj.obj U.obj.filtration).pageCouple s).d
              (2 * p + q) (-p) ≫
            eqToHom (congrArg₂
              ((filteredHomologyExactCouple U.obj.obj U.obj.filtration).pageCouple s).E
              (show 2 * p + q + 2 + s =
                2 * (p + (s + 1)) + (q - (s + 1) + 1) by omega)
              (show -p - 1 - s = -(p + (s + 1)) by omega)) ≫
              (eQ s (p + (s + 1)) (q - (s + 1) + 1)).hom) := by sorry

end CategoryTheory
