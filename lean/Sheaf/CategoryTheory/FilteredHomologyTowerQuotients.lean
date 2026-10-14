/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V2
-/
module

public import Sheaf.CategoryTheory.FilteredHomologyExactCouple
public import Sheaf.CategoryTheory.ExactCoupleConvergence
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Sheaf.Algebra.Homology.FilteredComplexSubquotients
import Sheaf.CategoryTheory.ExactCouple
import Sheaf.CategoryTheory.FilteredComplexDifferentialRepresentativesCover
import Sheaf.CategoryTheory.FilteredComplexPageDifferential
import Sheaf.CategoryTheory.FilteredComplexSuccessorBoundariesImage
import Sheaf.CategoryTheory.FilteredComplexSuccessorCyclesCover
import Sheaf.CategoryTheory.FilteredHomologyCoupleData
import Sheaf.CategoryTheory.FilteredHomologyTowerDifferential
import Sheaf.CategoryTheory.FiniteCycleFormula

/-! # Representative comparisons with the canonical exact-couple tower

Source: Stacks Project, Tags 012K and 011R.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe u v
open CategoryTheory.Limits
namespace CategoryTheory

/-- Graded filtered cycles cover the canonical tower cycles, and their composites
with the tower projections have exactly the boundary kernels. This is only the
object and quotient comparison, without a differential assertion.
Source: Stacks Project, Tag 012K, cycle/boundary formulas in Lemma 12.24.2;
Tag 011R, the canonical derived-couple quotient construction.
(blueprint: lem-sp-filtered-homology-tower-quotients).

Proof. First construct j and t at every stage, before proving epimorphy.
Since r=s+1 is at least one, an r-cycle has zero graded differential;
its graded inclusion therefore factors uniquely through iCycles, defining j.
Compose j with graded homology and the inverse initial E identification.
The finiteCycle_formula identifies T.Z s with the inverse image, under the
initial connecting f, of the image of the s-fold incoming alpha. On an
r-cycle representative, the connecting class is represented by its differential
in F^(p+s+1); its inclusion into F^(p+1) is exactly that incoming alpha
iterate on homology. Thus the initial E class factors through T.Z s.
This calculation descends from the epic cycle-representative projection,
because the graded representative kernel maps to zero in initial homology.
Factor uniquely through the monic tower inclusion to define t, for every s.
This supplies the whole normalized family required by the differential lemma,
without assuming any quotient comparison or the epimorphy being proved.

Now induct on s for the epic projection composites and their kernels.
At zero, hH and epic cancellation identify the composite with the initial
cokernel projection followed by eH and the inverse initial E identification;
it is epic and has kernel B_1. At stage s, its cokernel universal property
identifies the page with Z_(s+1)/B_(s+1). Apply the tower differential lemma
to the already constructed families and cancel an epic representative cover
to identify the canonical differential with the representative differential.
The successor-cycle cover identifies its outgoing kernel as the image of
Z_(s+2) modulo B_(s+1); the successor-boundary image identifies its incoming
image as B_(s+2) modulo B_(s+1). Quotienting this kernel by the incoming
image therefore gives an epic map from Z_(s+2), with kernel B_(s+2).
The tower cycleLift_comm and projection_succ equations identify that map
with t at stage s+1 followed by the tower projection: cancel the preceding
kernel inclusion and use the monic normalization of t to identify the lifts.
This proves both assertions at s+1. All representative lifts are made after
pullback along epimorphisms, so no projectivity or infinite sums are required.
The monic normalization fixes j and t uniquely; no arbitrary data is chosen. -/
theorem filteredHomology_tower_quotients
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
 :
    ∃ (j : ∀ (s : ℕ) (p q : ℤ),
      (U.obj.filtration.complexCycles p (p + q) (s + 1) : C) ⟶
        (U.obj.filtration.gradedPiece p).cycles (p + q))
      (t : ∀ (s : ℕ) (p q : ℤ),
      (U.obj.filtration.complexCycles p (p + q) (s + 1) : C) ⟶
        ((filteredHomologyExactCouple U.obj.obj U.obj.filtration).cycleBoundaryTower.Z
          s (2 * p + q) (-p) : C)),
      (∀ (s : ℕ) (p q : ℤ),
      j s p q ≫ (U.obj.filtration.gradedPiece p).iCycles (p + q) =
        (U.obj.filtration.complexCycles p (p + q) (s + 1)).arrow) ∧
      (∀ (s : ℕ) (p q : ℤ),
      t s p q ≫
          ((filteredHomologyExactCouple U.obj.obj U.obj.filtration).cycleBoundaryTower.Z
            s (2 * p + q) (-p)).arrow ≫
          (filteredHomologyEIso U.obj.obj U.obj.filtration p q).hom =
        j s p q ≫ (U.obj.filtration.gradedPiece p).homologyπ (p + q)) ∧
      (∀ (s : ℕ) (p q : ℤ), Epi (t s p q ≫
          (filteredHomologyExactCouple U.obj.obj U.obj.filtration).cycleBoundaryTower.projection
            s (2 * p + q) (-p))) ∧
      (∀ (s : ℕ) (p q : ℤ), kernelSubobject (t s p q ≫
          (filteredHomologyExactCouple U.obj.obj U.obj.filtration).cycleBoundaryTower.projection
            s (2 * p + q) (-p)) =
        imageSubobject (Subobject.ofLE _ _ (hBZ U p q (s + 1) (by omega)))) := by sorry

end CategoryTheory
