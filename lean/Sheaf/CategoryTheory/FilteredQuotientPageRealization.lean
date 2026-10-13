/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G3
-/
module

public import Sheaf.Algebra.Homology.FilteredComplexSubquotients
public import Sheaf.CategoryTheory.ExactCoupleConvergence
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Sheaf.CategoryTheory.FilteredComplexPageDifferential
import Sheaf.CategoryTheory.FilteredQuotientCanonicalFunctor
import Sheaf.CategoryTheory.FilteredQuotientCanonicalStructure

/-!
# Exact-couple realization of the cycle-boundary quotient pages

Source: Stacks Project, Homology, Tag 012K; blueprint spectral-object construction,
steps 1--4 (blueprint: lem-sp-filtered-quotient-page-realization).
-/

@[expose] public section

universe u v
open CategoryTheory.Limits
namespace CategoryTheory

set_option linter.unusedVariables false in
/-- Realize the concrete positive quotient pages, naturally in filtered maps.
Source: Stacks Project, Tag 012K, and blueprint thm-sp-spectral-object-yields,
steps 1--4 (blueprint: lem-sp-filtered-quotient-page-realization).

Proof: Form the short exact sequences F^(p+1) → F^p → gr^p and their homology
long exact sequences. At (P,Q) put D=H^(P+Q)(F^(-Q)) and E=H^(P+Q)(gr^(-Q)).
The inclusion, connecting and quotient maps satisfy the three exactness conditions.
Derive the couple recursively, and reindex by (P,Q)=(2p+q,-p). The resulting
r-th differential is represented by x ↦ dx on the cycle-boundary quotients.
The kernel consists of representatives whose differential is in F^(p+r+1), and
its boundaries are the classes of d(F^(p-r)); hence page homology is the next
quotient, as in the positive-page construction. These representative comparisons
provide eZ and eC. On page one the epic representative projection determines the
homology comparison uniquely; the hypothesis hH therefore gives exactly eH.
The connecting map of the three-step quotient sequence represents this first
page differential. Restrictions of filtered maps commute with the three maps of
the initial couple, so coupleMorphism induces maps on all derived pages. On the
quotient page these are precisely the maps induced by the graded cycle restriction:
compose with the epic boundary quotient and the monic cycle inclusion to check
this characterization. Their uniqueness gives identity and composition, hence S,
and yields the displayed naturality for every k satisfying that characterization.
The initial couple maps are the inclusion and quotient by construction, giving
the alpha and initialG equations. No stabilization or abutment is used. -/
theorem filteredQuotient_page_realization
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
          g ≫ (U.obj.filtration.gradedPiece p).homologyπ (p + q)) :
    ∃ (S : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite) ⥤
        CohomologicalSpectralSequence C 1)
      (eZ : ∀ (U : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite))
        (p q r : ℤ) (hr : 1 ≤ r),
        ((S.obj U).page r hr).X (p, q) ≅ cokernel (Subobject.ofLE _ _ (hBZ U p q r hr))),
      (∀ (U V : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite)) (t : U ⟶ V)
        (p q r : ℤ) (hr : 1 ≤ r)
      (s : ∀ a : ℤ, (U.obj.filtration.step a : CochainComplex C ℤ) ⟶
        (V.obj.filtration.step a : CochainComplex C ℤ))
      (g : U.obj.filtration.gradedPiece p ⟶ V.obj.filtration.gradedPiece p)
      (kz : (U.obj.filtration.complexCycles p (p + q) r : C) ⟶
        (V.obj.filtration.complexCycles p (p + q) r : C))
      (k : cokernel (Subobject.ofLE _ _ (hBZ U p q r hr)) ⟶
        cokernel (Subobject.ofLE _ _ (hBZ V p q r hr)))
      (hs : ∀ i : ℤ, s i ≫ (V.obj.filtration.step i).arrow =
        (U.obj.filtration.step i).arrow ≫ t.hom.hom)
      (hg : U.obj.filtration.complexQuotientπ p (p + 1) (by omega) ≫ g =
        s p ≫ V.obj.filtration.complexQuotientπ p (p + 1) (by omega))
      (hkz : kz ≫ (V.obj.filtration.complexCycles p (p + q) r).arrow =
        (U.obj.filtration.complexCycles p (p + q) r).arrow ≫ g.f (p + q))
      (hk : cokernel.π (Subobject.ofLE _ _ (hBZ U p q r hr)) ≫ k =
        kz ≫ cokernel.π (Subobject.ofLE _ _ (hBZ V p q r hr))),
        ((S.map t).hom r hr).f (p, q) ≫ (eZ V p q r hr).hom =
          (eZ U p q r hr).hom ≫ k) ∧
      ∀ U : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite),
        (∀ p q : ℤ,
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
            ((S.obj U).page 1).d (p, q) (p + 1, q) ≫
                (eZ U (p + 1) q 1 (by omega) ≪≫ eH U (p + 1) q).hom =
              (eZ U p q 1 (by omega) ≪≫ eH U p q).hom ≫
                hS.δ (p + q) (p + 1 + q) (by simp [ComplexShape.up]; omega)) ∧
        (∃ (X : BigradedExactCouple C 0)
          (eD : ∀ P Q : ℤ, X.D P Q ≅
            (U.obj.filtration.step (-Q) : CochainComplex C ℤ).homology (P + Q))
          (eC : ∀ (s : ℕ) (p q : ℤ),
            (X.pageCouple s).E (2 * p + q) (-p) ≅
              ((S.obj U).page (s + 1) (by omega)).X (p, q)) ,
          (∀ P Q : ℤ,
            X.alpha P Q ≫ (eD (P - 1) (Q + 1)).hom =
              (eD P Q).hom ≫ HomologicalComplex.homologyMap
                (Subobject.ofLE (U.obj.filtration.step (-Q))
                  (U.obj.filtration.step (-(Q + 1)))
                  (U.obj.filtration.antitone_step (by omega))) (P + Q) ≫
                eqToHom (by rw [show P - 1 + (Q + 1) = P + Q by omega])) ∧
          (∀ P Q : ℤ,
            X.initialG P Q ≫ eqToHom (by congr 1 <;> omega) ≫
                (eC 0 (-Q) (P + 2 * Q)).hom ≫
                (eZ U (-Q) (P + 2 * Q) 1 (by omega) ≪≫
                  eH U (-Q) (P + 2 * Q)).hom ≫
                eqToHom (by
                  rw [show -Q + (P + 2 * Q) = P + Q by omega]
                  rfl) =
              (eD P Q).hom ≫ HomologicalComplex.homologyMap
                (U.obj.filtration.complexQuotientπ (-Q) (-Q + 1) (by omega)) (P + Q)) ∧
          (∀ (s : ℕ) (p q : ℤ),
            (eC s p q).hom ≫
                ((S.obj U).page (s + 1) (by omega)).d (p, q)
                  (p + (s + 1), q - (s + 1) + 1) =
              (X.pageCouple s).d (2 * p + q) (-p) ≫
                eqToHom (by congr 1 <;> omega) ≫
                  (eC s (p + (s + 1)) (q - (s + 1) + 1)).hom)) := by
  classical
  have hD (U : ObjectProperty.FullSubcategory
      (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite))
      (r : ℤ) (hr : 1 ≤ r) :
      ∃! D : FilteredComplexPageDifferential U.obj.obj U.obj.filtration r, True :=
    filteredComplex_page_differential_exists_unique U.obj.obj U.obj.filtration r hr
  let D := fun U r hr ↦ (hD U r hr).choose
  obtain ⟨S, eZ, hd, hnat⟩ := filteredQuotient_canonical_functor C hBZ D
  refine ⟨S, eZ, hnat, ?_⟩
  intro U
  exact filteredQuotient_canonical_structure C hBZ eH hH U (S.obj U) (eZ U) (D U)
    (hd U)

end CategoryTheory
