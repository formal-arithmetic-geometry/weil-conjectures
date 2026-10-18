/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C3
-/
module

public import Sheaf.CategoryTheory.FilteredHomologyExactCouple
public import Sheaf.CategoryTheory.FilteredComplexPageDifferential
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Sheaf.CategoryTheory.FilteredHomologyTowerQuotients
import Sheaf.CategoryTheory.FilteredHomologyTowerDifferential
import Sheaf.CategoryTheory.FilteredComplexDifferentialRepresentativesCover
import WeilConjectures.CategoryTheory.ExactCoupleConvergence
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

set_option linter.unusedVariables false in
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
              (eQ s (p + (s + 1)) (q - (s + 1) + 1)).hom) := by
  classical
  obtain ⟨j, t, hj, ht, hepi, hker⟩ :=
    filteredHomology_tower_quotients C hBZ eH hH U
  let X := filteredHomologyExactCouple U.obj.obj U.obj.filtration
  let T := X.cycleBoundaryTower
  let Q := fun (s : ℕ) (p q : ℤ) ↦ t s p q ≫ T.projection s (2 * p + q) (-p)
  have hQepi (s : ℕ) (p q : ℤ) : Epi (Q s p q) := hepi s p q
  have hQzero (s : ℕ) (p q : ℤ) :
      Subobject.ofLE _ _ (hBZ U p q (s + 1) (by omega)) ≫ Q s p q = 0 := by
    apply (kernelSubobject_factors_iff _ _).mp
    rw [hker s p q]
    simpa only [Category.id_comp] using
      imageSubobject_factors_comp_self
        (Subobject.ofLE _ _ (hBZ U p q (s + 1) (by omega))) (𝟙 _)
  have hQcoker (s : ℕ) (p q : ℤ) :=
    ((ShortComplex.exact_iff_image_eq_kernel
      (ShortComplex.mk _ _ (hQzero s p q))).mpr (hker s p q).symm).gIsCokernel
  let eQ := fun (s : ℕ) (p q : ℤ) ↦
    (hQcoker s p q).coconePointUniqueUpToIso
      (cokernelIsCokernel (Subobject.ofLE _ _ (hBZ U p q (s + 1) (by omega))))
  have hQ (s : ℕ) (p q : ℤ) :
      Q s p q ≫ (eQ s p q).hom =
        cokernel.π (Subobject.ofLE _ _ (hBZ U p q (s + 1) (by omega))) :=
    (hQcoker s p q).comp_coconePointUniqueUpToIso_hom
      (cokernelIsCokernel _) WalkingParallelPair.one
  refine ⟨eQ, ?_, ?_⟩
  · intro p q
    apply heq_of_eq
    apply (cancel_epi (Q 0 p q)).mp
    rw [hQ]
    have hbase : Q 0 p q ≫ (filteredHomologyEIso U.obj.obj U.obj.filtration p q).hom =
        j 0 p q ≫ (U.obj.filtration.gradedPiece p).homologyπ (p + q) := by
      simpa only [Q, T.projection_zero, Category.assoc] using ht 0 p q
    obtain ⟨z, g, hz, hg, hzEpi, hzg⟩ := hH U p q
    have hzj : z ≫ j 0 p q = g := by
      apply (cancel_mono ((U.obj.filtration.gradedPiece p).iCycles (p + q))).mp
      rw [Category.assoc, hj]
      exact hz.trans hg.symm
    have hnorm : j 0 p q ≫ (U.obj.filtration.gradedPiece p).homologyπ (p + q) =
        cokernel.π (Subobject.ofLE _ _ (hBZ U p q 1 (by omega))) ≫ (eH U p q).hom := by
      apply (cancel_epi z).mp
      rw [← Category.assoc z, hzj]
      exact hzg.symm
    simp only [Iso.trans_hom, Iso.symm_hom, ← Category.assoc]
    rw [hbase, hnorm]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rfl
  · intro s p q
    have hij : (ComplexShape.up' ((s : ℤ) + 1, 1 - ((s : ℤ) + 1))).Rel
        (p, q) (p + (s + 1), q - (s + 1) + 1) := by
      change (p, q) + ((s : ℤ) + 1, 1 - ((s : ℤ) + 1)) = _
      have hq : q + (1 - ((s : ℤ) + 1)) = q - ((s : ℤ) + 1) + 1 := by omega
      exact congrArg (fun k : ℤ ↦ (p + ((s : ℤ) + 1), k)) hq
    obtain ⟨A, a, a', x, y, hxEpi, ha, hx, hy⟩ :=
      filteredComplex_differential_representatives_cover U.obj.obj U.obj.filtration
        (s + 1) (p, q) (p + (s + 1), q - (s + 1) + 1) hij
    have hD := (D (s + 1) (by omega)).on_representatives A
      (p, q) (p + (s + 1), q - (s + 1) + 1) hij a a' x y ha hx hy
    have hT := filteredHomology_tower_differential C hBZ eH hH U j t hj ht
      s p q A a a' x y ha hx hy
    apply (cancel_epi (x ≫ Q s p q)).mp
    simp only [Category.assoc]
    rw [reassoc_of% (hQ s p q)]
    calc
      _ = y ≫ cokernel.π (Subobject.ofLE _ _
          (hBZ U (p + (s + 1)) (q - (s + 1) + 1) (s + 1) (by omega))) := by
        simpa only [filteredComplexPageπ, filteredComplexPageObject] using hD
      _ = y ≫ Q s (p + (s + 1)) (q - (s + 1) + 1) ≫
          (eQ s (p + (s + 1)) (q - (s + 1) + 1)).hom := by
        rw [hQ]
      _ = _ := by
        simpa only [Q, Category.assoc] using
          congrArg (fun f ↦ f ≫ (eQ s (p + (s + 1)) (q - (s + 1) + 1)).hom) hT.symm

end CategoryTheory
