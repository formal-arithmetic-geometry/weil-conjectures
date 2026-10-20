/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D8
-/
module

public import Sheaf.Paper.WeilCompletedKoszulLimitComparison
import Sheaf.CategoryTheory.RingedCechKoszulComparisonOnSite

/-!
# Comparing the published Koszul fiber with Cech internal Hom

Source: Stacks Project, algebraization.tex, Tag 0A0E,
lemma-derived-completion-koszul, and sites-cohomology.tex, Tags 0941 and 0A0A.
(blueprint: lem-weil-pbc-completed-fiber-cech-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- The published Koszul fiber is Cech internal Hom, with its specified unit.
Source: Stacks Project, Tag 0A0E
(blueprint: lem-weil-pbc-completed-fiber-cech-comparison).
Proof: compare the explicit fiber with the prescribed strict derived inverse limit.
The existing single-site Cech--Koszul theorem identifies that strict limit with
Cech internal Hom and carries the Cech unit to the strict unit. Compose the two
isomorphisms and cancel the second unit equation. -/
theorem completed_fiber_cech_comparison
    (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A)
    (C : CochainComplex (pbcModules X (pbcAdicCompletion X d)) ℤ) :
    let O := completedCechRing X d
    let F := completedCechDerivedEquiv X d
    let b := fun i ↦ completedCechScalar X d (a i)
    ∃ e : F.functor.obj (DerivedCategory.Q.obj (intrinsicCompletionComplex X d r a C)) ≅
        (ringedCechCompletionFunctor O (ringedExtendedCech O r b).1).obj
          (F.functor.obj (DerivedCategory.Q.obj C)),
      F.functor.map (DerivedCategory.Q.map (intrinsicCompletionComplexUnit X d r a C)) ≫
          e.hom =
        ringedCechCompletionUnit O (ringedExtendedCech O r b).1
          (ringedExtendedCech O r b).2 (F.functor.obj (DerivedCategory.Q.obj C)) := by
  let O := completedCechRing X d
  let F := completedCechDerivedEquiv X d
  let b := fun i ↦ completedCechScalar X d (a i)
  obtain ⟨D, theta, htheta⟩ := exists_ringed_cech_koszul_comparison_on_site O r b
  obtain ⟨e, he⟩ := completed_fiber_strict_limit_comparison X d r a C D
  refine ⟨e ≪≫ (theta.app (F.functor.obj (DerivedCategory.Q.obj C))).symm, ?_⟩
  dsimp only [Iso.trans_hom, Iso.symm_hom]
  rw [← Category.assoc, he, ← htheta]
  change (_ ≫ theta.hom.app _) ≫ theta.inv.app _ = _
  rw [Category.assoc, Iso.hom_inv_id_app, Category.comp_id]

end AlgebraicGeometry.Scheme
