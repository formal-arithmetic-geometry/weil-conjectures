/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AbelianLimitStageTriangle

/-! # Shift and coefficient-isomorphism invariance of the continuity comparison

Source: Stacks Tag 0GIU, reduction to sheaves in one degree.
(blueprint: lem-sf-abelian-limit-stage-shift).
-/

@[expose] public section

universe u' u

set_option autoImplicit false

open CategoryTheory Limits

private lemma plus_homology_shift {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] (p : ℤ) :
    (DerivedCategory.Plus.homologyFunctor C 0).shift p =
      DerivedCategory.Plus.homologyFunctor C p := rfl

namespace AlgebraicGeometry.Etale.AbelianLimitStageSystem

variable {B W : Scheme.{u}} {I : Type u} [Category.{u} I]
  (A : Type u') [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
  (S : LimitStageSystem B W I)

/-- Transport continuity through an isomorphism of coefficient complexes.

Proof: the induced map of diagrams and the point-stage map are isomorphisms.
Naturality of the comparison identifies the desired map with their conjugate of
the comparison for the other coefficient complex.
Source: Stacks Tag 0GIU, invariance under choice of representatives.
(blueprint: lem-sf-abelian-limit-stage-shift). -/
theorem isIso_comparison_of_iso
    {K L : DerivedCategory.Plus (Sheaf W.smallEtaleTopology A)} (e : K ≅ L)
    (p : ℤ) [IsIso (comparison A S L p)] : IsIso (comparison A S K p) := by
  have : IsIso (diagramMap A S e.hom p) := by
    have : ∀ i, IsIso ((diagramMap A S e.hom p).app i) := fun i ↦ by
      dsimp only [diagramMap]
      infer_instance
    exact NatIso.isIso_of_isIso_app _
  have h := comparison_naturality A S e.hom p
  have : IsIso (comparison A S K p ≫ (DerivedCategory.Plus.homologyFunctor _ p).map
      ((AbelianLimitStage.functor A S.pt).map e.hom)) := by
    rw [← h]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    ((DerivedCategory.Plus.homologyFunctor _ p).map
      ((AbelianLimitStage.functor A S.pt).map e.hom))

/-- Shift the coefficient and adjust the cohomological degree. -/
noncomputable def stageShiftIso (α : LimitStage B W)
    (K : DerivedCategory.Plus (Sheaf W.smallEtaleTopology A)) (n p : ℤ) :
    (DerivedCategory.Plus.homologyFunctor _ p).obj
        ((AbelianLimitStage.functor A α).obj (K⟦n⟧)) ≅
      (DerivedCategory.Plus.homologyFunctor _ (n + p)).obj
        ((AbelianLimitStage.functor A α).obj K) :=
  (DerivedCategory.Plus.homologyFunctor _ p).mapIso
      (((AbelianLimitStage.functor A α).commShiftIso n).app K) ≪≫
    ((DerivedCategory.Plus.homologyFunctor _ 0).shiftIso n p (n + p) rfl).app _

omit [HasSmallSiteSheafify A] in
/-- Stage shift identifications commute with the stage transitions. -/
lemma stageShiftIso_naturality
    {α β : LimitStage B W} (φ : LimitStage.Hom α β)
    (K : DerivedCategory.Plus (Sheaf W.smallEtaleTopology A)) (n p : ℤ) :
    (DerivedCategory.Plus.homologyFunctor _ p).map
        ((AbelianLimitStage.transition A φ).app (K⟦n⟧)) ≫
        (stageShiftIso A α K n p).hom =
      (stageShiftIso A β K n p).hom ≫
        (DerivedCategory.Plus.homologyFunctor _ (n + p)).map
          ((AbelianLimitStage.transition A φ).app K) := by
  simp only [stageShiftIso, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom]
  rw [← Category.assoc, ← Functor.map_comp,
    ← NatTrans.shift_app_comm, Functor.map_comp, Category.assoc]
  simpa only [Category.assoc, plus_homology_shift, Functor.comp_obj] using
    congrArg (fun f ↦ (DerivedCategory.Plus.homologyFunctor _ p).map
      (((AbelianLimitStage.functor A β).commShiftIso n).hom.app K) ≫ f)
    ((DerivedCategory.Plus.homologyFunctor _ 0).shiftIso_hom_naturality n p (n + p) rfl
      ((AbelianLimitStage.transition A φ).app K))

/-- The shift comparisons assemble to an isomorphism of the homology diagrams. -/
noncomputable def diagramShiftIso
    (K : DerivedCategory.Plus (Sheaf W.smallEtaleTopology A)) (n p : ℤ) :
    diagram A S (K⟦n⟧) p ≅ diagram A S K (n + p) :=
  NatIso.ofComponents (fun i ↦ stageShiftIso A (S.obj i.unop) K n p)
    (fun f ↦ stageShiftIso_naturality A (S.map f.unop) K n p)

@[reassoc]
lemma comparison_shift
    (K : DerivedCategory.Plus (Sheaf W.smallEtaleTopology A)) (n p : ℤ) :
    colim.map (diagramShiftIso A S K n p).hom ≫ comparison A S K (n + p) =
      comparison A S (K⟦n⟧) p ≫ (stageShiftIso A S.pt K n p).hom := by
  apply colimit.hom_ext
  intro i
  simp only [comparison, colimit.ι_map_assoc, colimit.ι_desc, colimit.ι_desc_assoc]
  exact (stageShiftIso_naturality A (S.π i.unop) K n p).symm

/-- Continuity is preserved by shifting coefficients.

Proof: the shift isomorphisms commute with stage transitions and limit legs because
the exchange transformation commutes with shifts. They form an isomorphism of the
diagrams and an isomorphism of their point-stage values. The comparison square
therefore transports invertibility from degree `n+p` to degree `p` after shifting.
Source: Stacks Tag 0GIU, shifted-sheaf base case.
(blueprint: lem-sf-abelian-limit-stage-shift). -/
theorem isIso_comparison_shift
    (K : DerivedCategory.Plus (Sheaf W.smallEtaleTopology A)) (n p : ℤ)
    [IsIso (comparison A S K (n + p))] : IsIso (comparison A S (K⟦n⟧) p) := by
  have h := comparison_shift A S K n p
  have : IsIso (comparison A S (K⟦n⟧) p ≫ (stageShiftIso A S.pt K n p).hom) := by
    rw [← h]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (stageShiftIso A S.pt K n p).hom

end AlgebraicGeometry.Etale.AbelianLimitStageSystem
