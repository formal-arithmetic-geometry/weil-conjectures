/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.SingleFunctorLaxMonoidal
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Dualizable

/-! # Exact dual pairings placed in degree zero -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed

namespace DerivedCategory.SingleDualPairing

variable {A : Type v} [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
  [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]

private theorem iso_tensor_Q (K L : CochainComplex A ℤ)
    (hK : (HomologicalComplex.quasiIso A (.up ℤ)).kFlat K) :
    IsIso (Functor.LaxMonoidal.μ Q K L) := by
  have : IsIso (Functor.LaxMonoidal.μ Qh
      ((HomotopyCategory.quotient A (.up ℤ)).obj K)
      ((HomotopyCategory.quotient A (.up ℤ)).obj L)) :=
    isIso_μ_Qh_of_kFlat _ _ ((HomotopyCategory.kFlat_quotient_obj_iff _).2 hK)
  change IsIso ((_ ⊗ₘ _) ≫ (Functor.LaxMonoidal.μ Qh _ _ ≫ Qh.map _) ≫ _)
  infer_instance

private theorem tensorComparison_isIso (P Q : A) (hP : ObjectProperty.flat P) :
    IsIso (singleFunctorTensorComparison P Q) := by
  have := iso_tensor_Q ((CochainComplex.singleFunctor A 0).obj P)
    ((CochainComplex.singleFunctor A 0).obj Q)
    ((CochainComplex.kFlat_single_obj_iff_flat _ 0).2 hP)
  unfold singleFunctorTensorComparison
  infer_instance

/-- Placing an exact ordinary dual pairing in degree zero preserves its evaluation.
Source: Stacks Project, Tag 08JJ
(blueprint: lem-pod-single-dual-pairing).
Proof: both members of a dual pair are flat. The degree-zero functor restricted to
flat objects is strong monoidal: its tensor comparison is invertible because a flat
single complex is K-flat. Lift the ordinary dual pair through the fully faithful
flat-subcategory inclusion, and apply that strong monoidal functor. Its evaluation
is exactly the canonical tensor comparison, the original evaluation in degree zero,
and the unit comparison. -/
theorem singleFunctor_exactPairing (P D : A) [ExactPairing D P] :
    ∃ e : ExactPairing ((singleFunctor A 0).obj D) ((singleFunctor A 0).obj P),
      e.evaluation' = singleFunctorTensorComparison P D ≫
        (singleFunctor A 0).map (ε_ D P) ≫ (singleFunctorObjUnitIso A).hom := by
  obtain ⟨ms, hms, hus⟩ := exists_singleFunctorLaxMonoidal (A := A)
  let := ms
  let s := singleFunctor A 0
  let F := ObjectProperty.flat.ι ⋙ s
  have hμ (X Y : (ObjectProperty.flat (A := A)).FullSubcategory) :
      IsIso (Functor.LaxMonoidal.μ F X Y) := by
    change IsIso (Functor.LaxMonoidal.μ s X.obj Y.obj ≫ s.map (𝟙 _))
    rw [s.map_id, Category.comp_id]
    change IsIso (Functor.LaxMonoidal.μ (singleFunctor A 0) X.obj Y.obj)
    rw [hms]
    exact tensorComparison_isIso X.obj Y.obj X.property
  have hε : IsIso (Functor.LaxMonoidal.ε F) := by
    change IsIso (Functor.LaxMonoidal.ε s ≫ s.map (𝟙 _))
    rw [s.map_id, Category.comp_id]
    change IsIso (Functor.LaxMonoidal.ε (singleFunctor A 0))
    rw [hus]
    infer_instance
  let := hμ
  let := hε
  let := Functor.Monoidal.ofLaxMonoidal F
  have hP : IsDualizable P :=
    ⟨{ rightDual := D, exact := BraidedCategory.exactPairing_swap D P }⟩
  have hD : IsDualizable D := ⟨{ rightDual := P }⟩
  let Pf : (ObjectProperty.flat (A := A)).FullSubcategory := ⟨P, hP.flat⟩
  let Df : (ObjectProperty.flat (A := A)).FullSubcategory := ⟨D, hD.flat⟩
  let : ExactPairing (ObjectProperty.flat.ι.obj Df) (ObjectProperty.flat.ι.obj Pf) := by
    change ExactPairing D P
    infer_instance
  let : ExactPairing Df Pf := ExactPairing.ofFaithful ObjectProperty.flat.ι
    (X := Df) (Y := Pf)
    (ObjectProperty.homMk (ε_ D P)) (ObjectProperty.homMk (η_ D P))
    (by
      change ε_ D P = 𝟙 _ ≫ ε_ D P ≫ 𝟙 _
      simp)
    (by
      change η_ D P = 𝟙 _ ≫ η_ D P ≫ 𝟙 _
      simp)
  let ep := ExactPairing.map F Df Pf
  have hη : Functor.OplaxMonoidal.η F = (singleFunctorObjUnitIso A).hom := by
    rw [← cancel_epi (Functor.LaxMonoidal.ε F), Functor.Monoidal.ε_η]
    change 𝟙 _ = (Functor.LaxMonoidal.ε s ≫ s.map (𝟙 _)) ≫
      (singleFunctorObjUnitIso A).hom
    rw [s.map_id, Category.comp_id]
    change 𝟙 _ = Functor.LaxMonoidal.ε (singleFunctor A 0) ≫
      (singleFunctorObjUnitIso A).hom
    rw [hus, Iso.inv_hom_id]
  refine ⟨ep, ?_⟩
  change (Functor.LaxMonoidal.μ s P D ≫ s.map (𝟙 _)) ≫ s.map (ε_ D P) ≫
    Functor.OplaxMonoidal.η F = _
  rw [s.map_id, Category.comp_id, hη]
  change Functor.LaxMonoidal.μ (singleFunctor A 0) P D ≫
    (singleFunctor A 0).map (ε_ D P) ≫ (singleFunctorObjUnitIso A).hom = _
  rw [hms]

end DerivedCategory.SingleDualPairing
