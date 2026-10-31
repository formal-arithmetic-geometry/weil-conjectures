/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SystemLevelLeftExtensionBasic
import WeilConjectures.CategoryTheory.SystemDerivedSubsequenceTransition
import WeilConjectures.CategoryTheory.SystemDerivedTransitionCoherence
import WeilConjectures.CategoryTheory.DerivedCategory.AdjunctionTransitionCoherence

/-! # Normalization under selected left extension

Source: Zheng, Construction 4.1; integral scalar mates, proof step 2
(blueprint: lem-pur-system-selected-normalization).
-/

@[expose] public section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
namespace SheafOfModules
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  [EssentiallySmall.{w} C]

private theorem transition_eq (S : SystemLevelLeftExtensionTheory (J := J))
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) {m n : ℕ} (h : m ≤ n) :
    S.transition B h = systemDerivedTransition B h := by
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso (StrictRingSystem B) (.up ℤ))
  intro K
  apply (cancel_mono ((systemRestriction B h).mapDerivedCategory.map
      ((systemEvaluation B m).mapDerivedCategoryFactors.hom.app K) ≫
    (systemRestriction B h).mapDerivedCategoryFactors.hom.app
      (((systemEvaluation B m).mapHomologicalComplex (.up ℤ)).obj K))).1
  exact (S.transition_rep B h K).trans (systemDerivedTransition_rep B h K).symm

private theorem selectedEvaluation_eq (S : SystemLevelLeftExtensionTheory (J := J))
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (r : ℕ ↪o ℕ) (n : ℕ) :
    (S.selectedEvaluation B r n).hom = (systemDerivedSubsequenceEvaluation B r n).hom := by
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso (StrictRingSystem B) (.up ℤ))
  intro K
  apply (cancel_mono ((systemEvaluation B (r n)).mapDerivedCategoryFactors.hom.app K)).1
  exact (S.selectedEvaluation_rep B r n K).trans
    (systemDerivedSubsequenceEvaluation_rep B r n K).symm

/-- Restriction and selected left extension preserve invertibility of all
transition-adjoints, independently of constructibility or bounds.

Source: Zheng, Construction 4.1; integral scalar mates, proof step 2
(blueprint: lem-pur-system-selected-normalization).

Proof: exact restriction evaluates at r(n), and its transition is the original
transition from r(n) to r(m), conjugated by the selected evaluation isomorphisms.
Taking its scalar adjunct therefore preserves normalization. For left extension,
use selectedDerivedBelow and selectedTransition: its successive transition-adjoint
is the scalar extension of the original normalized transition-adjoint, conjugated
by the two derived tensor associators and the evaluation comparisons. All these
maps are invertible, including when the two next selected indices coincide.
For arbitrary m ≤ n, minimality gives t(m) ≤ t(n). Canonical transition
composition and subsequence coherence give the right-adjoint cocone square.
Apply adjunctionTransition_coherence to that square and the two selected transpose
identities. Its formula uses canonical left-adjoint-uniqueness associators and
remains valid when the two next indices coincide, including m=n. -/
theorem systemSelectedNormalization
    (S : SystemLevelLeftExtensionTheory (J := J))
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (r : ℕ ↪o ℕ) :
    let normalized := fun (A : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w})
        (M : DerivedCategory (StrictRingSystem A)) ↦
      ∀ {m n : ℕ} (h : m ≤ n),
        IsIso (((systemDerivedTensorAdj S.scalar A h).homEquiv _ _).symm
          ((S.transition A h).app M))
    (∀ M, normalized B M →
      normalized (selectedSystemRings B r) ((derivedSystemSubsequence B r).obj M)) ∧
    (∀ N, normalized (selectedSystemRings B r) N →
      normalized B ((S.selected B r).derived.obj N)) := by
  constructor
  · intro M hM m n h
    have hr := systemDerivedSubsequenceTransition B r h M
    rw [← selectedEvaluation_eq S B r n, ← selectedEvaluation_eq S B r m,
      ← transition_eq S B (r.monotone h),
      ← transition_eq S (selectedSystemRings B r) h] at hr
    have he := congrArg
      ((systemDerivedTensorAdj S.scalar B (r.monotone h)).homEquiv _ _).symm hr
    erw [Adjunction.homEquiv_naturality_left_symm,
      Adjunction.homEquiv_naturality_right_symm] at he
    have := hM (r.monotone h)
    have hc : IsIso ((((systemDerivedTensorAdj S.scalar
        (selectedSystemRings B r) h).homEquiv _ _).symm
          ((S.transition (selectedSystemRings B r) h).app
            ((derivedSystemSubsequence B r).obj M))) ≫
        (S.selectedEvaluation B r m).hom.app M) := by
      erw [← he]
      infer_instance
    exact IsIso.of_isIso_comp_right _ ((S.selectedEvaluation B r m).hom.app M)
  · intro N hN m n h
    let a := systemNextSelected r m
    let b := systemNextSelected r n
    let p := (systemNextSelected_spec r m).1
    let q := (systemNextSelected_spec r n).1
    have k : a ≤ b := (systemNextSelected_spec r m).2 b
      (h.trans (systemNextSelected_spec r n).1)
    have hν (j : ℕ) (P : DerivedCategory (StrictRingSystem (selectedSystemRings B r))) :
        (systemDerivedTensorAdj S.scalar B (systemNextSelected_spec r j).1).homEquiv _ _
          ((S.selectedDerivedBelow B r j).inv.app P) =
        (derivedSystemEvaluation (selectedSystemRings B r) (systemNextSelected r j)).map
          ((S.selected B r).adjunction.unit.app P) ≫
        (systemDerivedSubsequenceEvaluation B r (systemNextSelected r j)).hom.app
          ((S.selected B r).derived.obj P) ≫
        (systemDerivedTransition B (systemNextSelected_spec r j).1).app
          ((S.selected B r).derived.obj P) := by
      rw [← selectedEvaluation_eq S B r (systemNextSelected r j), ← transition_eq S B]
      have hh := S.selectedDerivedTranspose B r j P ((S.selected B r).derived.obj P) (𝟙 _)
      erw [(derivedSystemEvaluation B j).map_id, Category.comp_id,
        (S.selected B r).adjunction.homEquiv_id] at hh
      exact hh
    have hr (M : DerivedCategory (StrictRingSystem B)) :
        (systemDerivedSubsequenceEvaluation B r b).hom.app M ≫
          (systemDerivedTransition B q).app M ≫
          (systemRestriction B q).mapDerivedCategory.map
            ((systemDerivedTransition B h).app M) ≫
          (systemDerivedRestrictionComposition B h q).hom.app
            ((derivedSystemEvaluation B m).obj M) =
        (systemDerivedTransition (selectedSystemRings B r) k).app
            ((derivedSystemSubsequence B r).obj M) ≫
          (systemRestriction B (r.monotone k)).mapDerivedCategory.map
            ((systemDerivedSubsequenceEvaluation B r a).hom.app M) ≫
          (systemRestriction B (r.monotone k)).mapDerivedCategory.map
            ((systemDerivedTransition B p).app M) ≫
          (systemDerivedRestrictionComposition B p (r.monotone k)).hom.app
            ((derivedSystemEvaluation B m).obj M) := by
      erw [systemDerivedTransition_comp B h q M]
      erw [← systemDerivedTransition_comp B p (r.monotone k) M]
      erw [reassoc_of% (systemDerivedSubsequenceTransition B r k M)]
    have hh := adjunctionTransition_coherence (S.selected B r).adjunction
      (systemDerivedTensorAdj S.scalar B p) (systemDerivedTensorAdj S.scalar B q)
      (systemDerivedTensorAdj S.scalar B h)
      (systemDerivedTensorAdj S.scalar (selectedSystemRings B r) k)
      (systemDerivedTensorAdj S.scalar B (p.trans (r.monotone k)))
      (systemDerivedRestrictionComposition B h q)
      (systemDerivedRestrictionComposition B p (r.monotone k))
      (systemDerivedSubsequenceEvaluation B r a).hom
      (systemDerivedSubsequenceEvaluation B r b).hom
      (systemDerivedTransition (selectedSystemRings B r) k)
      (systemDerivedTransition B h) (systemDerivedTransition B p) (systemDerivedTransition B q)
      (S.selectedDerivedBelow B r m) (S.selectedDerivedBelow B r n)
      (hν m) (hν n) hr N
    have hi := hN k
    rw [transition_eq S (selectedSystemRings B r) k] at hi
    rw [transition_eq S B h, hh]
    infer_instance

end SheafOfModules
