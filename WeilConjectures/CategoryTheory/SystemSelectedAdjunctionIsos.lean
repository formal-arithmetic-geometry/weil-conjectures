/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SystemLevelLeftExtensionBasic
import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-! # Isomorphisms in the selected-system adjunction

Source: Zheng, Construction 4.1, and the selected-level calculation in the proof of
exceptional integral scalar mates (blueprint: lem-pur-system-selected-adjunction-isos).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
namespace SheafOfModules
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  [EssentiallySmall.{w} C]

private theorem identity_transpose_isIso
    (S : SystemLevelLeftExtensionTheory (J := J))
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) {m n : ℕ} (h : m ≤ n) (hn : n = m)
    {P : DerivedCategory (systemLevel B n)} {Q : DerivedCategory (systemLevel B m)}
    (f : (systemDerivedTensor S.scalar B h).obj P ⟶ Q) [IsIso f] :
    IsIso ((systemDerivedTensorAdj S.scalar B h).homEquiv P Q f) := by
  subst n
  have := Functor.Full.of_iso (S.tensor.derivedUnit B m).symm
  have := Functor.Faithful.of_iso (S.tensor.derivedUnit B m).symm
  rw [Adjunction.homEquiv_unit]
  infer_instance

/-- The unit of selected left extension is always invertible, and its counit is
invertible on systems whose transition-adjoints are invertible.

Source: Zheng, Construction 4.1; integral scalar mates, proof step 2
(blueprint: lem-pur-system-selected-adjunction-isos).

Proof: the next selected index at r(n) is n, by strict monotonicity and minimality.
At that index the selected transpose formula identifies the evaluated unit with
the tensor unitor, conjugated by the evaluation comparison. For the counit, the
same formula at an arbitrary m identifies its evaluated map with the normalization
map from r(t(m)) to m, conjugated by invertible evaluation comparisons. Joint
detection of isomorphisms by evaluations gives both assertions. -/
theorem systemSelectedAdjunctionIsos
    (S : SystemLevelLeftExtensionTheory (J := J))
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (r : ℕ ↪o ℕ) :
    (∀ N, IsIso ((S.selected B r).adjunction.unit.app N)) ∧
      ∀ M, (∀ {m n : ℕ} (h : m ≤ n),
        IsIso (((systemDerivedTensorAdj S.scalar B h).homEquiv _ _).symm
          ((S.transition B h).app M))) →
        IsIso ((S.selected B r).adjunction.counit.app M) := by
  constructor
  · intro N
    apply (S.detectsIso (selectedSystemRings B r) _).2
    intro n
    have hn : systemNextSelected r (r n) = n := by
      apply Nat.le_antisymm
      · exact (systemNextSelected_spec r (r n)).2 n le_rfl
      · exact r.le_iff_le.mp (systemNextSelected_spec r (r n)).1
    rw [← hn]
    have hr : r (systemNextSelected r (r n)) = r n := congrArg r hn
    have ht := S.selectedDerivedTranspose B r (r n) N
      ((S.selected B r).derived.obj N) (𝟙 _)
    erw [(derivedSystemEvaluation B (r n)).map_id, Category.comp_id,
      (S.selected B r).adjunction.homEquiv_id] at ht
    have htrans (m k : ℕ) (h : m ≤ k) (hk : k = m)
        (M : DerivedCategory (StrictRingSystem B)) : IsIso ((S.transition B h).app M) := by
      subst k
      have hi := identity_transpose_isIso S B h rfl
        ((S.tensor.derivedUnit B m).hom.app ((derivedSystemEvaluation B m).obj M))
      erw [← S.transition_identity B m M, Equiv.apply_symm_apply] at hi
      exact hi
    have := htrans _ _ (systemNextSelected_spec r (r n)).1 hr
      ((S.selected B r).derived.obj N)
    have hleft := identity_transpose_isIso S B
      (systemNextSelected_spec r (r n)).1 hr ((S.selectedDerivedBelow B r (r n)).inv.app N)
    erw [ht] at hleft
    exact IsIso.of_isIso_comp_right
      ((derivedSystemEvaluation (selectedSystemRings B r) (systemNextSelected r (r n))).map
        ((S.selected B r).adjunction.unit.app N))
      ((S.selectedEvaluation B r (systemNextSelected r (r n))).hom.app
          ((S.selected B r).derived.obj N) ≫
        (S.transition B (systemNextSelected_spec r (r n)).1).app
          ((S.selected B r).derived.obj N))
  · intro M hM
    apply (S.detectsIso B _).2
    intro m
    have ht := S.selectedDerivedTranspose B r m
      ((derivedSystemSubsequence B r).obj M) M ((S.selected B r).adjunction.counit.app M)
    have hc : (S.selected B r).adjunction.homEquiv _ M
        ((S.selected B r).adjunction.counit.app M) = 𝟙 _ := by
      rw [← (S.selected B r).adjunction.homEquiv_symm_id M]
      exact ((S.selected B r).adjunction.homEquiv _ M).apply_symm_apply (𝟙 _)
    erw [hc, (derivedSystemEvaluation (selectedSystemRings B r)
      (systemNextSelected r m)).map_id, Category.id_comp] at ht
    have he := congrArg
      ((systemDerivedTensorAdj S.scalar B (systemNextSelected_spec r m).1).homEquiv _ _).symm ht
    erw [Equiv.symm_apply_apply, Adjunction.homEquiv_naturality_left_symm] at he
    have hi := hM (systemNextSelected_spec r m).1
    have hcomp : IsIso ((S.selectedDerivedBelow B r m).inv.app
        ((derivedSystemSubsequence B r).obj M) ≫
        (derivedSystemEvaluation B m).map ((S.selected B r).adjunction.counit.app M)) := by
      rw [he]
      infer_instance
    exact IsIso.of_isIso_comp_left
      ((S.selectedDerivedBelow B r m).inv.app ((derivedSystemSubsequence B r).obj M))
      ((derivedSystemEvaluation B m).map ((S.selected B r).adjunction.counit.app M))

end SheafOfModules
