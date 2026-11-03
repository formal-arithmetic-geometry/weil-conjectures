/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SequentialDerived.Coinduced.SequentialSemilinearCoinducedComplexes
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-! # Compatible families and the kernel of the coinduced difference

Source: Stacks 0941, the kernel computation in the two-term resolution.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
namespace SheafOfModules.SequentialDerived.Coinduced

attribute [local implicit_reducible] CoinducedSequence.productFunctor
  CoinducedSequence.relationsFunctor

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [EssentiallySmall.{w} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w})

/-- Adjacent compatibility implies compatibility with every transition.
Source: Stacks 0941
(blueprint: lem-sf-sequential-semilinear-coinduced-kernel).
Proof: induct on the length of the interval. Identity transitions act identically;
for a successor use the composition law of each system and adjacent compatibility. -/
theorem compatible_all (M N : StrictRingSystem B)
    (f : ∀ n, M.level n ⟶ N.level n)
    (hf : ∀ n, f (n + 1) ≫ N.transition (Nat.le_succ n) =
      M.transition (Nat.le_succ n) ≫ (systemRestriction B (Nat.le_succ n)).map (f n))
    {m n : ℕ} (h : m ≤ n) :
    f n ≫ N.transition h = M.transition h ≫ (systemRestriction B h).map (f m) := by
  have hh (n : ℕ) (h : m ≤ n) (U : Cᵒᵖ) (x : (M.level n).val.obj U) :
      (N.transition h).val.app U ((f n).val.app U x) =
        (f m).val.app U ((M.transition h).val.app U x) := by
    induction n, h using Nat.le_induction with
    | base =>
        rw [N.identity, M.identity]
    | succ n h ih =>
        rw [N.compose h (Nat.le_succ n), M.compose h (Nat.le_succ n)]
        have he := congrArg (fun z ↦ z.val.app U x) (hf n)
        change (N.transition (Nat.le_succ n)).val.app U ((f (n + 1)).val.app U x) =
          (f n).val.app U ((M.transition (Nat.le_succ n)).val.app U x) at he
        rw [he, ih]
  ext U x
  exact hh n h U x

/-- Compatible maps of evaluated complexes assemble into a strict-system chain map.
Source: Stacks 0941
(blueprint: lem-sf-sequential-semilinear-coinduced-kernel).
Proof: use the prescribed level maps in each degree. The preceding induction proves
all transition squares. The chain-map identity is checked at each level. -/
theorem compatible_assembly
    (M N : CochainComplex (StrictRingSystem B) ℤ)
    (f : ∀ n, (complexEvaluation B n).obj M ⟶ (complexEvaluation B n).obj N)
    (hf : ∀ n, f (n + 1) ≫ (complexTransition B n).app N =
      (complexTransition B n).app M ≫ (complexRestriction B n).map (f n)) :
    ∃ g : M ⟶ N, ∀ n, (complexEvaluation B n).map g = f n := by
  let a (q : ℤ) : M.X q ⟶ N.X q :=
    { app := fun n ↦ (f n).f q
      comm := by
        intro m n h
        apply compatible_all B (M.X q) (N.X q) (fun k ↦ (f k).f q)
        intro k
        exact congrArg (fun z ↦ z.f q) (hf k) }
  let g : M ⟶ N :=
    { f := a
      comm' := by
        intro q r _
        apply strictRingSystem_hom_ext B
        intro n
        exact (f n).comm q r }
  refine ⟨g, ?_⟩
  intro n
  apply HomologicalComplex.Hom.ext
  funext q
  rfl

/-- The augmentation is a monomorphism of complexes.
Source: Stacks 0941
(blueprint: lem-sf-sequential-semilinear-coinduced-kernel).
Proof: transposing each product projection of an equality after augmentation gives
an equality of all level chain maps. These jointly detect chain maps. -/
theorem complexAugmentation_mono (K : CochainComplex (StrictRingSystem B) ℤ) :
    Mono ((complexAugmentationNat B).app K) := by
  constructor
  intro M f g h
  have he := congrArg
    (CoinducedSequence.productHomEquiv (complexEvaluation B) (complexRight B)
      (complexAdjunction B) M K) h
  dsimp only [complexAugmentationNat, CoinducedSequence.augmentationNat] at he
  rw [CoinducedSequence.productHomEquiv_augmentation,
    CoinducedSequence.productHomEquiv_augmentation] at he
  apply HomologicalComplex.Hom.ext
  funext q
  apply strictRingSystem_hom_ext B
  intro n
  exact congrArg (fun z ↦ z.f q) (congrFun he n)

/-- The middle term of the coinduced short complex is exact.
Source: Stacks 0941
(blueprint: lem-sf-sequential-semilinear-coinduced-kernel).
Proof: transpose the components of a map killed by the difference. Its zero defect
is exactly adjacent compatibility. Assemble the resulting family, and transpose back
to see that the map factors through the augmentation. Apply this to the kernel
inclusion; its composite with the cokernel projection of the augmentation vanishes. -/
theorem complexSequence_exact (K : CochainComplex (StrictRingSystem B) ℤ) :
    (complexSequence B K).Exact := by
  apply (ShortComplex.exact_iff_kernel_ι_comp_cokernel_π_zero _).2
  let b := kernel.ι ((complexDifferenceNat B).app K)
  let f := CoinducedSequence.productHomEquiv (complexEvaluation B) (complexRight B)
    (complexAdjunction B) _ K b
  have hf (n : ℕ) : f (n + 1) ≫ (complexTransition B n).app K =
      (complexTransition B n).app _ ≫ (complexRestriction B n).map (f n) := by
    have h := CoinducedSequence.relationsHomEquiv_defect
      (complexEvaluation B) (complexRight B) (complexAdjunction B)
      (complexRestriction B) (complexTransition B) b n
    have hb : b ≫ (complexDifferenceNat B).app K = 0 := kernel.condition _
    change CoinducedSequence.relationsHomEquiv (complexEvaluation B) (complexRight B)
      (complexAdjunction B) (complexRestriction B) _ K
        (b ≫ (complexDifferenceNat B).app K) n = _ at h
    rw [hb, map_zero] at h
    exact (sub_eq_zero.mp h.symm).symm
  obtain ⟨g, hg⟩ := compatible_assembly B _ K f hf
  have he : g ≫ (complexAugmentationNat B).app K = b := by
    apply (CoinducedSequence.productHomEquiv (complexEvaluation B) (complexRight B)
      (complexAdjunction B) _ K).injective
    dsimp only [complexAugmentationNat, CoinducedSequence.augmentationNat]
    rw [CoinducedSequence.productHomEquiv_augmentation]
    exact funext hg
  change b ≫ cokernel.π ((complexAugmentationNat B).app K) = 0
  rw [← he, Category.assoc, cokernel.condition, comp_zero]

end SheafOfModules.SequentialDerived.Coinduced
