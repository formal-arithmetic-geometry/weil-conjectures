/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SequentialDerived.SequentialSemilinearDerivedDiagrams

/-! # Unshifted compatible maps of derived semilinear towers

Source: the coherent-tower paragraph of `lem-coef-integral-finite-extension.proof.md`.
This removes the zero-shift transport in the sequential mapping theorem and exposes
its unique-lifting, extensionality, and isomorphism consequences.
(blueprint: lem-sf-sequential-derived-tower-lifting)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
namespace SheafOfModules.SequentialDerived

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [EssentiallySmall.{w} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w})

/-- A compatible family of unshifted vertex maps has a unique lift when the adjacent
negative Hom groups vanish and both towers have common lower bounds.
Source: blueprint `lem-coef-integral-finite-extension.proof.md`, coherent-tower paragraph
(blueprint: lem-sf-sequential-derived-tower-lifting).
Proof: insert the canonical inverse zero-shift comparison at every vertex, apply the
sequential unique-lift assertion, and cancel those invertible comparisons. Naturality
of the zero-shift comparison identifies the two compatibility equations. -/
theorem existsUnique_compatible_lift
    (M N : DerivedCategory (StrictRingSystem B))
    (hM : HasCommonLowerBound B M) (hN : HasCommonLowerBound B N)
    (hs : ∀ n : ℕ, Subsingleton ((derivedSystemEvaluation B (n + 1)).obj M ⟶
      (adjacentRestriction B n).obj (((derivedSystemEvaluation B n).obj N)⟦(-1 : ℤ)⟧)))
    (f : ∀ n : ℕ, (derivedSystemEvaluation B n).obj M ⟶
      (derivedSystemEvaluation B n).obj N)
    (hf : ∀ n : ℕ,
      (systemDerivedTransition B (Nat.le_succ n)).app M ≫
          (adjacentRestriction B n).map (f n) =
        f (n + 1) ≫ (systemDerivedTransition B (Nat.le_succ n)).app N) :
    ∃! g : M ⟶ N, ∀ n : ℕ, (derivedSystemEvaluation B n).map g = f n := by
  let f0 : vertexHom B M N 0 := fun n ↦ f n ≫
    (shiftFunctorZero _ ℤ).inv.app ((derivedSystemEvaluation B n).obj N)
  have hf0 : difference B M N 0 f0 = 0 := by
    funext n
    dsimp only [difference, f0]
    apply sub_eq_zero.mpr
    simp only [shiftedTransition, Functor.commShiftIso_zero,
      Functor.CommShift.isoZero_inv_app, Category.assoc]
    rw [← (shiftFunctorZero _ ℤ).inv.naturality_assoc]
    dsimp only [Functor.id_map, Functor.comp_obj]
    erw [Iso.inv_hom_id_app_assoc]
    rw [Functor.map_comp, ← Category.assoc, hf]
    exact Category.assoc _ _ _
  obtain ⟨g, hg, hu⟩ :=
    (sequentialSemilinearDerivedDiagrams B).2.2.2.2.1 M N hM hN hs f0 hf0
  have he (g : M ⟶ N) : evaluateHom B M N g = f0 ↔
      ∀ n : ℕ, (derivedSystemEvaluation B n).map g = f n := by
    constructor
    · intro h n
      exact (cancel_mono ((shiftFunctorZero _ ℤ).inv.app _)).1 (congrFun h n)
    · intro h
      funext n
      dsimp only [evaluateHom, f0]
      rw [h]
  exact ⟨g, (he g).1 hg, fun g' hg' ↦ hu g' ((he g').2 hg')⟩

/-- Evaluation detects equality of maps under the boundedness and rigidity hypotheses.
Source: blueprint `lem-coef-integral-finite-extension.proof.md`, coherence paragraph
(blueprint: lem-sf-sequential-derived-tower-lifting).
Proof: the evaluations of the first map satisfy the transition equation by naturality.
Both given maps are lifts of that same family, so unique lifting identifies them. -/
theorem hom_ext_of_negative_hom
    (M N : DerivedCategory (StrictRingSystem B))
    (hM : HasCommonLowerBound B M) (hN : HasCommonLowerBound B N)
    (hs : ∀ n : ℕ, Subsingleton ((derivedSystemEvaluation B (n + 1)).obj M ⟶
      (adjacentRestriction B n).obj (((derivedSystemEvaluation B n).obj N)⟦(-1 : ℤ)⟧)))
    (f g : M ⟶ N) (h : ∀ n : ℕ,
      (derivedSystemEvaluation B n).map f = (derivedSystemEvaluation B n).map g) :
    f = g := by
  obtain ⟨z, _hz, hu⟩ := existsUnique_compatible_lift B M N hM hN hs
    (fun n ↦ (derivedSystemEvaluation B n).map f)
    (fun n ↦ ((systemDerivedTransition B (Nat.le_succ n)).naturality f).symm)
  exact (hu f (fun _ ↦ rfl)).trans (hu g (fun n ↦ (h n).symm)).symm

/-- A compatible family of vertex isomorphisms has a unique isomorphism lifting it.
Source: blueprint `lem-coef-integral-finite-extension.proof.md`, coherence paragraph
(blueprint: lem-sf-sequential-derived-tower-lifting).
Proof: lift the family of homs. Joint conservativity of evaluations makes the lift
invertible. Any competing isomorphism has the same hom by uniqueness of the lift. -/
theorem existsUnique_compatible_iso
    (M N : DerivedCategory (StrictRingSystem B))
    (hM : HasCommonLowerBound B M) (hN : HasCommonLowerBound B N)
    (hs : ∀ n : ℕ, Subsingleton ((derivedSystemEvaluation B (n + 1)).obj M ⟶
      (adjacentRestriction B n).obj (((derivedSystemEvaluation B n).obj N)⟦(-1 : ℤ)⟧)))
    (f : ∀ n : ℕ, (derivedSystemEvaluation B n).obj M ≅
      (derivedSystemEvaluation B n).obj N)
    (hf : ∀ n : ℕ,
      (systemDerivedTransition B (Nat.le_succ n)).app M ≫
          (adjacentRestriction B n).map (f n).hom =
        (f (n + 1)).hom ≫ (systemDerivedTransition B (Nat.le_succ n)).app N) :
    ∃! g : M ≅ N, ∀ n : ℕ, (derivedSystemEvaluation B n).map g.hom = (f n).hom := by
  obtain ⟨g, hg, hu⟩ := existsUnique_compatible_lift B M N hM hN hs
    (fun n ↦ (f n).hom) hf
  have : IsIso g := by
    apply ((sequentialSemilinearDerivedDiagrams B).2.2.2.2.2 M N g).2
    intro n
    rw [hg n]
    infer_instance
  refine ⟨asIso g, hg, ?_⟩
  intro g' hg'
  apply Iso.ext
  exact hu g'.hom hg'

end SheafOfModules.SequentialDerived
