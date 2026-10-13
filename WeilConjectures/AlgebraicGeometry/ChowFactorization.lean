/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.ChowLemma
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Blueprint statements

lemma-weil-pbc-chow-factorization.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Blueprint: lemma-weil-pbc-chow-factorization. -/
theorem exists_chow_factorization_of_isAffine {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsProper f] [IsAffine Y] :
    (∃ (T : Scheme.{u}) (n : ℕ) (π : T ⟶ X)
      (i : T ⟶ ProjectiveSpace (ULift.{u} (Fin (n + 1))) Y),
      IsProper π ∧ Surjective π ∧ IsClosedImmersion i ∧
        π ≫ f = i ≫ ProjectiveSpace (ULift.{u} (Fin (n + 1))) Y ↘ Y) ∧
    (∀ (T : Scheme.{u}) (n : ℕ) (π : T ⟶ X)
      (i : T ⟶ ProjectiveSpace (ULift.{u} (Fin (n + 1))) Y),
      IsProper π → Surjective π → IsClosedImmersion i →
      ∀ (h : π ≫ f = i ≫ ProjectiveSpace (ULift.{u} (Fin (n + 1))) Y ↘ Y)
        (Y' X' T' : Scheme.{u}) (g : Y' ⟶ Y) (x : X' ⟶ X) (f' : X' ⟶ Y')
        (t : T' ⟶ T) (b : T' ⟶ Y') (hx : IsPullback x f' f g)
        (ht : IsPullback t b (π ≫ f) g),
      IsProper (hx.lift (t ≫ π) b ((Category.assoc t π f).trans ht.w)) ∧
      Surjective (hx.lift (t ≫ π) b ((Category.assoc t π f).trans ht.w)) ∧
      IsClosedImmersion
        (ProjectiveSpace.liftBaseChange b (t ≫ i)
          (ht.w.symm.trans ((congrArg (fun k => t ≫ k) h).trans
            (Category.assoc t i _).symm))) ∧
      hx.lift (t ≫ π) b ((Category.assoc t π f).trans ht.w) ≫ f' =
        ProjectiveSpace.liftBaseChange b (t ≫ i)
          (ht.w.symm.trans ((congrArg (fun k => t ≫ k) h).trans
            (Category.assoc t i _).symm)) ≫
          ProjectiveSpace (ULift.{u} (Fin (n + 1))) Y' ↘ Y') := by
  sorry

end AlgebraicGeometry
