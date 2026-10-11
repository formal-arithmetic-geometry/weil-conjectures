/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T1
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Chow factorization over an affine base

Source: Weil conjectures blueprint, `sec-proper-base-change`, `sk-thm-chow`,
`lemma-weil-pbc-chow-factorization` (blueprint: lemma-weil-pbc-chow-factorization).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A proper morphism over an affine base is dominated by a projective scheme, without
Noetherian or finite-presentation assumptions. Every such factorization survives base change.
Source: Weil conjectures blueprint, `sk-thm-chow`,
(blueprint: lemma-weil-pbc-chow-factorization).

Proof: (1) Use `prop-nagata-finite-type-closed-in-fp` to embed `X` as a closed subscheme
of a separated finitely presented envelope over `Y`.
(2) Descend the envelope to a Noetherian model by `lemma-nagata-final-descended-model`.
(3) Apply `thm-chow-lemma` to obtain a proper surjection and an immersion into projective
space over the model. (4) Pull these back to `Y`, using
`lemma-nagata-projective-space-base-change-pullback` and stability of properness and
surjectivity. (5) Pull back the closed subscheme `X` to obtain the modification; composing
its closed immersion into the modified envelope with the projective immersion gives an
immersion over `Y`. (6) Its source is proper over `Y` and its target is separated, so
`lem-weil-pbc-proper-to-separated` makes the immersion proper and
`lem-weil-pbc-proper-immersion-closed` makes it closed.
(7) Properness, surjectivity and closed immersions are stable under base change; the
factorization identity follows from the universal properties of the two pullbacks.

In the second conjunct, `hx` and `ht` specify arbitrary models of the base changes of
`X` and the modification. Their universal properties define the base-changed modification
map and projective embedding using `hx.lift` and `ProjectiveSpace.liftBaseChange`.
-/
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
