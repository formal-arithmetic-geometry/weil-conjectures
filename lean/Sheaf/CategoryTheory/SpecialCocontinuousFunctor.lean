/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.CoverLifting

/-!
# Special cocontinuous functors between sites

Source: Stacks Project, Definitions 00XJ and 03CG, Lemma 03A0, conditions (1)-(5)
(blueprint: def-weil-pbc-special-cocontinuous-functor).

Cocontinuity itself is `Functor.IsCocontinuous` for the generated topologies.
The remaining conditions use the actual covering presieves, not their saturation.
-/

@[expose] public section

universe u₁ v₁ u₂ v₂

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

/-- Source: Stacks Project, Lemma 03A0, conditions (1)-(5), and Definition 03CG
(blueprint: def-weil-pbc-special-cocontinuous-functor).

The sites use the precoverage encoding of `def-weil-pbc-sites-and-cohomology`.
The first conjunct is cocontinuity (00XJ) for the generated topologies: a covering
sieve contains a covering family, and membership in its functor pullback means
that the image arrows factor through members of that family (refinement, 00VT).
The next two conjuncts express Stacks continuity (00WV): coverings map to
coverings and pullbacks of covering arrows along arbitrary arrows are preserved.
The next two conjuncts give local equality and local lifting on a source covering.
Finally each target object has an actual covering by image objects; its index type
`Type (max u₁ v₂)` holds every family of pairs `(U, F.obj U ⟶ V)`. Empty coverings
are allowed throughout. The categories are not required to be small, so that large
sites such as the small etale site `X.Etale` are covered (as in
`siteContinuous_pushforward_isSheaf`). As in the node, the equivalence-of-topoi
conclusion of 03A0 is not included as an additional condition. -/
def IsSpecialCocontinuous
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (J : Precoverage C) (K : Precoverage D)
    [J.HasIsos] [J.IsStableUnderComposition] [J.IsStableUnderBaseChange] [J.HasPullbacks]
    [K.HasIsos] [K.IsStableUnderComposition] [K.IsStableUnderBaseChange] [K.HasPullbacks]
    (F : C ⥤ D) : Prop :=
  F.IsCocontinuous J.toGrothendieck K.toGrothendieck ∧
  (∀ (X : C) (R : Presieve X), R ∈ J X → R.map F ∈ K (F.obj X)) ∧
  (∀ (X Y Z : C) (R : Presieve X), R ∈ J X →
    ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f → PreservesLimit (cospan f g) F) ∧
  (∀ (X Y : C) (a b : X ⟶ Y), F.map a = F.map b →
    ∃ R : Presieve X, R ∈ J X ∧
      ∀ (Z : C) (f : Z ⟶ X), R f → f ≫ a = f ≫ b) ∧
  (∀ (X Y : C) (c : F.obj X ⟶ F.obj Y),
    ∃ R : Presieve X, R ∈ J X ∧
      ∀ (Z : C) (f : Z ⟶ X), R f →
        ∃ d : Z ⟶ Y, F.map d = F.map f ≫ c) ∧
  (∀ V : D, ∃ (I : Type (max u₁ v₂)) (U : I → C) (f : ∀ i : I, F.obj (U i) ⟶ V),
    Presieve.ofArrows (fun i : I => F.obj (U i)) f ∈ K V)

end CategoryTheory.Functor
