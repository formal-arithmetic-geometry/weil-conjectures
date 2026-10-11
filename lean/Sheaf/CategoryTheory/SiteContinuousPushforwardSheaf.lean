/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Sheaf.CategoryTheory.SheavesAlgebraicStructuresObjects

/-!
# Precomposition with a continuous functor of sites

Source: Stacks Project, Definition 00WV and Lemma 00WW
(blueprint: lem-weil-pbc-site-continuous-pushforward-sheaf).
-/

@[expose] public section

universe u₁ v₁ u₂ v₂ w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Source: Stacks Project, Definition 00WV and Lemma 00WW
(blueprint: lem-weil-pbc-site-continuous-pushforward-sheaf).

The four precoverage instances express the site axioms of 00VH. Covering families
are encoded by their presieves of arrows. The generated topology has exactly the
same sheaves. The hypothesis `hcover` is 00WV(a); `hpullback` is 00WV(b), expressed
as preservation of the pullback of a covering arrow with any arrow to its target.
Existence of the source pullback follows from `J.HasPullbacks`; preservation gives
existence of the target pullback and invertibility of the canonical comparison.

Proof:
1. For a covering presieve `R`, `hcover` makes `R.map F` covering. Apply `hpullback`
   to two arrows of `R`: the canonical comparison identifies their fibre products,
   compatibly with both projections (00WV).
2. The sheaf on the target satisfies the equalizer condition on `R.map F`.
   The definition of sheaf and its algebraic-valued version are those of
   lem-weil-pbc-sheaf-algebraic-structures-objects.
3. Transport this equalizer along the comparison isomorphisms. Its sections and
   maps are precisely those of `F.op ⋙ G.obj` on `R`. This proves the per-covering
   equivalence and the sheaf condition on every covering (00WW). The comparison
   between covering-family sheaves and generated-topology sheaves gives `IsSheaf`.
4. For abelian groups the same argument on underlying sets applies: restrictions
   and comparison maps are homomorphisms, so the equalizer is also an equalizer
   of abelian groups, using lem-weil-pbc-sheaf-algebraic-structures-objects. -/
theorem siteContinuous_pushforward_isSheaf
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (J : Precoverage C) (K : Precoverage D)
    [J.HasIsos] [J.IsStableUnderComposition] [J.IsStableUnderBaseChange] [J.HasPullbacks]
    [K.HasIsos] [K.IsStableUnderComposition] [K.IsStableUnderBaseChange] [K.HasPullbacks]
    (F : C ⥤ D)
    (hcover : ∀ (X : C) (R : Presieve X), R ∈ J X → R.map F ∈ K (F.obj X))
    (hpullback : ∀ (X Y Z : C) (R : Presieve X), R ∈ J X →
      ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f → PreservesLimit (cospan f g) F) :
    (∀ G : Sheaf K.toGrothendieck (Type w),
      Presheaf.IsSheaf J.toGrothendieck (F.op ⋙ G.obj) ∧
      ∀ (X : C) (R : Presieve X), R ∈ J X →
        (Presieve.IsSheafFor (F.op ⋙ G.obj) R ↔ Presieve.IsSheafFor G.obj (R.map F))) ∧
    (∀ G : Sheaf K.toGrothendieck AddCommGrpCat.{w},
      Presheaf.IsSheaf J.toGrothendieck (F.op ⋙ G.obj)) := by
  sorry

end CategoryTheory
