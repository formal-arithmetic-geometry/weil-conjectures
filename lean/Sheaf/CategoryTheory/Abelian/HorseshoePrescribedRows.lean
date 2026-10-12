/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y2
-/
module

public import Mathlib.CategoryTheory.Abelian.Injective.Resolution

/-!
# Extending a fixed initial horseshoe embedding to a complex

Source: Stacks Project, Derived Categories, Tag 013T, proof Step 2, specialized
by the cokernel induction to objects with prescribed outer resolutions.
(blueprint: lem-sp-horseshoe-prescribed-row-construction).
-/

@[expose] public section

universe v u
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.InjectiveResolution

/-- Extend a chosen initial horseshoe embedding to compatible augmented complexes
with short exact rows. This only constructs a complex: positive-degree exactness,
injectivity of its terms, and the quasi-isomorphism of its augmentation are not
part of the conclusion and are verified separately.

Source: Stacks Project, Derived Categories, Tag 013T, proof Step 2, specialized
by the following cokernel induction to prescribed resolutions of objects.
(blueprint: lem-sp-horseshoe-prescribed-row-construction).

Proof: put `K.X 0 = IA.X 0 ⊞ IC.X 0` and augment by
`w = (lift, S.g ≫ IC.ι.f 0)`. The hypothesis on `lift` gives a morphism from
`S` to the split biproduct row. Its outer vertical maps are monomorphisms,
so the snake lemma makes `w` a monomorphism and gives a short exact sequence
of the three cokernels. For either outer resolution, exactness identifies the
cokernel of its augmentation with a subobject of its degree-one term. Use
these two embeddings at the next step. Extend the left embedding across the
monomorphism of the cokernel sequence into the injective left degree-one term;
pair this extension with the right embedding composed with the quotient map.
This gives the middle embedding into the degree-one biproduct. Apply the
snake lemma again to obtain the next short exact sequence of cokernels.
Continue recursively, always using the embeddings supplied by exactness of
the prescribed outer resolutions into their next injective terms.

Define each middle differential as the quotient map onto the current middle
cokernel followed by its new embedding. Consecutive differentials compose to
zero because the quotient kills the preceding embedding. The squares defining
the induced cokernel maps, followed by the embedding squares, show that the
biproduct inclusions and projections commute with differentials; hence they
assemble into `α` and `β`. Their composite is zero degreewise. The degree-zero
squares give the augmentation equalities. Each row is the canonical split
biproduct row. The identity in degree zero gives `e₀` and its equation.
Finally, the first middle differential factors through the cokernel of `w`
followed by a monomorphism, so its kernel is the image of `w`; this is the
asserted degree-zero exactness. The augmentation is the complex map determined
by `w`, which is killed by the first differential. -/
theorem exists_horseshoe_prescribed_rows
    {C : Type u} [Category.{v} C] [Abelian C]
    (S : ShortComplex C) (hS : S.ShortExact)
    (IA : InjectiveResolution S.X₁) (IC : InjectiveResolution S.X₃)
    (lift : S.X₂ ⟶ IA.cocomplex.X 0) (hlift : S.f ≫ lift = IA.ι.f 0) :
    ∃ (K : CochainComplex C ℕ)
      (ι : (CochainComplex.single₀ C).obj S.X₂ ⟶ K)
      (α : IA.cocomplex ⟶ K) (β : K ⟶ IC.cocomplex),
      IA.ι ≫ α = (CochainComplex.single₀ C).map S.f ≫ ι ∧
      ι ≫ β = (CochainComplex.single₀ C).map S.g ≫ IC.ι ∧
      (∃ e₀ : K.X 0 ≅ IA.cocomplex.X 0 ⊞ IC.cocomplex.X 0,
        ι.f 0 ≫ e₀.hom = biprod.lift lift (S.g ≫ IC.ι.f 0)) ∧
      (ShortComplex.mk (ι.f 0) (K.d 0 1) (by simp)).Exact ∧
      ∃ (hαβ : α ≫ β = 0), ∀ n : ℕ,
        ((ShortComplex.mk α β hαβ).map
          (HomologicalComplex.eval C (ComplexShape.up ℕ) n)).ShortExact := by sorry

end CategoryTheory.InjectiveResolution
