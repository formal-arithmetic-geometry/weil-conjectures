/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift

/-! # Left exact functors and cohomology

Source: literature/stacks-project/derived.tex, Lemma 015I (lemma-cartan-eilenberg), using the
split short exact sequences from injectivity
(blueprint: lem-sp-cart-eilenberg-left-exact-cohomology)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace CategoryTheory

/-- If all cycles `Z^q(C)` and boundaries `B^q(C) = im(d^{q-1})` of a bounded-below complex are
injective, then for an additive left exact functor `G` the canonical comparison
`H^q(G(C)) → G(H^q(C))` induced by the maps on cycles and quotients is an isomorphism: there is
an isomorphism `φ` whose composite with the cycle map `G(Z^q(C)) → Z^q(G(C))` (lifting
`G(Z^q(C) ↪ C^q)`) and the projection `Z^q(G(C)) → H^q(G(C))` is `G` of the projection
`Z^q(C) → H^q(C)`; since the cycle map is an isomorphism and the projection is epi, this
equation determines `φ` as the canonical comparison.
Source: literature/stacks-project/derived.tex, Lemma 015I (lemma-cartan-eilenberg)
(blueprint: lem-sp-cart-eilenberg-left-exact-cohomology)

Proof: fix `q`. The short exact sequences `0 → B^q → Z^q → H^q → 0` and
`0 → Z^q → C^q → B^{q+1} → 0` split because their subobjects `B^q` and `Z^q` are injective.
Applying the additive left exact functor `G` preserves the splittings; left exactness identifies
`ker(G(C^q) → G(C^{q+1}))` with `G(Z^q)`, and the image of `G(C^{q-1}) → G(C^q)` is `G(B^q)`, so
`0 → G(B^q) → G(Z^q) → G(H^q) → 0` is split exact and the comparison induced by the maps on
cycles and quotients is an isomorphism `H^q(G(C)) ≅ G(H^q(C))`. -/
theorem cartanEilenberg_leftExact_cohomology
    {A B : Type*} [Category A] [Category B]
    [Abelian A] [Abelian B]
    (C : CochainComplex A ℤ)
    (hbounded : ∃ n : ℤ, ∀ q : ℤ, q < n → IsZero (C.X q))
    (hcycles : ∀ q : ℤ, Injective (C.cycles q))
    (hboundaries : ∀ q : ℤ, Injective (image (C.d (q - 1) q)))
    (G : A ⥤ B) [G.Additive] [PreservesFiniteLimits G] :
    ∀ q : ℤ, ∃ φ : ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj C).homology q ≅
        G.obj (C.homology q),
      ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj C).liftCycles
          (G.map (C.iCycles q)) (q + 1) (by simp)
          (by simp [← G.map_comp]) ≫
        ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj C).homologyπ q ≫ φ.hom =
      G.map (C.homologyπ q) := by
  sorry

end CategoryTheory
