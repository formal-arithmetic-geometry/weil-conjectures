/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Maps from reduced schemes through closed subschemes

Source: literature/stacks-project/schemes.tex, Lemma 0356 (blueprint:
lem-weil-pbc-reduced-source-factors-through-closed-subscheme)
-/

@[expose] public section

universe u

open CategoryTheory
namespace AlgebraicGeometry

/-- A morphism from a reduced scheme factors through a closed subscheme exactly
set-theoretically; every map factors through the reduction.

Source: Stacks Project, Schemes, Lemma 0356, lines 2268-2289
(blueprint: lem-weil-pbc-reduced-source-factors-through-closed-subscheme).
Proof:
1. If `f = g ≫ i`, its underlying image is contained in the image of `i`
   (`def-pc-scheme`).
2. Conversely, assume the image inclusion and let `I` be the ideal sheaf of `i`
   (`def-sbc-closed-immersion-ideal-sheaf`). For an affine open `U` of `X`,
   a section `a ∈ I(U)`, and an affine open `V ⊆ f⁻¹(U)` of `Y`, let `b` be
   the restriction to `V` of the pullback of `a`. At `y ∈ V`, the image point
   `x = f(y)` lies in `i(Z)`, so `a` belongs to the prime of `x`
   (`lem-weil-pbc-closed-immersion-image-zero-locus`). Its residue at `x` is zero
   (`lem-weil-pbc-affine-open-section-vanishing-prime`), and the local stalk map
   sends its germ into the maximal ideal at `y` (`def-pc-scheme`,
   `def-weil-residue-field`). Thus the residue of `b` at `y` is zero.
3. The same section-vanishing lemma puts `b` in the prime of every point of `V`.
   All primes of `Γ(V, 𝒪_Y)` arise from such points
   (`lem-weil-pbc-affine-open-spec-points`). Their intersection is the nilradical
   (`lem-weil-pbc-zero-locus-eq-iff-radical-eq`), so `b` is nilpotent and hence
   zero because `Y` is reduced (`def-pc-reduced-scheme`).
4. Affine opens cover `f⁻¹(U)` (`lem-weil-pbc-affine-opens-basis`); the sheaf
   property (`def-pc-scheme`) makes the pullback section zero on all of `f⁻¹(U)`.
5. Thus the pullback kills `I(U)` on every affine open `U`, and
   `lem-weil-pbc-closed-immersion-lift-ideal-kills-sections` gives the factorization.
6. The reduction immersion is a closed immersion with full underlying image
   (`def-weil-pbc-scheme-reduction`); applying the equivalence to it gives the
   final factorization for every `f`.
-/
theorem reduced_source_factors_through_closed_subscheme
    {X Y Z : Scheme.{u}} [IsReduced Y]
    (i : Z ⟶ X) [IsClosedImmersion i] (f : Y ⟶ X) :
    ((∃ g : Y ⟶ Z, g ≫ i = f) ↔ Set.range f.base ⊆ Set.range i.base) ∧
      (∃ g : Y ⟶ X.nilradical.subscheme, g ≫ X.nilradical.subschemeι = f) := by
  sorry

end AlgebraicGeometry
