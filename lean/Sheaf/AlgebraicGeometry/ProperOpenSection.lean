/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import Sheaf.AlgebraicGeometry.ProperOpenComparison
public import Mathlib.AlgebraicGeometry.OpenImmersion

/-!
# The section and open pullback for a proper morphism

Source: literature/blueprint/master/blueprint/sec-smooth-purity/
sk-def-sf-operations/lem-weil-pbc-proper-open-section.md,
node lem-weil-pbc-proper-open-section, order 1478 (blueprint: lem-weil-pbc-proper-open-section).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- For a proper morphism and compatible open immersions, the canonical section of the
pullback is an open immersion with clopen image, while the first projection identifies
that pullback with the inverse image of the second open immersion.

Source: literature/blueprint/master/blueprint/sec-smooth-purity/
sk-def-sf-operations/lem-weil-pbc-proper-open-section.md,
node lem-weil-pbc-proper-open-section, order 1478 (blueprint: lem-weil-pbc-proper-open-section).

Proof: The pair `(j₁, id)` gives the section by the pullback universal property.
Base change of the open immersion `j₂` makes the first projection an open immersion
and identifies its range with the inverse image of `j₂(X)`.  The section is the
restriction of `j₁` to this open subscheme, hence is an open immersion and satisfies
`s ≫ p = id`.  The properness of `u` makes `p` separated; the clopen-section theorem
then gives that the section image is both open and closed.
More explicitly, the defining equation `s ≫ b = j₁` and the injectivity of `b`
identify the image of `s` with the inverse image of `j₁(X)` under `b`.
The geometric steps use def-pc-fibre-product, lem-weil-pbc-open-immersion-base-change,
def-weil-open-immersion, lem-weil-pbc-proper-open-p-proper, and
lem-weil-pbc-open-section-clopen, in that order. -/
theorem properOpenSectionProperties {T₁ T₂ X : Scheme.{u}}
    (u : T₁ ⟶ T₂) [IsProper u] (j₁ : X ⟶ T₁) (j₂ : X ⟶ T₂)
    [IsOpenImmersion j₁] [IsOpenImmersion j₂] (h : j₁ ≫ u = j₂) :
    IsOpenImmersion (properOpenSection u j₁ j₂ h) ∧
      properOpenSection u j₁ j₂ h ≫ (pullback.snd u j₂) = 𝟙 X ∧
      IsClopen (Set.range (properOpenSection u j₁ j₂ h).base) ∧
      Set.range (properOpenSection u j₁ j₂ h).base =
        (pullback.fst u j₂).base ⁻¹' Set.range j₁.base ∧
      IsOpenImmersion (pullback.fst u j₂) ∧
      Set.range (pullback.fst u j₂) =
        (u.base ⁻¹' Set.range j₂.base) := by
  sorry

end AlgebraicGeometry.Etale
