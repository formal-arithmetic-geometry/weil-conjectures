/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Q105
-/
module

public import Sheaf.AlgebraicGeometry.ChowProjectiveQcqs
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import Sheaf.AlgebraicGeometry.ClosedImmersionProducts

/-!
# Closedness and projectivity of the Chow immersions

Source: Weil conjectures blueprint, `sec-nagata-compactification/sk-thm-chow-projective`,
`det-chow-projective-closed-immersions.md` and its proof;
Stacks Project, Tags 01W3, 01W6, 01IQ, 01KR, 01KS, 01QR and 01W8
(blueprint: det-chow-projective-closed-immersions).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- For a proper morphism over a qcqs base, both Chow immersions are closed and both
resulting morphisms are projective. The map into projective space over `X` is the canonical
base-change lift of the pair `(π, i)`, with its stated projection to `X`.

Source: current blueprint, `sec-nagata-compactification/sk-thm-chow-projective`,
`det-chow-projective-closed-immersions.md` and its proof, Parts 1 and 2;
Stacks Project, Tags 01W3, 01W6, 01IQ, 01KR, 01KS, 01QR and 01W8
(blueprint: det-chow-projective-closed-immersions).

Proof:
1. Compose the proper maps `π` and `f` using `lem-weil-pbc-proper-composition`.
   The projective-space projection is proper by
   `lemma-nagata-projective-space-base-change-proper`, hence separated by
   `def-weil-proper-morphism`.
2. The compatibility `h` makes `i` an `S`-morphism from a proper `S`-scheme to a
   separated one. Thus `lem-weil-pbc-proper-to-separated` makes it proper.
   Its immersion hypothesis and `lem-weil-pbc-proper-immersion-closed` make it closed.
3. Since `f` is separated, `lem-weil-pbc-fibre-product-change-of-base-closed-immersion`
   applied to `π`, the identity of `X`, and `f` makes the graph `(id, π)` closed.
   Identify its source with `X'` by the universal property `def-pc-fibre-product`.
4. The map `i × id` from `X' ×_S X` to `ProjectiveSpace N S ×_S X` is a base change
   of `i`, hence closed by `lem-weil-pbc-closed-immersion-base-change`.
5. Compose these two closed immersions using `lem-weil-pbc-closed-immersion-products`.
   Interchange the projections and use `def-nagata-projective-space-base-change`:
   the resulting canonical map is `ProjectiveSpace.liftBaseChange π i h.symm`.
   Its projection to `X` is `π`, by the pullback universal property.
6. The two closed embeddings give H-projective factorizations as in
   `def-pc-projective-morphism`. For the integer-coordinate convention, rename a nonempty
   finite coordinate set to `Fin (r + 1)`. If `N` is empty, its projective space and `X'`
   are empty; embed `X'` into the projective zero-space over either base instead.
   Finally, properness of `π ≫ f` and `π` gives quasi-compactness by
   `def-weil-proper-morphism` and `def-weil-finite-type-morphism`, proving projectivity. -/
theorem chow_projective_closed_immersions {S X X' : Scheme.{u}} (N : Type u) [Finite N]
    (f : X ⟶ S) (π : X' ⟶ X) (i : X' ⟶ ProjectiveSpace N S)
    [CompactSpace S] [QuasiSeparatedSpace S] [IsProper f] [IsProper π] [Surjective π]
    [IsImmersion i] (h : i ≫ ProjectiveSpace N S ↘ S = π ≫ f) :
    IsProper (π ≫ f) ∧ IsClosedImmersion i ∧ IsProjective (π ≫ f) ∧
      IsClosedImmersion (ProjectiveSpace.liftBaseChange π i h.symm) ∧
      ProjectiveSpace.liftBaseChange π i h.symm ≫ ProjectiveSpace N X ↘ X = π ∧
      IsProjective π := by
  sorry

end AlgebraicGeometry
