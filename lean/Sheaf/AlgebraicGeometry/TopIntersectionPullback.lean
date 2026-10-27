/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Sheaf.AlgebraicGeometry.IntersectionNumber
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Sheaf.TraceFormula.LocalDimensionFormula
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex
import WeilConjectures.AlgebraicGeometry.Cohomology.LongExact
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections
import WeilConjectures.AlgebraicGeometry.HigherDirectImageOpenRestriction
import Sheaf.AlgebraicGeometry.NumericalPolynomialLeadingTerm

/-! # Top self-intersection under a morphism of proper integral varieties

Source: Stacks Project, Varieties, Tag 0BET, lemma-intersection-number-and-pullback,
with the whole source as the integral closed subscheme and all entries equal
(blueprint: lem-sfb-top-intersection-pullback).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- Top self-intersection after pullback is multiplied by the degree of the canonical
function-field extension for a dominant morphism, and is zero for a nondominant one.
Finiteness of the field extension is part of the conclusion; the morphism need not be finite.
Source: Stacks Project, Varieties, Tag 0BET, lemma-intersection-number-and-pullback
(blueprint: lem-sfb-top-intersection-pullback).

Proof:
1. The morphism is proper by `lemma-nagata-proper-to-separated-target`. The target is
Noetherian by `lem-weil-pbc-finite-type-over-noetherian`. By `lem-pc-coherent-hi`, its
higher direct images of the structure module are coherent and eventually zero.
Apply the Euler--Leray clause of `lem-pc-euler-additive` to the pullback of the integer
powers of the line bundle, then `lem-pc-projection-formula` to identify the summands
with those higher images tensored by the powers. Pullback commutes with these powers
by trivializing the line bundle locally; negative powers are powers of its dual.
2. If the image is not dense, it is a proper closed subset. Restriction of the higher
images to its complement vanishes by `lem-pc-higher-direct-image-open-restriction`.
Their supports have dimension at most g-1 (extend each irreducible closed chain by
Y). By `lem-sc-snapper-numerical-polynomial`, their Euler polynomials have total degree
less than g. The coefficient defining the intersection number is therefore zero.
3. In the dominant case, `lem-sfb-equal-dimension-generic-structure-image` gives a finite
canonical function-field extension of degree e, identifies the generic stalk of the
zeroth direct image with k(X), and makes the positive higher images vanish over a
nonempty open. Their supports again have dimension less than g, so Snapper removes
all positive higher images from the coefficient under consideration.
4. The support of the zeroth direct image is all of Y and its generic multiplicity is
e: over the generic local field it is the vector space k(X). By
`lem-sc-numerical-polynomial-leading-term`, its Euler polynomial differs from e times
that of the structure module by degree less than g. Extract the coefficient of the
product of the g variables, using `def-sc-intersection-number`, to obtain the formula.
The pullback-invertibility proof supplied to the existing definition is the established
clause of `lem-weil-pbc-invertible-pullback-tensor`, not an additional hypothesis. -/
theorem selfIntersectionNumber_tensorPullback
    (k : Type u) [Field k] (X Y : Scheme.{u})
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsIntegral X] [IsIntegral Y]
    [IsProper (X ↘ Spec (.of k))] [IsProper (Y ↘ Spec (.of k))]
    (g : ℕ) (_hg : 1 ≤ g)
    (hX : topologicalKrullDim X = ((g : ℕ∞) : WithBot ℕ∞))
    (hY : topologicalKrullDim Y = ((g : ℕ∞) : WithBot ℕ∞))
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] (L : Y.Modules) [L.IsInvertible] :
    (∀ [IsDominant f],
      @Module.Finite Y.functionField X.functionField _ _
        (f.dominantFunctionFieldAlgebra).toModule ∧
      @selfIntersectionNumber k _ X _ _ X _ (𝟙 X) inferInstance g hX
          ((tensorPullback f).obj L) ((invertible_pullback_tensor f).1 L).2 =
        (@Module.finrank Y.functionField X.functionField _ _
          (f.dominantFunctionFieldAlgebra).toModule : ℚ) *
          selfIntersectionNumber k Y Y (𝟙 Y) g hY L) ∧
    (¬ IsDominant f →
      @selfIntersectionNumber k _ X _ _ X _ (𝟙 X) inferInstance g hX
        ((tensorPullback f).obj L) ((invertible_pullback_tensor f).1 L).2 = 0) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
