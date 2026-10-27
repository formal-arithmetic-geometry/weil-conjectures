/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleDimension
public import Mathlib.AlgebraicGeometry.ResidueField
import Sheaf.AlgebraicGeometry.AlgebraicSpaceLocalFibreDimensionOpen

/-!
# Upper semicontinuity of proper algebraic-space fibre dimension

Source: Stacks Project, More on Morphisms of Spaces, Tags 0D4M and 0D4Q,
lemma-dimension-fibre and lemma-dimension-fibres-proper, with a scheme target
(blueprint: lem-sfb-proper-space-fibre-dimension-upper-semicontinuous).

The dimension is the existing chartwise dimension of the residue-field sheaf fibre.
On algebraic spaces this is equally the supremum of dimensions of affine étale charts:
refine arbitrary charts by affine opens and take the supremum of their local dimensions.
The threshold -1 denotes the empty-fibre locus and is represented by dimension bottom.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- Dimension of the actual residue-field fibre of a map to a scheme. The existing
`etaleDimension` computes its dimension using scheme charts; equivalently one takes the
supremum of the topological Krull dimensions of all affine representable étale charts.
For an empty fibre that supremum is bottom. The ambient base `S` is only bookkeeping.
Source: Stacks Project, More on Morphisms of Spaces, Tag 0D4M
(blueprint: lem-sfb-proper-space-fibre-dimension-upper-semicontinuous). -/
def fibreDimensionOverScheme {S : Scheme.{u}} {T : Over S} {X : AlgebraicSpace S}
    (f : X ⟶ schemeSpace T) (t : T.left) : WithBot ℕ∞ :=
  etaleDimension (Limits.pullback f.hom.hom
    (yoneda.map (Over.homMk (T.left.fromSpecResidueField t)
      (U := Over.mk (T.left.fromSpecResidueField t ≫ T.hom)) (V := T) rfl)))

/-- Proper fibres have dimension bottom or a finite natural number, and the locus where
fibre dimension is at most any integer `a ≥ -1` is open, with closed complementary locus.
There is no flatness, finite-presentation or Noetherian assumption.
Source: Stacks Project, More on Morphisms of Spaces, Tag 0D4Q,
lemma-dimension-fibres-proper, restricted to a scheme target
(blueprint: lem-sfb-proper-space-fibre-dimension-upper-semicontinuous).

Proof:
1. Properness includes finite type. Apply `lem-sfb-space-fibre-dimension-supremum`
   (Tag 0D4M) to identify the dimension with the supremum of `localFibreDimension`
   over source points above `t`. The dimension is bottom exactly on empty fibres,
   and a finite natural number otherwise. The chartwise definition agrees with
   the supremum over affine étale charts by affine refinement and local dimensions.
2. For `a ≥ 0`, the complement of the open source locus of local fibre dimension
   at most `a` is closed by `lem-sfb-space-local-fibre-dimension-open` (Tag 04NT).
   This uses only the local finite type constituent of properness.
3. By the supremum formula, its image in the target is precisely the locus where
   fibre dimension exceeds `a`. Universal closedness, applied to the identity base
   change, makes that image closed. Its complement is the asserted open locus.
4. For `a = -1`, use the entire source as the closed subset instead. Its image is
   precisely the locus of nonempty fibres by Tag 0D4M; the complement is the locus
   of dimension bottom. This also handles an empty source or an empty target. -/
theorem proper_fibreDimension_finite_isOpen {S : Scheme.{u}}
    (T : Over S) (X : AlgebraicSpace S) (f : X ⟶ schemeSpace T)
    (hf : MapIsProper f) :
    (∀ t : T.left, fibreDimensionOverScheme f t = ⊥ ∨
      ∃ n : ℕ, fibreDimensionOverScheme f t = (n : WithBot ℕ∞)) ∧
    (∀ a : ℤ, -1 ≤ a →
      IsOpen {t : T.left | fibreDimensionOverScheme f t ≤
        (if a < 0 then ⊥ else (a.toNat : WithBot ℕ∞))} ∧
      IsClosed {t : T.left | (if a < 0 then ⊥ else (a.toNat : WithBot ℕ∞)) <
        fibreDimensionOverScheme f t}) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
