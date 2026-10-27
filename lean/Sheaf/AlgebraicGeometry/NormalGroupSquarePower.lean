/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NX
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.Topology.Connected.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.AlgebraicGeometry.Morphisms.Slicing
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.AlgebraicGeometry.RegularNormalDecomposition

/-!
# A positive tensor power satisfies the square identity on a normal-base group

Source: Guo, Divisors on coherent schemes and homogeneous spaces, Proposition 5.9,
final assertion, case (1), applied to the left multiplication action on the group;
finite disjoint normal-component extension (blueprint: lem-sfb-normal-group-square-power).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

/-- A positive tensor power of a line bundle satisfies the square condition for left
multiplication on a smooth separated finitely presented group with connected fibres over
an affine locally Noetherian normal base. Neither the base nor the group is assumed integral,
connected, proper, or commutative beyond the explicitly stated fibre condition.

Here `H ⊗ B` in `Over S` is `H ×_S B`. The morphism
`(snd H B ≫ g) * fst H B` is `(x,b) ↦ g(b)x`; hence its tensor pullback of `L.tensorPow r`
is canonically the translation pullback of the base-changed line. The base line and the
isomorphism are existential propositions, with no coherence data.

Source: Guo, Proposition 5.9, final assertion, case (1)
(blueprint: lem-sfb-normal-group-square-power).

Proof:
1. Apply `lem-sbc-smooth-section-component-geometrically-irreducible` to the identity
   section. Connectedness of each fibre makes the section component the entire fibre.
   Smooth geometric reducedness (`sbc-lem-smooth-geometrically-reduced`) then makes every
   fibre geometrically integral (`def-pc-geometrically-irreducible`, `def-pc-integral-scheme`).
2. Affineness and local Noetherianness make the base Noetherian. Decompose it into finitely
   many clopen normal integral components by `rem-pc-regular-normal`. On the empty base use
   exponent one. Smoothness, separatedness and finite presentation survive restriction by
   `lem-pc-proper-base-change`, `lem-weil-pbc-separated-base-change`, and
   `lem-weil-pbc-qcqs-morphism-permanence`.
3. On a component put `a(u,v,x) = uv⁻¹x` and `A = a*L`. Apply
   `lem-sfb-field-product-square-power` to its generic fibre, giving a positive exponent n.
   Pullback commutes with tensors and duals, checked on local rank-one generators.
4. Apply `lem-sfb-normal-product-square-descent` to `A.tensorPow n`. Its four-term square
   difference descends to a line on the four group factors.
5. Pull back along `x ↦ (g,e,h⁻¹,e,x)`. The four evaluations of a are ghx, x, gx, hx.
   Cancel the inverse lines using `def-sc-invertible-module`; pullback composition is
   `def-pc-module-pullback`. This gives the displayed identity without commuting factors.
6. Take the product r of the component exponents. Raise each component identity to r/n,
   and glue its base lines and isomorphisms over the finite disjoint clopen cover of B.
   On an open V the glued sheaf has the product of sections on its component intersections.
   It is locally free of rank one and gives the identity for every B, g, h. -/
theorem exists_tensorPow_square_of_normal_base
    (S : Scheme.{u}) [IsAffine S] [IsLocallyNoetherian S]
    (hS : ∀ s : S, IsDomain (S.presheaf.stalk s) ∧
      IsIntegrallyClosed (S.presheaf.stalk s))
    (H : Over S) [GrpObj H] [Smooth H.hom] [IsSeparated H.hom]
    [LocallyOfFinitePresentation H.hom] [QuasiCompact H.hom] [QuasiSeparated H.hom]
    (hH : ∀ s : S, ConnectedSpace (H.hom.fiber s))
    (L : H.left.Modules) [L.IsInvertible] :
    ∃ r : ℕ, 1 ≤ r ∧ ∀ (B : Over S) (g h : B ⟶ H),
      ∃ N : B.left.Modules, N.IsInvertible ∧
        Nonempty
          (((Scheme.Modules.tensorPullback
              (((snd H B ≫ (g * h)) * fst H B).left)).obj (L.tensorPow r) ⊗
            (Scheme.Modules.tensorPullback (fst H B).left).obj (L.tensorPow r)) ≅
           (((Scheme.Modules.tensorPullback
               (((snd H B ≫ g) * fst H B).left)).obj (L.tensorPow r) ⊗
             (Scheme.Modules.tensorPullback
               (((snd H B ≫ h) * fst H B).left)).obj (L.tensorPow r)) ⊗
            (Scheme.Modules.tensorPullback (snd H B).left).obj N)) := by
  sorry

end AlgebraicGeometry
