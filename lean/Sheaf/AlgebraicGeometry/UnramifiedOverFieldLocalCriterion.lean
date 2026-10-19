/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q31
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.FieldTheory.Separable
public import Mathlib.Topology.JacobsonSpace
public import WeilConjectures.ZetaSeries
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Unramified.Basic
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import WeilConjectures.AlgebraicGeometry.Morphisms.FormallyUnramifiedStalkNeighbourhood
import WeilConjectures.AlgebraicGeometry.Thickening
import Sheaf.AlgebraicGeometry.UnramifiedFieldFibreDecomposition

/-!
# Local criterion for unramified schemes over a field

Source: Stacks Project, Morphisms, Tag 02G7 (`lemma-unramified-over-field`),
and Tag 02GF (`lemma-unramified-at-point`)
(blueprint: lem-trf-unramified-over-field-local-criterion).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A locally finite type scheme over a field is unramified exactly when every point is
closed, its canonical local-ring residue map is bijective, and its residue field is a
finite separable extension of the base field. The field extension uses the canonical
map induced by `f`; no abstract isomorphism or arbitrary algebra structure is used.
Empty schemes are included.

Source: Stacks Project, Morphisms, Tag 02G7, with Tag 02GF, condition (6)
(blueprint: lem-trf-unramified-over-field-local-criterion).

Proof:
1. By lem-trf-unramified-field-fibre-decomposition, an unramified scheme over k is a
   disjoint union of spectra of finite separable extensions. Each component has one
   point (def-weil-affine-spectrum); its complement is open, so that point is closed.
   The component is its smallest open neighbourhood, so its stalk is the corresponding
   field. The canonical quotient to the residue field (def-weil-residue-field) is an
   isomorphism, compatible with the k-structure. This also handles the empty union.
2. Conversely, at y set L = κ(y). Apply
   lem-weil-pbc-separable-algebraic-differentials-base-change to the tower k/k/L.
   By def-weil-pbc-kahler-differentials, Ω[k/k] = 0, so Ω[L/k] = 0. Transport along
   the canonical residue isomorphism to the stalk. By
   lem-weil-pbc-formally-unramified-ring-iff-kahler-zero the stalk is formally
   unramified over k. The stalk of Spec k at its single point is k.
3. Apply lem-sbc-formally-unramified-stalk-neighbourhood at each point to obtain
   formally unramified open neighbourhoods; these cover Y, with no finiteness needed.
4. For a square-zero thickening T ⊂ T' and two lifts to Y agreeing on T, the equality
   of underlying spaces (def-sbc-first-order-thickening) makes the inverse images of
   those neighbourhoods the same for both lifts. Cover them by affine opens W.
   Then T ∩ W is an affine square-zero thickening in W. By
   def-weil-pbc-formally-unramified-morphism the lifts agree on W, hence on T'.
   This gives formal unramifiedness of f, also when Y is empty.
5. Apply lem-weil-pbc-lft-formally-unramified-unramified: local finite type and
   formal unramifiedness give an open diagonal, hence unramifiedness. -/
theorem unramified_over_field_iff_local_criterion
    {k : Type u} [Field k] {Y : Scheme.{u}} (f : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType f] :
    (LocallyOfFiniteType f ∧ IsOpenImmersion (pullback.diagonal f)) ↔
      ∀ y : Y, y ∈ closedPoints Y ∧ Function.Bijective (Y.residue y) ∧
        (f.residueFieldAlgebraMap y).Finite ∧
        @Algebra.IsSeparable k (Y.residueField y) _ _
          (f.residueFieldAlgebraMap y).toAlgebra := by
  sorry

end AlgebraicGeometry
