/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q42
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.Mathlib.Topology.KrullDimension
import Sheaf.AlgebraicGeometry.FiniteTypeDimensionFormula
import Sheaf.AlgebraicGeometry.CompositeFibreLocalModels
import WeilConjectures.Topology.PresheafModuleStalkFunctor
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Local fibre dimension inequality for a composite

Source: Stacks Project, Morphisms, Tag 02JS, first assertion
(blueprint: lem-trf-composite-fibre-dimension-inequality).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Local fibre dimensions are subadditive under composition of locally finite type morphisms.
Source: Stacks Project, Morphisms, Tag 02JS, first assertion
(blueprint: lem-trf-composite-fibre-dimension-inequality).

Proof:
1. Put `y = f x` and `t = g y`. Choose affine neighbourhoods in the three fibres
   `X_t`, `X_y`, and `Y_t`. Local finite type is preserved by composition and base change,
   so these neighbourhoods are finite type over their respective residue fields.
   The affine-spectrum fibre-product identification
   (`lem-weil-pbc-fibre-product-affine-spectra`) identifies their rings with tensor products.
   By `pqf-lem-locnoeth-lft`, the three fibre stalks are Noetherian.
2. Apply `lem-kun-dimension-formula` to the three finite type affine neighbourhoods.
   By `lem-weil-pbc-dimension-at-point-open-subspace`, their local topological dimensions
   equal those in the entire fibres. Each is the dimension of its stalk plus the
   transcendence degree of its residue field over the ground residue field.
3. By `lem-sbc-composite-fibre-local-models`, the map
   `A = O_{Y_t,y} → B = O_{X_t,x}` is local between Noetherian local rings, with closed
   fibre canonically `B / m_A B ≅ O_{X_y,x}`. Apply
   `lem-trf-local-fibre-ring-dimension-inequality` (Stacks 00OM) at the maximal ideals:
   `dim B ≤ dim A + dim O_{X_y,x}`. This step does not require flatness.
4. Apply `lem-sbc-transcendence-degree-tower` to `κ(t) → κ(y) → κ(x)`:
   `trdeg_{κ(t)} κ(x) = trdeg_{κ(y)} κ(x) + trdeg_{κ(t)} κ(y)`.
   Substitute into the three formulas of step 2 and the inequality of step 3, and regroup
   the sums to obtain `dim_x X_t ≤ dim_x X_y + dim_y Y_t`.
-/
theorem composite_fibre_dimension_at_point_le
    {X Y T : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ T)
    [LocallyOfFiniteType f] [LocallyOfFiniteType g] (x : X) :
    topologicalKrullDimAt ((f ≫ g).asFiber x) ≤
      topologicalKrullDimAt (f.asFiber x) + topologicalKrullDimAt (g.asFiber (f x)) := by
  sorry

end AlgebraicGeometry
