/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: N7
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Monoidal.Grp
public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.NormalScheme
import WeilConjectures.AlgebraicGeometry.EffectiveCartier
import WeilConjectures.AlgebraicGeometry.Morphisms.Slicing
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.EffectiveCartier

/-! # An ample line on a smooth connected group over an affine normal integral base

Source: Ning Guo, Divisors on coherent schemes and homogeneous spaces,
Corollary 6.14, printed p.19, March 31, 2026; the affine integral base conclusion,
applied to the group acting on itself by left translation
(blueprint: lem-sfb-affine-normal-connected-group-ample).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A smooth separated finitely presented group over an affine normal integral Noetherian
scheme has an absolutely ample invertible module on its entire total space.

Source: Guo, Divisors on coherent schemes and homogeneous spaces, Corollary 6.14,
printed p.19, March 31, 2026, affine integral base clause, with the left translation action
(blueprint: lem-sfb-affine-normal-connected-group-ample).

Proof plan:
1. Apply lem-sfb-normal-group-affine-fibre-transversal to obtain one affine open V in H
   meeting every fibre. This is the global input; a chart after shrinking S does not suffice.
2. Finite presentation gives quasi-compactness and quasi-separatedness. Apply
   lem-sbc-smooth-section-component-geometrically-irreducible to the unit section. Its open
   contains the connected component of the unit in every fibre. Connectedness makes this
   the whole fibre, so every fibre is geometrically irreducible. The nonempty open V in
   each fibre is consequently dense.
3. Apply lem-sfb-smooth-normal-affine-boundary-cartier to V: the reduced complement D is
   an effective Cartier divisor, including when the complement is empty.
4. By lemma-nagata-effective-cartier-is-invertible its ideal I_D is invertible. Define
   L = I_D dual as in def-pc-divisor-line-bundle. It is invertible by
   def-sc-invertible-module. The inclusion I_D into O_H defines a section sigma of L.
   In a frame I_D = f O_H its coefficient in the dual frame is f, so its nonvanishing
   locus, in the sense of def-weil-pbc-ample-invertible-module, is exactly V. These local
   sections agree because they express the same inclusion.
5. Apply lem-sfb-group-affine-section-ampleness with exponent one and section sigma:
   its locus V is affine and meets every fibre. The conclusion is absolute ampleness
   on all of H, over the original base S.
-/
theorem exists_isAmple_of_affine_normal_connected_group
    (S : Scheme.{u}) [IsAffine S] [IsNoetherian S] (hS : IsNormalScheme S)
    (H : Over S) [GrpObj H] [Smooth H.hom] [IsSeparated H.hom]
    [LocallyOfFinitePresentation H.hom] [QuasiCompact H.hom] [QuasiSeparated H.hom]
    [GeometricallyConnected H.hom] :
    ∃ (L : H.left.Modules) (_ : L.IsInvertible), Scheme.Modules.IsAmple H.left L := by
  sorry

end AlgebraicGeometry
