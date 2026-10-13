/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.RingTheory.KrullDimension.Basic
public import WeilConjectures.Mathlib.Topology.KrullDimension
import Sheaf.AlgebraicGeometry.RestrictedFibreLocallyNoetherian

/-! # Constant fibre dimension near a zero-dimensional fibre stalk

Source: Stacks Project, Tags 045U, 02NM and 02NJ.
(blueprint: lem-sbc-flat-fibre-dimension-near-zero-dimensional-stalk)
-/

@[expose] public section

universe u
open CategoryTheory Topology
namespace AlgebraicGeometry

/-- A zero-dimensional fibre stalk has a neighbourhood of constant fibre dimension.

The local ring dimension at x is zero, whereas the local *topological* dimension of
the fibre near x is n. These numbers need not agree: at the generic point of an
affine line they are zero and one, respectively.

Source: Stacks Project, Tags 045U (openness), 02NM (relative dimension decomposition),
and 02NJ (equidimensional fibres).
Proof: Restrict f over U. Identify its fibre at f(x) with the original fibre, using
the pullback square for restriction and the residue-field isomorphism at a point
of an open subscheme. This identifies the fibre stalk at x with the given stalk.
The fibre is locally of finite type over a field, hence locally Noetherian. Its
zero-dimensional local ring at x is Artinian and Cohen-Macaulay: the empty regular
sequence has maximal possible length zero. By Tag 045U the Cohen-Macaulay locus is
open. Restrict to that locus; the resulting morphism is flat, locally finitely
presented and has Cohen-Macaulay fibres. Tag 02NM decomposes this locus into open
and closed pieces of relative dimension n. Take the piece containing x, and map
it into X by the two open restriction inclusions, giving V. Its image lies over U.
The fibres of this piece are equidimensional of dimension n by Tag 02NJ. Every
nonempty open neighbourhood in such a fibre has dimension n, so its local
topological dimension at each point is n. The fibre of the piece is an open
subscheme of the original fibre, and local topological dimension is unchanged by
an open embedding. These identifications give the equality for every y in V.
Empty schemes and the empty base open have no x satisfying the hypotheses.
(blueprint: lem-sbc-flat-fibre-dimension-near-zero-dimensional-stalk) -/
theorem exists_constant_fibre_dimension_neighbourhood_of_stalk_dimension_zero
    {X T : Scheme.{u}} (f : X ⟶ T) (U : T.Opens)
    [Flat (f ∣_ U)] [LocallyOfFinitePresentation (f ∣_ U)]
    (x : X) (hx : f x ∈ U)
    (hdim : ringKrullDim ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) = 0) :
    ∃ (n : ℕ) (V : X.Opens), x ∈ V ∧
      ∀ y ∈ V, f y ∈ U ∧ topologicalKrullDimAt (f.asFiber y) = (n : WithBot ℕ∞) := by
  sorry

end AlgebraicGeometry
