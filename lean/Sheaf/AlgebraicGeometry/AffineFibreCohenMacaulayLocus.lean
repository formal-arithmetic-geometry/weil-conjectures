/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.RingTheory.KrullDimension.Basic
public import Sheaf.RingTheory.Depth

/-! # Affine fibre Cohen-Macaulay locus

Source: Stacks Project, Tags 00RI, 00RH, 00N8.
(blueprint: lem-sbc-affine-fibre-cohen-macaulay-locus-open)
-/

@[expose] public section

universe u
open CategoryTheory Topology
namespace AlgebraicGeometry

/-- The fibre depth-equals-dimension locus for a flat finitely presented map
between affine schemes is open.

Source: Stacks Project, Tag 00RI, via Tag 00RH; Tag 00N8.
Proof: Identify X and T with spectra of their global section rings B and A.
Flatness and local finite presentation give a flat finitely presented map A → B.
The fibre stalk at q is the local ring B_q ⊗_A κ(p), where p is the inverse image
of q. It is Noetherian, since B is finitely presented over A and κ(p) is a field.
Its self-module is Cohen-Macaulay precisely when its depth equals its dimension.
For completeness, the affine openness argument of Tag 00RH is as follows. At a
Cohen-Macaulay fibre point of relative dimension d, localize B away from q to get
a quasi-finite map A[t₁,…,t_d] → B (Tag 00QE). On the fibre at p its localization
at q is flat by the Cohen-Macaulay criterion for quasi-finite maps over polynomial
rings (Tag 00RE). Since B is flat over A, the fibrewise flatness criterion
(Tag 00R7) implies flatness over the polynomial ring at q. Openness of flatness
(Tag 00RC) gives a further principal neighborhood where this polynomial map is
flat. At every point of that neighborhood its fibre over A is a flat
quasi-finite algebra over a polynomial ring over a field, and Tag 00RE makes the
local fibre ring Cohen-Macaulay. Thus each point of the locus has a principal
open neighborhood contained in the locus. The union of these neighborhoods is
open, and transport along the affine scheme isomorphisms gives the result.
There are no points when B is the zero ring; the locus is then empty.
(blueprint: lem-sbc-affine-fibre-cohen-macaulay-locus-open) -/
theorem isOpen_fibre_depth_eq_ringKrullDim_of_isAffine
    {X T : Scheme.{u}} [IsAffine X] [IsAffine T]
    (f : X ⟶ T) [Flat f] [LocallyOfFinitePresentation f] :
    IsOpen {y : X |
      (IsLocalRing.depth (R := (f.fiber (f y)).presheaf.stalk (f.asFiber y))
        ((f.fiber (f y)).presheaf.stalk (f.asFiber y)) : WithBot ℕ∞) =
          ringKrullDim ((f.fiber (f y)).presheaf.stalk (f.asFiber y))} := by sorry

end AlgebraicGeometry
