/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.RingTheory.KrullDimension.Basic
public import Sheaf.RingTheory.Depth
public import WeilConjectures.Mathlib.Topology.KrullDimension

/-! # Fibre flatness on a quasi-finite polynomial chart

Source: Stacks Project, Tags 00RE and 00R7, as used in Tag 00RH.
(blueprint: lem-sbc-polynomial-chart-fibre-flat-criterion)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- Flatness on a quasi-finite polynomial chart is equivalent to Cohen-Macaulayness
of the original fibre stalk together with the expected dimension of its fibre.

Source: Stacks Project, Tags 00RE, 00R7, 00RH and 00N8.
Proof: An open immersion identifies the fibre stalk of U.ι followed by f with
that of f at U.ι x, and preserves the topological dimension at the fibre point.
Work in the affine coordinate rings A of T and B of U. The factorization gives
an A-algebra map P = A[t_1,...,t_n] to B. It is finitely presented and quasi-finite.
Put p equal to the prime in A below x. After base change to κ(p), its localized
source is a regular polynomial local ring and the closed fibre is Artinian.
Tag 00RE says that the map on these fibre local rings is flat if and only if
the target is Cohen-Macaulay and its fibre dimension at the point is n. For the
forward direction of that result, flatness preserves a regular system of
parameters; the Artinian quotient has dimension and depth zero, and the flat
local depth and dimension formulas give equality of depth and dimension.
For the converse, quasi-finiteness gives a finite residue extension, hence equal
residue transcendence degrees. The dimension n assumption and the finite-type
field dimension formula give equality of the two local dimensions. Miracle
flatness then gives flatness of the fibre map. To pass from fibre flatness to
flatness of P localized at the image of x to B localized at x, use Tag 00R7:
B is flat over A because f is flat, both local maps are essentially finitely
presented, and the self-module B_x is nonzero and finitely presented over itself.
In the other direction stalk flatness survives base change to κ(p). Finally,
Tag 00N8 identifies the self-module Cohen-Macaulay condition with the displayed
depth equality. This argument concerns only a point and asserts no openness.
(blueprint: lem-sbc-polynomial-chart-fibre-flat-criterion) -/
theorem polynomial_chart_flat_stalk_iff_fibre_depth_and_dimension
    {X T : Scheme.{u}} [IsAffine T] (f : X ⟶ T)
    [Flat f] [LocallyOfFinitePresentation f]
    (U : X.Opens) [IsAffine U.toScheme] (n : ℕ)
    (e : U.toScheme ⟶ AffineSpace (ULift.{u} (Fin n)) T)
    [LocallyOfFinitePresentation e] [LocallyQuasiFinite e]
    (he : e ≫ (AffineSpace (ULift.{u} (Fin n)) T ↘ T) = U.ι ≫ f)
    (x : U.toScheme) :
    (e.stalkMap x).hom.Flat ↔
      (IsLocalRing.depth
          (R := (f.fiber (f (U.ι x))).presheaf.stalk (f.asFiber (U.ι x)))
          ((f.fiber (f (U.ι x))).presheaf.stalk (f.asFiber (U.ι x))) : WithBot ℕ∞) =
        ringKrullDim ((f.fiber (f (U.ι x))).presheaf.stalk (f.asFiber (U.ι x))) ∧
      topologicalKrullDimAt (f.asFiber (U.ι x)) = (n : WithBot ℕ∞) := by sorry

end AlgebraicGeometry
