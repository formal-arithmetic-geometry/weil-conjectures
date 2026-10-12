/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X3
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-!
# Affineness of a finite locally free norm locus

Source: Stacks Project, Tag 03JE, final norm argument.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace CategoryTheory.Over.DescentDatum

/-- A norm locus contained in an affine basic open is affine.
Source: Stacks Project, Tag 03JE, final norm argument.

Proof: Restrict the finite, flat, locally finitely presented morphism s to W. It is
finite locally free, and t on its source factors through A by hWA. Pull f back along
this restriction of t, and form the determinant norm g on W. On a trivializing open
of W the source algebra is finite free. Reducing multiplication by the pulled-back
section modulo the residue field of x shows that its determinant is nonzero exactly
when that section is a unit in the fibre algebra: equivalently it is nonzero at every
point of that fibre. Determinants commute with localization and changes of basis,
so these local norms glue to g, even when the rank varies. Thus the nonvanishing
locus of g, regarded as an open of V, is W intersected with the complement of the
s-image of the t-preimage of the complement of D(f). By hUset this is U. Since
D(f) is contained in W, restrict g to D(f). By hU its nonvanishing locus is still
U. The open D(f) is affine by hA, and a basic open in an affine scheme is affine.
The empty W and rank-zero components obey the same determinant criterion (the
empty determinant is 1); no surjectivity, constant rank, or field base is required.
(blueprint: lem-pd-descent-norm-locus-affine). -/
theorem isAffineOpen_descent_norm_locus
    {V R : Scheme.{u}} (s t : R ⟶ V)
    [IsFinite s] [Flat s] [LocallyOfFinitePresentation s]
    (A : V.Opens) (hA : IsAffineOpen A) (W : V.Opens)
    (hWA : s ⁻¹' (W : Set V) ⊆ t ⁻¹' (A : Set V))
    (f : Γ(V, A)) (hfW : V.basicOpen f ≤ W)
    (U : V.Opens) (hU : U ≤ V.basicOpen f)
    (hUset : (U : Set V) = (W : Set V) ∩
      (s '' (t ⁻¹' (V.basicOpen f : Set V)ᶜ))ᶜ) :
    IsAffineOpen U := by
  sorry

end CategoryTheory.Over.DescentDatum
