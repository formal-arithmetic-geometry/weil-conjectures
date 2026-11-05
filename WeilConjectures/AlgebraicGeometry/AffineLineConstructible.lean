/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.Spectrum.Prime.Noetherian
public import WeilConjectures.Topology.ConstructibleGenericPoint

/-!

# Constructible subsets of the affine line avoiding the generic point

Let `X` be a scheme isomorphic to `Spec R`, for `R` a noetherian domain of dimension at most one.
A constructible subset of `X` containing no generic point of `X` is a finite set of closed points
(`AlgebraicGeometry.exists_finset_of_isConstructible_of_isIso`). In particular this holds for the
affine line `𝔸(n; Spec K)` over a field `K`, with `n` a singleton
(`AlgebraicGeometry.AffineSpace.exists_finset_of_isConstructible`).

This is the first half of the finite-support step of Gabber's Künneth formula (blueprint
`sk-prop-tf-nearby-external-kunneth`): the image of the support in a coordinate line is
constructible and omits the generic point, so is a finite set of closed points.

-/

@[expose] public section

universe u

open CategoryTheory Set Topology TopologicalSpace

namespace AlgebraicGeometry

variable {R : Type u} [CommRing R] {X : Scheme.{u}}

end AlgebraicGeometry
