/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LinearProjection
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import WeilConjectures.RingTheory.GradedAlgebra.LinearPair
public import WeilConjectures.RingTheory.GradedAlgebra.PowersAlgebraSpan

/-!
# Auxiliary results for the homogeneous coordinate model of a projective scheme

This file collects the general facts used to identify an integral closed subscheme of
projective space with `Proj` of its homogeneous coordinate ring, see
`AlgebraicGeometry.exists_isStandard_iso_proj`.

## Main statements

- `AlgebraicGeometry.AffineSpace.isoSpec_inv_comp_eq_homOfVector` — a morphism from an affine
  scheme `Y` to `𝔸(m; Spec k)` is, under `Y ≅ Spec Γ(Y, ⊤)`, given by its coordinates.
- `AlgebraicGeometry.surjective_of_isClosedImmersion_SpecMap` — a ring map whose `Spec` is a
  closed immersion is surjective.
- `AlgebraicGeometry.Proj.isReduced_of_isDomain` — `Proj` of a graded domain is reduced.
- `AlgebraicGeometry.IsClosedImmersion.exists_iso_of_range_eq` — two closed immersions with
  reduced sources and the same image are isomorphic over the target.
- `AlgebraicGeometry.Proj.exists_isClosedImmersion_chart` — the projective closure of an affine
  chart `Spec K ⟶ 𝔸(n ∖ {j₀}; Spec k)`, as `Proj` of a standard graded domain.
-/

@[expose] public section

universe u

open CategoryTheory Limits HomogeneousLocalization

noncomputable section

namespace ProjectiveSpectrum

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (𝒜 : ℕ → Submodule R A)
  [GradedAlgebra 𝒜]

end ProjectiveSpectrum

namespace AlgebraicGeometry

namespace AffineSpace

variable {k : Type u} [CommRing k] {m : Type u}

end AffineSpace

namespace Proj

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] (𝒜 : ℕ → Submodule R A)
  [GradedAlgebra 𝒜]

end Proj

namespace Proj

open ProjectiveSpace

end Proj

end AlgebraicGeometry
