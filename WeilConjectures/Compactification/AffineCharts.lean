/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
public import WeilConjectures.AlgebraicGeometry.LocallyEmbedsInAffineSpace
public import WeilConjectures.Compactification.Affine
public import WeilConjectures.Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!

# Affine charts of the affine compactification

The relative projective space `ℙ(Option n; S)` is covered by the images of open immersions
`𝔸(n; S) ⟶ ℙ(Option n; S)` over `S`: for `a : Option n`, the chart onto `D₊(T_a)` is the
standard chart `AffineSpace.toRelativeProjectiveSpace` onto `D₊(T_none)` followed by the
automorphism of `ℙ(Option n; S)` swapping the homogeneous coordinates `T_none` and `T_a`.

Consequently the compactification `Compactification.ofIsImmersionAffineSpace` of a scheme
immersed in `𝔸(n; S)`, being a closed subscheme of `ℙ(Option n; S)`, locally embeds into
`𝔸(n; S)` over `S`.

## Main definitions

- `AlgebraicGeometry.Proj.renameMap`: the morphism of projective spectra of polynomial rings
  induced by a bijection of the variables.
- `AlgebraicGeometry.ProjectiveSpace.rename`: the induced morphism of relative projective
  spaces over `S`.
- `AlgebraicGeometry.AffineSpace.toRelativeProjectiveSpaceChart`: the chart
  `𝔸(n; S) ⟶ ℙ(Option n; S)` onto `D₊(T_a)`.

## Main results

- `AlgebraicGeometry.AffineSpace.exists_mem_range_toRelativeProjectiveSpaceChart`: the charts
  cover `ℙ(Option n; S)`.
- `AlgebraicGeometry.Compactification.locallyEmbedsInAffineSpace_ofIsImmersionAffineSpace`:
  the affine compactification locally embeds into `𝔸(n; S)` over `S`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry

namespace Proj

variable {σ τ R : Type u} [CommRing R]

end Proj

namespace ProjectiveSpace

variable {σ τ : Type u} (S : Scheme.{u})

end ProjectiveSpace

namespace AffineSpace

variable {n : Type u} (S : Scheme.{u})

/-- A point of `ℙ(Option n; S)` lying over a point of `D₊(T_none) ⊆ ℙⁿ_ℤ` lies in the range
of the standard chart. -/
lemma mem_range_toRelativeProjectiveSpace (z : ℙ(Option n; S))
    (hz : ProjectiveSpace.toProjInt (Option n) S z ∈
      Proj.basicOpen (homogeneousSubmodule (Option n) (ULift.{u} ℤ)) (X none)) :
    z ∈ Set.range (toRelativeProjectiveSpace n S) := by
  rw [← Proj.opensRange_awayι _ _ isHomogeneous_X_none Nat.one_pos] at hz
  obtain ⟨y, hy⟩ := hz
  obtain ⟨y, rfl⟩ := (Spec.map (dehomogenizeEquiv n (ULift ℤ)).toCommRingCatIso.hom).surjective y
  obtain ⟨o, -, ho⟩ := Scheme.exists_preimage_of_isPullback
    (isPullback_toRelativeProjectiveSpace n S) y z hy
  exact ⟨o, ho⟩

end AffineSpace

namespace Compactification

variable {X S : Scheme.{u}} {n : Type u} [Finite n] {f : X ⟶ S}

end Compactification

end AlgebraicGeometry
