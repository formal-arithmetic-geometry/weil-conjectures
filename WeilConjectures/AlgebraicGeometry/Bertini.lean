/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.GeometricFrobenius

/-!
# Curves through prescribed points preserving a finite étale cover

Let `X₀` be a smooth geometrically connected affine scheme of dimension `d ≥ 2` over a finite
field `k₀`, with geometric fiber `X = X₀ ×_{k₀} k̄`, let `T ⟶ X` be a connected finite étale
cover and `S` a nonempty finite set of `k̄`-points of `X`. A Bertini argument produces a smooth
connected closed affine curve `C ⊆ X` through `S` over which `T` stays connected; the curve is
defined over a finite extension of `k₀`, that is, it is stable under a power of the geometric
Galois Frobenius of `X`.

## Main statements

- `AlgebraicGeometry.Scheme.Hom.exists_isClosedImmersion_connectedSpace_pullback`: blueprint
  `lem-zl-bertini-finite-cover-curve`.

## Implementation notes

The blueprint lemma is stated over an arbitrary algebraically closed field `k`, with a
complement on descent when `k = 𝔽̄_q`. Only the case `k = 𝔽̄_q` is used, and it is stated here
directly for the geometric fiber of a scheme `X₀` over `𝔽_q`: "defined over a finite extension
`𝔽_{qᵐ}`" is rendered as stability of `C` under the `m`-th power of the geometric Galois Frobenius
`𝟙 × σ` of `X`, an automorphism `φ` of `C` with `φ ≫ i = i ≫ (𝟙 × σ)ᵐ`; by Galois descent, this
is the same as a model of `C ⟶ X` over `𝔽_{qᵐ}`. Dimensions are relative dimensions of smooth
morphisms.

## References

- [Stacks Project, Tags 0FD5, 0FD6 and 0G4F](https://stacks.math.columbia.edu/tag/0FD5), the
  Bertini theorems the proof uses.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Hom

/-- **Curves through prescribed points preserving a finite cover**
(blueprint: `lem-zl-bertini-finite-cover-curve`). Let `f : X₀ ⟶ Spec k₀` be a smooth
geometrically connected affine scheme of relative dimension `d ≥ 2` over a finite field, with
geometric fiber `X`, let `π : T ⟶ X` be a finite étale morphism with `T` connected, and let `S`
be a nonempty finite set of `k̄`-points of `X`. There is a closed immersion `i : C ⟶ X` of a
smooth connected affine curve over `k̄` through every point of `S`, such that `T ×_X C` is
connected and `C` is stable under some power `(𝟙 × σ)ᵐ`, `m ≥ 1`, of the geometric Galois
Frobenius of `X`. -/
theorem exists_isClosedImmersion_connectedSpace_pullback {k₀ : Type u} [Field k₀] [Finite k₀]
    {X₀ : Scheme.{u}} (f : X₀ ⟶ Spec (.of k₀)) [IsAffine X₀] {d : ℕ} (hd : 2 ≤ d)
    [SmoothOfRelativeDimension d f] [GeometricallyConnected f] {T : Scheme.{u}}
    (π : T ⟶ f.geometricFiber) [IsFinite π] [Etale π] [ConnectedSpace T]
    (S : Finset (Spec (.of (AlgebraicClosure k₀)) ⟶ f.geometricFiber)) (hS : S.Nonempty)
    (hS' : ∀ s ∈ S, s ≫ f.geometricFiberToAlgebraicClosure = 𝟙 _) :
    ∃ (C : Scheme.{u}) (i : C ⟶ f.geometricFiber), IsClosedImmersion i ∧ IsAffine C ∧
      SmoothOfRelativeDimension 1 (i ≫ f.geometricFiberToAlgebraicClosure) ∧
      ConnectedSpace C ∧ (∀ s ∈ S, ∃ c, c ≫ i = s) ∧ ConnectedSpace ↑(pullback π i) ∧
      ∃ m : ℕ, 0 < m ∧ ∃ φ : C ≅ C, φ.hom ≫ i = i ≫ (f.geometricGaloisFrobenius ^ m).hom :=
  sorry

end AlgebraicGeometry.Scheme.Hom
