/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.GeometricFrobenius
public import WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance

/-!
# Weil equivariance of the smooth trace on a geometric fibre

Let `X₀` be a smooth separated scheme of finite type and relative dimension `d` over a finite field
`k₀ = 𝔽_q`, `a : X ⟶ Spec k̄` its geometric fibre and `σ` the geometric Frobenius of `Spec k̄`, so
that the geometric Galois Frobenius `g` of `X` fits in the cartesian square `g ≫ a = a ≫ σ`
(`AlgebraicGeometry.Scheme.Hom.isPullback_geometricGaloisFrobenius`). Smooth purity and the smooth
trace are Weil equivariant (blueprint `thm-pur-weil-equivariance-of-purity-and-trace` of the
six-functor section, for the Tate datum of `def-pur-tate-datum`, on which geometric Frobenius acts
by `q⁻ᵈ` on `Λ(d)`). This file records that statement, in the untwisted form in which the
Frobenius files use it
(`AlgebraicGeometry.Etale.TateOrientation.untwistedDegreewisePoincarePairing_frobeniusOperator`):
there are a Tate orientation `γ` of `a` and a Weil datum `τ` on `Λ_{k̄}(-d)`, on whose sections
Frobenius acts by `q^d`, for which the untwisted smooth trace `(Ra_! Λ_X)[2d] ⟶ Λ_{k̄}(-d)` is a
morphism of Weil objects.

The repository has smooth purity only as the existence of an orientation
(`AlgebraicGeometry.Etale.nonempty_iso_dualizingComplex_twistShift`) and no Weil datum on the Tate
twists, so the statement is existential. It is a node of another section and is stated here with
`sorry`.
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {X₀ : Scheme.{u}} (f : X₀ ⟶ Spec (.of k₀)) (d : ℕ)
  [SmoothOfRelativeDimension d f] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasTateTwist Λ]
  [HasInvertibleExponent Λ (Spec (.of (AlgebraicClosure k₀)))]
  [HasInvertibleExponent Λ f.geometricFiber]
  [HasCompactification f.geometricFiberToAlgebraicClosure]

/-- Blueprint `thm-pur-weil-equivariance-of-purity-and-trace` (Weil equivariance of purity and
trace, with the Tate datum `def-pur-tate-datum`), for the geometric fibre `a : X ⟶ Spec k̄` of a
smooth separated `𝔽_q`-scheme of finite type and relative dimension `d`, in untwisted form: there
are a Tate orientation `γ` of `a` and a Weil datum `τ` on `Λ_{k̄}(-d)` for the geometric Frobenius
of `Spec k̄`, on whose sections Frobenius acts by `q^d`, such that the untwisted smooth trace of `γ`
is a morphism of Weil objects from the datum induced by the canonical datum of `Λ_X` (through
`Ra_!` and the shift by `2d`) to `τ`. -/
theorem exists_tateOrientation_isWeilMorphism_untwistedSmoothTrace :
    ∃ (γ : TateOrientation Λ f.geometricFiberToAlgebraicClosure d)
      (τ : (L(((specGeometricFrobenius k₀).hom)^*[ModuleCat.{u + 1} Λ])).obj
          (tateObject Λ (Spec (.of (AlgebraicClosure k₀))) (-d)) ⟶
        tateObject Λ (Spec (.of (AlgebraicClosure k₀))) (-d)),
      IsWeilMorphism (specGeometricFrobenius k₀).hom
          (shiftWeilDatum (specGeometricFrobenius k₀).hom
            (lowerShriekWeilDatum f.isPullback_geometricGaloisFrobenius
              (leftDerivedUpperStarUnitIso _ f.geometricGaloisFrobenius.hom).hom) (2 * d))
          τ γ.untwistedSmoothTrace ∧
        ∀ z, frobeniusOperator (specGeometricFrobenius k₀).hom τ z = ((Nat.card k₀ : Λ) ^ d) • z :=
  sorry

end AlgebraicGeometry.Etale
