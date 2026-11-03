/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.GeometricFrobenius
public import WeilConjectures.SixFunctors.Etale.Derived.VerdierDualWeil

/-!
# Frobenius equivariance of the smooth orientation of a geometric fibre

Let `X₀` be a smooth separated scheme of finite type and relative dimension `d` over a finite
field `k₀ = 𝔽_q`, `a : X ⟶ Spec k̄` its geometric fibre, `σ` the geometric Frobenius of `Spec k̄`
and `g` the geometric Galois Frobenius of `X`, so that `g ≫ a = a ≫ σ` is cartesian
(`AlgebraicGeometry.Scheme.Hom.isPullback_geometricGaloisFrobenius`). The dualizing complex
`ω = Ra^! Λ` carries the exceptional Weil datum of the square
(`AlgebraicGeometry.Etale.upperShriekMateWeilDatum`), and smooth purity identifies it with
`Λ_X(d)[2d]`, on which geometric Frobenius acts through the Tate datum by `q⁻ᵈ`
(`def-pur-tate-datum`). Over `k̄` the twist is trivial, so the statement can be written without
Tate twists: there is an isomorphism `o : Λ_X[2d] ≅ ω` which is a morphism of Weil objects from
the canonical datum of `Λ_X[2d]` to `q^d` times the exceptional datum.

This is the Frobenius case of the compatibility of the canonical purity isomorphism with base
change (blueprint `sk-prop-sp-purity-bc`, `thm-pur-smooth-base-change-coherence`), at the unit
and read through the normalization of the Tate datum. The library has smooth purity only as the
existence of an orientation (`AlgebraicGeometry.Etale.nonempty_iso_dualizingComplex_twistShift`)
and the canonical orientation (`AlgebraicGeometry.Etale.dualizingComplexTwistShiftIso`) without
its base change compatibility, so the statement is recorded here with `sorry`; it is the input
of `AlgebraicGeometry.Etale.exists_tateOrientation_isWeilMorphism_untwistedSmoothTrace`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {X₀ : Scheme.{u}} (f : X₀ ⟶ Spec (.of k₀)) (d : ℕ)
  [SmoothOfRelativeDimension d f] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
  [HasInvertibleExponent Λ (Spec (.of (AlgebraicClosure k₀)))]
  [HasInvertibleExponent Λ f.geometricFiber]
  [HasCompactification f.geometricFiberToAlgebraicClosure]

/-- Blueprint `sk-prop-sp-purity-bc` (compatibility of purity with base change), for the
cartesian square `g ≫ a = a ≫ σ` of the geometric Galois Frobenius of the geometric fibre
`a : X ⟶ Spec k̄` of a smooth separated `𝔽_q`-scheme of finite type and relative dimension `d`,
at the unit and in untwisted form (with the Tate datum of `def-pur-tate-datum`, on which
geometric Frobenius acts by `q⁻ᵈ` on `Λ(d)`).

There is an isomorphism `o : Λ_X[2d] ≅ ω = Ra^! Λ_{k̄}` such that

`Lg^*(o) ≫ q^d • φ^! = φ_{Λ_X}[2d] ≫ o`,

where `φ_{Λ_X}` is the canonical datum `Lg^* Λ_X ≅ Λ_X` and `φ^!` is the exceptional datum
`Lg^* Ra^! Λ ⟶ Ra^! Lσ^* Λ ≅ Ra^! Λ` of the square
(`AlgebraicGeometry.Etale.upperShriekMateWeilDatum`). For the canonical orientation
`θ : Λ_X(d)[2d] ≅ ω` this is the base change compatibility of purity along the Frobenius square
(which makes `θ` a morphism of Weil objects for the Tate datum on `Λ_X(d)`), composed with a
trivialization `Λ_{k̄} ≅ Λ_{k̄}(d)` pulled back to `X`, on which the Tate datum is `q⁻ᵈ` times the
canonical one. Equivalently, geometric Frobenius acts by `q^d` on the compactly supported
cohomology `H^{2d}_c(X, Λ)` through the trace. -/
theorem exists_iso_dualizingComplex_isWeilMorphism :
    ∃ o : (𝟙_ (DerivedCategoryModule Λ f.geometricFiber))⟦(2 * d : ℤ)⟧ ≅
        dualizingComplex Λ f.geometricFiberToAlgebraicClosure,
      IsWeilMorphism f.geometricGaloisFrobenius.hom
        (shiftWeilDatum f.geometricGaloisFrobenius.hom
          (leftDerivedUpperStarUnitIso _ f.geometricGaloisFrobenius.hom).hom (2 * d))
        (((Nat.card k₀ : Λ) ^ d) •
          upperShriekMateWeilDatum (Λ := Λ) f.isPullback_geometricGaloisFrobenius
            (leftDerivedUpperStarUnitIso _ (specGeometricFrobenius k₀).hom).hom)
        o.hom :=
  sorry

end AlgebraicGeometry.Etale
