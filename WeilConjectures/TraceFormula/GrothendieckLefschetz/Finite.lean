/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.GeometricFrobenius
public import WeilConjectures.SixFunctors.Etale.Derived.AdicFrobenius
public import WeilConjectures.SixFunctors.Etale.Derived.WeilComplex

/-!
# The Grothendieck–Lefschetz trace formula with finite coefficients

Let `X₀` be a separated scheme of finite type over a finite field `k = 𝔽_q`, with geometric
fibre `X = X₀ ×_k k̄`, geometric Galois Frobenius `g_X` (`Scheme.Hom.geometricGaloisFrobenius`)
over the geometric Frobenius `σ` of `Spec k̄`, and let `Λ` be a finite ring whose exponent is
invertible in `k̄`. For `K ∈ Dᵇctf(X, Λ)` and a Weil datum `φ : Lg_X^* K ⟶ K`, the global
Frobenius operator `F_{c,m} = F_c(φ^{[m]})` on `RΓ_c(X, K)` and the local Frobenius operators
`F_{x̄,m} = F_x̄(φ^{[m]})` on the stalks at the points `x̄ ∈ X(k̄)` fixed by `(g_X^m, σ^m)`, that is
at the points of `X₀(𝔽_{q^m})` (`Etale.globalOperator`, `Etale.localOperator`), satisfy
```
tr_Λ(F_{c,m} ∣ RΓ_c(X, K)) = ∑_{x̄} tr_Λ(F_{x̄,m} ∣ K_x̄)
```
for every `m ≥ 1`, the traces being categorical traces in `D(Λ)` for the Koszul braiding.

## Main statements

- `AlgebraicGeometry.Etale.trace_globalOperator_iterateWeilDatum_eq_finsum`: the formula for an
  arbitrary Weil datum `φ`, not necessarily invertible (stated with `sorry`).
- `AlgebraicGeometry.Etale.WeilComplex.trace_globalOperator_eq_finsum`: the formula for a strict
  Weil complex, blueprint `theorem-grothendieck-lefschetz-trace-formula--1`.

## Implementation notes

The fixed points are morphisms `x̄ : Spec k̄ ⟶ X` over `Spec k̄` with `σ^m ≫ x̄ = x̄ ≫ g_X^m`; they
correspond to the points of `X₀(𝔽_{q^m})`. There are finitely many of them, and the sum is a
`finsum`. The perfectness of `RΓ_c(X, K)` and of the stalks is given by right duals, as in
`AlgebraicGeometry.Etale.AdicSystem.FrobeniusSystem.exists_trace_eq_globalOperatorFamily`; the
traces do not depend on their choice.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

variable {k : Type u} [Field k] [Finite k] {X₀ : Scheme.{u}} (f : X₀ ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  [HasCompactification f.geometricFiberToAlgebraicClosure]
  (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
  [HasInvertibleExponent Λ (Spec (.of (AlgebraicClosure k)))]

/-- The points `x̄ ∈ X(k̄)` of the geometric fibre fixed by `(g_X^m, σ^m)`, that is
`σ^m ≫ x̄ = x̄ ≫ g_X^m`: the points of `X₀(𝔽_{q^m})`. -/
abbrev geometricFixedPoint (m : ℕ) : Type u :=
  {x : Spec (.of (AlgebraicClosure k)) ⟶ f.geometricFiber //
    x ≫ f.geometricFiberToAlgebraicClosure = 𝟙 _ ∧
      endIterate (specGeometricFrobenius k).hom m ≫ x =
        x ≫ endIterate f.geometricGaloisFrobenius.hom m}

attribute [local instance] DerivedCategory.braidedCategory'

/-- **The trace formula for Frobenius correspondences with finite coefficients** (blueprint
`theorem-trace-formula-frobenius-correspondence`, through the comparison `κ` of
`lemma-scheme-frobenius-geometric-frobenius`): for `K ∈ Dᵇctf(X, Λ)`, an arbitrary Weil datum
`φ : Lg_X^* K ⟶ K` and `m ≥ 1`,
`tr_Λ(F_c(φ^{[m]}) ∣ RΓ_c(X, K)) = ∑_{x̄ ∈ X₀(𝔽_{q^m})} tr_Λ(F_x̄(φ^{[m]}) ∣ K_x̄)`. -/
theorem trace_globalOperator_iterateWeilDatum_eq_finsum
    {K : DerivedCategory (Sheaf f.geometricFiber.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (_hK : DerivedCategory.boundedConstructibleFiniteTor Λ f.geometricFiber K)
    (φ : (L((f.geometricGaloisFrobenius.hom)^*[ModuleCat.{u + 1} Λ])).obj K ⟶ K)
    {m : ℕ} (_hm : m ≠ 0)
    [_hΓ : HasRightDual ((compactlySupportedGlobalSections (ModuleCat.{u + 1} Λ)
      f.geometricFiberToAlgebraicClosure).obj K)]
    [_hx : ∀ x : geometricFixedPoint f m,
      HasRightDual ((geometricStalk Λ x.1).obj K)] :
    trace (globalOperator Λ (isPullback_endIterate f.isPullback_geometricGaloisFrobenius m)
        (iterateWeilDatum Λ _ φ m)) =
      ∑ᶠ x : geometricFixedPoint f m,
        trace (localOperator Λ x.2.2 (iterateWeilDatum Λ _ φ m)) := by
  sorry

/-- **The Grothendieck–Lefschetz trace formula with finite coefficients** (blueprint
`theorem-grothendieck-lefschetz-trace-formula--1`): for a strict Weil complex `(K, φ)` of
`Dᵇctf(X, Λ)`, `Λ` finite with exponent invertible in `k̄`, and every `m ≥ 1`,
```
tr_Λ(Frob_{X,K}^m ∣ RΓ_c(X, K)) = ∑_{y ∈ X₀(𝔽_{q^m})} tr_Λ(Frob_{y,m} ∣ K_ȳ)
```
in `End (𝟙_ D(Λ)) = Λ`. -/
theorem WeilComplex.trace_globalOperator_eq_finsum
    (W : WeilComplex (ModuleCat.{u + 1} Λ) f.geometricGaloisFrobenius) {m : ℕ} (hm : m ≠ 0)
    [HasRightDual ((compactlySupportedGlobalSections (ModuleCat.{u + 1} Λ)
      f.geometricFiberToAlgebraicClosure).obj
      ((DerivedCategoryFiniteTor.ι (ModuleCat.{u + 1} Λ) f.geometricFiber).obj W.obj))]
    [∀ x : geometricFixedPoint f m,
      HasRightDual ((geometricStalk Λ x.1).obj
      ((DerivedCategoryFiniteTor.ι (ModuleCat.{u + 1} Λ) f.geometricFiber).obj W.obj))] :
    trace (globalOperator Λ (isPullback_endIterate f.isPullback_geometricGaloisFrobenius m)
        (iterateWeilDatum Λ _ W.frobenius.hom.hom m)) =
      ∑ᶠ x : geometricFixedPoint f m,
        trace (localOperator Λ x.2.2 (iterateWeilDatum Λ _ W.frobenius.hom.hom m)) :=
  trace_globalOperator_iterateWeilDatum_eq_finsum f Λ
    (K := (DerivedCategoryFiniteTor.ι _ _).obj W.obj) W.obj.property _ hm

end AlgebraicGeometry.Etale
