/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.SchemeGaloisComparison

/-!
# Frobenius correspondences

Let `X₀` be a scheme over a finite field `k`, with geometric fibre `X = X₀ ×_k k̄` and scheme
Frobenius `Φ_X` (`AlgebraicGeometry.Scheme.Hom.geometricFiberFrobenius`), the base change of the
`q`-power Frobenius of `X₀`. A *Frobenius correspondence* on `K ∈ Dctf(X, Λ)` is a morphism
`ψ : LΦ_X^* K ⟶ K`, not necessarily invertible
(`AlgebraicGeometry.Etale.FrobeniusCorrespondence`). Its iterates and its operators are
`AlgebraicGeometry.Etale.weilDatumIterate` and `AlgebraicGeometry.Etale.frobeniusCompactOperator`.
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ]
  {k : Type u} [Field k] [Finite k] {X₀ : Scheme.{u}} (f : X₀ ⟶ Spec (.of k))

/-- A *Frobenius correspondence* on `K ∈ Dctf(X, Λ)`, for the geometric fibre `X = X₀ ×_k k̄` of
a scheme over a finite field and the base change `Φ_X` of the `q`-power Frobenius of `X₀`
(`AlgebraicGeometry.Scheme.Hom.geometricFiberFrobenius`), is a morphism
`ψ : LΦ_X^* K ⟶ K` of `D(X_ét, Λ)`, not necessarily invertible. -/
abbrev FrobeniusCorrespondence
    (K : DerivedCategoryFiniteTor (ModuleCat.{u + 1} Λ) f.geometricFiber) : Type (u + 1) :=
  (L((f.geometricFiberFrobenius)^*[ModuleCat.{u + 1} Λ])).obj
      ((DerivedCategoryFiniteTor.ι _ _).obj K) ⟶ (DerivedCategoryFiniteTor.ι _ _).obj K

end AlgebraicGeometry.Etale
