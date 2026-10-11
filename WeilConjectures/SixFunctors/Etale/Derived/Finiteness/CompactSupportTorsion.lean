/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.CompactSupport

/-!
# Compactly supported cohomology of torsion complexes is perfect

The finite stage of `sk-prop-sf-trace-perfectness` for a complex of sheaves of modules over a
Noetherian ring `Λ` which is killed by an integer `N` invertible on the base. This is the form in
which the finite stages `A_{E,n} = 𝒪_E/𝔪_Eⁿ` occur at the integral stage `Λ = 𝒪_E`: an object of
`D(X_ét, A_{E,n})` is recorded through its restriction of scalars to `𝒪_E`, as in
`AlgebraicGeometry.Etale.DerivedCategory.boundedConstructibleIntegral`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale

open Scheme

/-- Blueprint `sk-prop-sf-trace-perfectness`: Perfectness of compact cohomology and of
geometric stalks.

**Compactly supported cohomology of a torsion complex is perfect.** Let `Λ` be a Noetherian ring,
`k` a separably closed field, `X` separated of finite type over `k`, and `K` a bounded
constructible complex of sheaves of `Λ`-modules on `X_ét` of finite Tor amplitude, killed by an
integer `N` invertible in `k`. Then `RΓ_c(X, K)` is a perfect complex of `Λ`-modules: it is
bounded, with finitely generated cohomology modules, and of finite Tor amplitude.

This is the finite stage of the blueprint (the coefficient ring there is `Λ / N`, through whose
restriction of scalars `K` is recorded); compare
`AlgebraicGeometry.Etale.isPerfect_compactlySupportedGlobalSections` for a finite `Λ`. -/
theorem isPerfect_compactlySupportedGlobalSections_of_nsmul_eq_zero (Λ : Type (u + 1))
    [CommRing Λ] [IsNoetherianRing Λ] {k : Type u} [Field k] [IsSepClosed k] {X : Scheme.{u}}
    (aX : X ⟶ Spec (.of k)) [IsSeparated aX] [LocallyOfFiniteType aX] [HasCompactification aX]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (N : ℕ) [NeZero N] (hN : N • 𝟙 K = 0) (hNk : IsUnit (N : Γ(Spec (.of k), ⊤)))
    (hK : DerivedCategory.boundedConstructibleFiniteTor Λ X K) :
    ((compactlySupportedGlobalSections (ModuleCat.{u + 1} Λ) aX).obj K).IsPerfect :=
  sorry

end AlgebraicGeometry.Etale
