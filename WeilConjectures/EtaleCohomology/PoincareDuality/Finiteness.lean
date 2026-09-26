/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.PoincareDuality.Perfect
public import WeilConjectures.EtaleCohomology.PoincareDuality.Setting

/-!

# Finiteness: the global sections are perfect at the point

The duality statements pair objects of the coefficient derived category against one another,
so they need to know that the cohomology of `X` is *perfect at the point*: bounded with
finite cohomology of finite Tor amplitude. This is the finiteness input of the
smooth-base-change chapter, assembled into the statement that for `K` in `D^b_ctf(X, Λ)` both
`RΓ_c(X, K)` and `RΓ(X, K)`, and the duals of both, are perfect point complexes.

## Main results

- `AlgebraicGeometry.ProEtale.isPerfectPointComplex_globalSections`.

-/

@[expose] public section

universe u

open CategoryTheory Abelian Limits MonoidalCategory Opposite

namespace AlgebraicGeometry

open Scheme ProEtale

namespace ProEtale

variable {Λ : Type (u + 1)} [CommRing Λ] {k₀ : Type u} [Field k₀] [Finite k₀] {d : ℕ}

/-- Blueprint `sk-lem-finite`: Finiteness: the global sections are perfect at the point.

For `K` in `D^b_ctf(X, Λ)`, the compactly supported global sections `RΓ_c(X, K)`, the ordinary
global sections `RΓ(X, K)` and the duals of both are perfect point complexes: bounded
complexes of finite projective `Λ`-modules. -/
theorem isPerfectPointComplex_globalSections (T : PoincareDualitySetting k₀ d)
    (k : Type u) [Field k] [IsAlgClosed k] [Algebra k₀ k]
    [HasCompactification (T.structureMorphism k)]
    (K : DerivedCategory
      (Sheaf (Scheme.ProEt.topology (T.geometricFibre k)) (ModuleCat.{u + 1} Λ)))
    (hK : boundedConstructibleFiniteTor (ModuleCat.{u + 1} Λ) (T.geometricFibre k) K) :
    IsPerfectPointComplex ((compactlySupportedGlobalSections (ModuleCat.{u + 1} Λ)
        (T.structureMorphism k)).obj K) ∧
      IsPerfectPointComplex ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ)
        (T.geometricFibre k)).obj K) ∧
      IsPerfectPointComplex ((ihom ((compactlySupportedGlobalSections
        (ModuleCat.{u + 1} Λ) (T.structureMorphism k)).obj K)).obj (𝟙_ _)) ∧
      IsPerfectPointComplex ((ihom ((rightDerivedGlobalSections
        (ModuleCat.{u + 1} Λ) (T.geometricFibre k)).obj K)).obj (𝟙_ _)) :=
  sorry

end ProEtale

end AlgebraicGeometry
