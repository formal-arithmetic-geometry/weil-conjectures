/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.DirectImageTorAmplitude
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Ordinary

/-!
# Direct images along morphisms of finite cohomological dimension

Let `f : X ⟶ Y` be a quasi-compact quasi-separated morphism of schemes and `Λ` a ring, and assume
that `f` has cohomological dimension at most `d` for sheaves of `Λ`-modules: `Rᵠf_* F = 0` for
every étale sheaf `F` of `Λ`-modules on `X` and every `q > d`. This file proves:

* the scalar projection formula: for every `E ∈ D(X_ét, Λ)` and every complex `C` of
  `Λ`-modules, the projection map `Rf_* E ⊗ᴸ C_Y ⟶ Rf_*(E ⊗ᴸ C_X)` is an isomorphism
  (`AlgebraicGeometry.Etale.isIso_rightDerivedLowerStarProjectionMap_app_app_constantFunctor_obj`).
  Both sides are triangulated in `C` and commute with direct sums (`Rf_*` does, by the finite
  cohomological dimension, `lem-kun-0f11`), and the map is an isomorphism for `C = Λ`, which
  generates `D(Λ)`;
* for a finite ring `Λ`, `Rf_*` moves Tor amplitude from `[a, b]` to `[a, b + d]`
  (`AlgebraicGeometry.Etale.torAmplitudeIn_rightDerivedLowerStar_of_cohomologicalDimension`), by
  the residue test.

These are parts (1) and (2) of blueprint `det-cor-sf-direct-image-ctf-open-tor`, where `f` is an
open immersion of schemes of finite type over a separably closed field (so that its
cohomological dimension is finite, `lem-kun-0f10`). Part (3), on the pro-étale site, is in
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Stability`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme _root_.AlgebraicGeometry.Etale.DerivedCategory

variable (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
  [QuasiSeparated f] (d : ℕ)
  (hd : ∀ (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ), d < q →
    IsZero ((((f)_*[ModuleCat.{u + 1} Λ]).rightDerived q).obj F))

include hd

end AlgebraicGeometry.Etale
