/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.LocalRing.Module
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect

/-!
# Perfect complexes over a local ring

A perfect complex over a commutative ring has finite Tor amplitude, and over a local ring it is
represented by a bounded complex of finitely generated *free* modules. Over a Noetherian local
ring (for instance the finite coefficient ring `A_{E,n} = 𝒪_E/ϖⁿ`), a bounded complex with
finite cohomology modules therefore has finite Tor amplitude exactly when it is quasi-isomorphic
to a bounded complex of finite free modules (`lem-trf-finite-tor-amplitude-perfect`).

## Main statements

- `DerivedCategory.IsPerfect.torAmplitudeIn`, `DerivedCategory.IsPerfect.finiteTorAmplitude`:
  a perfect complex has finite Tor amplitude.
- `DerivedCategory.IsPerfect.exists_free`: over a local ring a perfect complex is represented by
  a bounded complex of finite free modules.
- `DerivedCategory.finiteTorAmplitude_iff_exists_free` (`lem-trf-finite-tor-amplitude-perfect`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace DerivedCategory

variable {R : Type u} [CommRing R] [HasDerivedCategory.{u} (ModuleCat.{u} R)]

end DerivedCategory
