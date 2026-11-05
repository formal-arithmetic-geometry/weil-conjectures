/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingSupplement

/-!
# Functoriality of continuous-map condensed rings

Source: blueprint `sec-proetale-coefficients/sk-def-sfb-condensed-ring/`
`def-sfb-continuous-map-condensed-ring-map.md` and its proof
(blueprint: def-sfb-continuous-map-condensed-ring-map).

Postcomposition on the recorded universe-polymorphic continuous-map sheaves.
The coefficient rings lie in an arbitrary common universe, independent of the
universe of the profinite sets. The underlying ring objects and their tensor are
exactly those of `def-sfb-continuous-map-condensed-ring`.
-/

@[expose] public section

universe u v

open CategoryTheory Opposite

namespace Profinite

variable {T T' : Type v} [TopologicalSpace T] [Ring T] [IsTopologicalRing T]
  [TopologicalSpace T'] [Ring T'] [IsTopologicalRing T']
  (φ : T →+* T') (hφ : Continuous φ)

end Profinite
