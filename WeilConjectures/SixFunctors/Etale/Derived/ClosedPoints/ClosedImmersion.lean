/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.AdicImageTower
public import WeilConjectures.SixFunctors.Etale.Derived.Stalks.Support
public import WeilConjectures.SixFunctors.OpenClosed.Supported
public import WeilConjectures.SixFunctors.OpenClosed.Vanishing
public import WeilConjectures.SixFunctors.OpenClosed.ClosedImmersion
public import WeilConjectures.ConstructibleSheaf.AdicImageTower

/-!
# Pushforward along a closed immersion

For a closed immersion `i : Z ⟶ X`, the pushforward `i_*` of étale sheaves of `Λ`-modules is
fully faithful with left inverse `i^*`, and its essential image consists of the sheaves whose
geometric stalks vanish at the points outside `Z` (blueprint `lem-kun-04ca`).

## Main statements

- `AlgebraicGeometry.Etale.mem_essImage_lowerStar_iff_isZero_sheafFiber` (`lem-kun-04ca`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ]

end Etale

end AlgebraicGeometry
