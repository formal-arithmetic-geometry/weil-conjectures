/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.FilteredColimitStabilization
public import WeilConjectures.SixFunctors.Etale.Derived.Stalks.Support
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk

/-!
# Deligne's approximation by a constructible subsheaf

Let `X` be a Noetherian scheme, `Λ` a finite ring and `F` an étale sheaf of `Λ`-modules on `X`.
Let `hᵢ : Wᵢ ⟶ X` be finitely many morphisms from Noetherian schemes such that the pullbacks
`hᵢ^* F` are constructible. Then `F` has a constructible subsheaf `F₀` such that the stalks of
`F / F₀` vanish at all the points in the images of the `hᵢ`
(`AlgebraicGeometry.Etale.exists_mono_isConstructibleSheaf_isZero_sheafFiber_cokernel`).

Write `F` as the filtered union of its constructible subsheaves `F_S` (Stacks 03SA,
`AlgebraicGeometry.Etale.finsetSectionImage`). Pullback commutes with colimits and preserves
monomorphisms, so `hᵢ^* F` is the filtered union of the `hᵢ^* F_S`; being constructible on the
Noetherian `Wᵢ`, it equals one of them
(`AlgebraicGeometry.Etale.exists_epi_ι_app_of_isConstructibleSheaf`). A common stage `F_S` for
the finitely many `i` has `hᵢ^* (F / F_S) = 0`, so the stalks of `F / F_S` vanish on the images.

This is the spreading step of Deligne's proof of the finiteness of nearby cycles (SGA 4½,
[Th. finitude], proof of 3.2): for the geometric generic fibres `hᵢ` of the coordinates of
`𝔸ⁿ`, every non-closed point is in the image of some `hᵢ`, so `F / F₀` is supported at closed
points.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]

end Etale

end AlgebraicGeometry
