/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Sheaf.Paper.SfExchanges
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat

/-!
# Small-etale component of the exchange and projection transformations

Source: Weil blueprint main-20261015, sec-six-functors-basics,
`sk-def-sf-exchanges/_section.md`, order 1701 (blueprint: sk-def-sf-exchanges).

All previously recorded exchange maps are re-exported unchanged. The finite projection
in that module uses intrinsic pro-etale modules. This interface also exposes the
canonical small-etale projection used by the finite-coefficient theorem. It is exactly
the published proper-counit/open-extension composite, as a natural transformation of
bifunctors, without any choice of an isomorphism. The finite theorem states that its
endpoints are bounded below and its component is invertible on the specified domain.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- The small-etale projection transformation, natural in both arguments. This is the
existing canonical composite of proper direct-image projection, the inverse canonical
open-extension tensor comparison and pullback composition. Its bounded constructible /
finite-Tor domain is used in sk-thm-sf-pf-finite; bounded-below membership of its endpoints
is asserted there. The previously supplied exchange maps remain imported unchanged.
Source: blueprint main-20261015, order 1701, projection display
(blueprint: sk-def-sf-exchanges). -/
def sfEtaleProjection (Λ : Type (u + 1)) [CommRing Λ]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    derivedTensorRightDerivedLowerShriek (ModuleCat.{u + 1} Λ) c ⟶
      rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar (ModuleCat.{u + 1} Λ) c :=
  projectionMapOfCompactification (ModuleCat.{u + 1} Λ) c

end AlgebraicGeometry.Etale
