/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.CurrentSixFunctorDatum
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.RelativeMap

/-! # Canonical current projection transformation

Source: `WeilConjectures/SixFunctors/Etale/Derived/Kunneth/RelativeMap.lean`
(blueprint: def-sf-current-pf).

The current projection formula is the published finite-coefficient projection isomorphism.  This
module introduces no replacement map or choice of isomorphism.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace WeilConjectures

/-- The canonical finite-coefficient projection isomorphism at two objects.
Source: `WeilConjectures/SixFunctors/Etale/Derived/Kunneth/RelativeMap.lean`
(blueprint: def-sf-current-pf). -/
noncomputable def currentProjectionFormula
    {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (K : CurrentDerived Λ X) (L : CurrentDerived Λ Y) :
    ((currentTensor Y).obj ((currentShriek f).obj K)).obj L ≅
      (currentShriek f).obj (((currentTensor X).obj K).obj ((currentPull f).obj L)) :=
  AlgebraicGeometry.Etale.projectionIsoApp Λ f K L

end WeilConjectures
