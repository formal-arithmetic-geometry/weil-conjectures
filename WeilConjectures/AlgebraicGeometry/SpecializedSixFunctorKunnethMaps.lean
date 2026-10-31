/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.NativeSixFunctorKunnethMaps

/-!
# The sketch's binding to the shared product comparisons

Source: current blueprint sk-def-sf-kv-maps, order 3513, clauses (i)--(iv),
and its expanded def-sf-kv-maps, order 3514 (blueprint: sk-def-sf-kv-maps).
This is an abbreviation of the expanded definition's computed tuple, not a second
construction or a record of independently chosen comparison maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

namespace WeilConjectures

/-- Exactly the expanded definition's four computed maps for the fixed native datum S.
The admissible condensed coefficient ranges over A_{E,n}, O_E, E and Qbar; both the
constructible adjunctions and every component map are those of the shared definition.
Source: sk-def-sf-kv-maps (i)--(iv) (blueprint: sk-def-sf-kv-maps). -/
abbrev specializedSixFunctorKunnethMaps (Λ : ScalarSixRing.{u})
    (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime] (hne : ringChar D.k ≠ ell)
    (hΛ : IsLocalizingAdmissibleCoefficient ell Λ.X)
    (S : ∀ {X Y : SepFinType D.k} (f : X ⟶ Y) (c : Compactification f.hom.left),
      SixOperationsLocalizingAdjunction Λ.X c) :=
  ProductComparisons.maps Λ D ell hne hΛ S

end WeilConjectures
