/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q08
-/
module

public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Algebra.Category.Grp.Abelian
import WeilConjectures.SixFunctors.Finite.BaseChange

/-!
# Underived étale base change for an open and closed immersion

Source: blueprint, sec-smooth-purity, sk-prop-sf-kunneth-ordinary,
node lem-kun-base-change-open-closed (blueprint: lem-kun-base-change-open-closed).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- Direct image along an open and closed immersion commutes with arbitrary base change,
for the canonical underived exchange and every abelian sheaf on the small étale site.
Source: blueprint, sec-smooth-purity, sk-prop-sf-kunneth-ordinary,
node lem-kun-base-change-open-closed (blueprint: lem-kun-base-change-open-closed).

Proof: A closed immersion is finite. The chosen pullback identification gives an
`IsPullback` square, so the finite exchange theorem makes the canonical base-change
natural transformation invertible. Its component at `F` is therefore invertible. -/
theorem isIso_baseChangeMap_app_of_isOpenImmersion_of_isClosedImmersion
    {U' U Y X : Scheme.{u}} (p : U' ⟶ U) (h : U' ⟶ Y) (j : U ⟶ X) (g : Y ⟶ X)
    [IsOpenImmersion j] [IsClosedImmersion j] (sq : ChosenCartesianSquare p h j g)
    (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    IsIso ((baseChangeMap AddCommGrpCat.{u + 1} sq.toCommSq).app F) := by
  have hsq := CategoryTheory.IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback
    sq.hom_fst sq.hom_snd
  have := isIso_baseChangeMap_of_isFinite AddCommGrpCat.{u + 1} hsq
  infer_instance

end AlgebraicGeometry.Etale
