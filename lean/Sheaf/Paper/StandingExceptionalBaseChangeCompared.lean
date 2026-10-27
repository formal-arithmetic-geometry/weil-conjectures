/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q153
-/
module

public import Sheaf.Paper.CohomologicalSmoothnessFiniteComparison
public import WeilConjectures.Compactification.BaseChange

/-! # The standing exceptional base-change mate in comparison coordinates

Source: main-20261015, sec-smooth-purity/sk-prop-sp-purity-bc/pur9-cs-def-bc.md,
the displayed counit transpose (blueprint: pur9-cs-def-bc).

On a retained etale origin K, the specified constructible Hom bijection transports
exactly the etale counit mate. Both compactifications are retained,
including the base-changed choice
used by the item.
The maps below are its comparison-coordinate components, with the canonical source
and target comparison isomorphisms understood as in def-pur-co-smoothness. There is
no ambient pro-etale exceptional-adjunction assumption. Every bounded constructible
input has an etale origin; naturality makes these components independent of that origin.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.ProEtale

/-- The counit mate on a retained etale origin, transported by the specified comparison.
The underlying etale map is mateEquiv of the inverse compact-support exchange, whose
proper and open factors are the prescribed compactification exchanges. The constructible
Hom-chain carries this very mate to the standing exceptional base-change map. The source
and target are written in comparison coordinates, as for the recorded theta and beta.
No invertibility of this mate is used.
Source: main-20261015, pur9-cs-def-bc, defining displayed transpose
(blueprint: pur9-cs-def-bc). -/
noncomputable def standingExceptionalBaseChangeCompared
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g' : X' ⟶ X} {g : Y' ⟶ Y} [QuasiCompact f']
    (sq : IsPullback g' f' f g) (c : Compactification f) (c' : Compactification f')
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology
      (ModuleCat.{u + 1} P.Coefficient))) :=
  letI := c.hasCompactification
  letI := c'.hasCompactification
  (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X').mapDerivedCategory.map
    ((Etale.rightDerivedUpperShriekBaseChangeMap P.Coefficient sq).app K)

end AlgebraicGeometry.ProEtale
