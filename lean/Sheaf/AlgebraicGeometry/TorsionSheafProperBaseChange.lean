/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK
-/
module

public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.SixFunctors.BaseChange.Derived
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
import WeilConjectures.AlgebraicGeometry.DerivedCategories

/-!
# Proper base change for torsion abelian sheaves

Source: blueprint sec-proper-base-change/sk-thm-properbasechange,
Detailed form of prop-weil-proet-finite-proper-base-change; Stacks Project, Tag 0DDE,
specialized to a sheaf in degree zero (blueprint: prop-weil-proet-finite-proper-base-change).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- Proper base change for a torsion abelian sheaf, placed in degree zero.
Source: blueprint sec-proper-base-change/sk-thm-properbasechange, Detailed form;
Stacks Project, Tag 0DDE (blueprint: prop-weil-proet-finite-proper-base-change).

Proof plan: Put `K = F[0]` using `DerivedCategory.Plus.singleFunctor`.
Its degree-zero cohomology is `F`, and its other cohomology sheaves are zero,
so it is bounded below with lower bound zero and has torsion cohomology:
`F` is torsion by hypothesis, and every section of the zero sheaf is killed by one
(def-weil-pbc-derived-categories, def-weil-pbc-etale-sheaves).
The chosen pullback identification makes the square Cartesian, and `f` is proper.
Apply thm-weil-pbc-bounded-below, namely `Etale.isIso_baseChange_of_isProper`,
to this square and `K`, with no restriction on `g`.
The morphism denoted by the exchange at `F` is by definition the component at `F[0]`
of `derivedBaseChangeMapPlus` (def-weil-pbc-derived-exchange); this is the same
canonical transformation as `Etale.baseChange`. Thus the resulting isomorphism is
precisely the asserted exchange morphism, not merely an isomorphism of its endpoints. -/
theorem isIso_derivedBaseChangeMapPlus_app_torsionSheaf_of_isProper
    {X' X Y' Y : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    [IsProper f] (sq : ChosenCartesianSquare g' f' f g)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (hF : F.IsTorsion) :
    IsIso ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq).app
      ((DerivedCategory.Plus.singleFunctor
        (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj F)) := by
  sorry

end AlgebraicGeometry.Etale
