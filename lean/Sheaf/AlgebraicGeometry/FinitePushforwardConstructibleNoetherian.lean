/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Finite pushforward preserves constructibility over a Noetherian scheme

Source: smooth purity blueprint, unit `sk-prop-sf-cbc`, order 1579;
Stacks Project, Lemma 59.73.9 (Tag 095R)
(blueprint: lem-weil-pbc-finite-pushforward-constructible-noetherian).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- The direct image of a constructible abelian etale sheaf along a finite morphism
with Noetherian target is constructible. Constructibility is that of the underlying
set sheaf, with finite geometric stalks on constructible locally closed strata.

Source: smooth purity blueprint, unit `sk-prop-sf-cbc`, order 1579;
Stacks Project, Tag 095R
(blueprint: lem-weil-pbc-finite-pushforward-constructible-noetherian).

Proof, following the node's three steps:
1. For each closed subset T of U give T its reduced scheme structure and form V_T.
   Pullback of E to V_T and its opens is constructible by `prop-constructible-pullback`.
   V is Noetherian since it is finite over U; locally closed subsets of these Noetherian
   schemes are constructible (`def-weil-constructible-subset`, Stacks 005L), so the
   pullback statement's stratification notion agrees with the notion here. Finite
   exchange (`lemma-weil-pbc-finite-exchange`) identifies the restriction of h_*E to T
   with the finite direct image from V_T.
2. Use Noetherian induction on closed subsets T. The empty subset is immediate.
   For reducible T use its finitely many irreducible components
   (`lem-weil-pbc-noetherian-finite-components`), each a proper closed subset. Restrict
   their inductively obtained partitions to T_i minus the union of earlier components;
   these pieces remain locally closed, are disjoint, and cover T.
3. For irreducible T its reduced structure is integral. Choose a nonempty affine open Q
   and apply `lem-weil-pbc-finite-pushforward-generic-constructible` to V_Q over Q to
   obtain a dense open on which the direct image is lisse. Apply induction to its proper
   closed complement and adjoin this open. For T = U_red, compose the resulting strata
   with U_red to U: they partition U and are constructible by Noetherianity
   (`def-weil-constructible-subset`, Stacks 005L). No bound on Krull dimension is needed. -/
theorem isConstructibleEtaleSheafOfSets_lowerStar_of_isNoetherian
    {U V : Scheme.{u}} [IsNoetherian U] (h : V ⟶ U) [IsFinite h]
    (E : Sheaf V.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hE : IsConstructibleEtaleSheafOfSets
      ((sheafCompose V.smallEtaleTopology
        (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj E)) :
    IsConstructibleEtaleSheafOfSets
      ((sheafCompose U.smallEtaleTopology
        (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
          ((Etale.lowerStar AddCommGrpCat.{u + 1} h).obj E)) := by
  sorry

end AlgebraicGeometry.Scheme
