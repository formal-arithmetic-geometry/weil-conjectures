/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NY
-/
module

public import Sheaf.AlgebraicGeometry.SmallSingularLocusPair
public import Sheaf.AlgebraicGeometry.RegularSchemeMorphism
public import Sheaf.AlgebraicGeometry.OrdinaryResolutionRule
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module

/-! # Resolution rules for pairs with small singular locus

Source: Temkin, Non-embedded Desingularization, §3.4.2 and Theorem 3.4.1,
printed pp.25–26 (blueprint: def-per-small-singular-locus-resolution-rule).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- One assignment on all small-singular-locus pairs, compatible with regular pullback
and deletion of exactly empty centers. The existing ordinary comparison records the
cartesian squares, the extended ideals, and the order of every retained center, including
nonempty centers whose blowup happens to be an isomorphism. There is no assertion that
the assigned tower is independent of the divisor. The regular-resolution predicate
includes nonemptiness, nowhere density, regular centers and a regular terminal level.
Source: Temkin §3.4.2, Theorem 3.4.1 and Remark 3.4.2(i)
(blueprint: def-per-small-singular-locus-resolution-rule). -/
structure SmallSingularLocusResolutionRule where
  tower : ∀ P : SmallSingularLocusPair.{u}, OrdinaryBlowupTower P.scheme
  resolves : ∀ P, (tower P).IsRegularResolution
  coherent : ∀ (P : SmallSingularLocusPair.{u}) (i : Fin (tower P).length),
    RingedSpace.IsCoherent ((tower P).level i.castSucc).toRingedSpace
      ((tower P).center i).toModules
  singularSupport : ∀ (P : SmallSingularLocusPair.{u}) (i : Fin (tower P).length)
    (z : ((tower P).center i).subscheme),
    ¬ IsRegularLocalRing (P.scheme.presheaf.stalk
      ((tower P).toBase i.castSucc (((tower P).center i).subschemeι z)))
  comparison : ∀ (P Q : SmallSingularLocusPair.{u}) (f : Q.scheme ⟶ P.scheme),
    IsRegularSchemeMorphism f → Q.divisor = P.divisor.comap f →
    Nonempty (OrdinaryResolutionComparison f (tower P) (tower Q))
  empty_length : ∀ P : SmallSingularLocusPair.{u}, IsEmpty P.scheme → (tower P).length = 0

end AlgebraicGeometry
