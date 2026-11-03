/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
public import WeilConjectures.NumberTheory.Padics.IntegersProfiniteTower
public import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteConstantRepresentable
public import Mathlib.CategoryTheory.Monoidal.Internal.Limits

/-! # The actual limit of the condensed integral quotient rings

Source: current blueprint, integral coefficient limit, clauses 1--3
(blueprint: det-prop-sfb-qlbar-colimit-x-integral-limit).
The limit is constructed in ring objects. Its comparison from the pulled-back
continuous integers is the limit lift of the specified quotient cone.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedIntegralLimit

attribute [local irreducible] upperStarFromPoint
attribute [local instance] AdicCompletion.ringMonoidalObject AdicCompletion.ringCommutative
  AdicCompletion.finiteRingMonoidalObject AdicCompletion.finiteRingCommutative

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})

/-- The positive quotient tower in ring objects, indexed by exponent n+1.
Source: integral coefficient limit, clause 3
(blueprint: det-prop-sfb-qlbar-colimit-x-integral-limit). -/
def quotientTower : ℕᵒᵖ ⥤ Mon (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) :=
  Functor.ofOpSequence (X := fun n ↦ Mon.mk (AdicCompletion.finiteRing l E X n))
    (fun n ↦ ⟨AdicCompletion.transition l E X n⟩)

/-- The actual categorical inverse limit of the finite coefficient rings.
Source: integral coefficient limit, clause 3
(blueprint: det-prop-sfb-qlbar-colimit-x-integral-limit). -/
abbrev limitRing := limit (quotientTower l E X)

/-- The integers with their canonical profinite topology.
Source: integral coefficient limit, clause 1
(blueprint: det-prop-sfb-qlbar-colimit-x-integral-limit). -/
def integersProfinite : Profinite.{u} :=
  letI := Padic.coefficientExtensionIntegersTopology l E
  letI := (Padic.coefficientExtension_integers_profinite_tower.{u, u} l E).2.1
  letI := (Padic.coefficientExtension_integers_profinite_tower.{u, u} l E).2.2.1
  letI := (Padic.coefficientExtension_integers_profinite_tower.{u, u} l E).2.2.2.1
  Profinite.of (Padic.coefficientExtensionIntegers l E)

end AlgebraicGeometry.ProEtale.CondensedIntegralLimit
