/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NY
-/
module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible
public import Sheaf.RingTheory.ExcellentRing
public import Sheaf.AlgebraicGeometry.IsRegularScheme

/-! # Pairs with small singular locus

Source: Temkin, Non-embedded Desingularization, §3.4.2, printed pp.25–26
(blueprint: def-per-small-singular-locus-pair).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- An object of Temkin's small-singular-locus pair category, on reduced schemes.
The divisor presentation is a proposition, not a chosen field or decomposition on which
an assignment could depend. `IsField` on a bundled commutative ring means a field without
requiring a separately chosen field structure. The finite coproduct includes `n = 0`.
Source: Temkin §3.4.2 (blueprint: def-per-small-singular-locus-pair). -/
structure SmallSingularLocusPair where
  scheme : Scheme.{u}
  structureMap : scheme ⟶ Spec (.of (ULift.{u} ℚ))
  reduced : IsReduced scheme
  noetherian : IsNoetherian scheme
  quasiExcellent : ∀ U : scheme.affineOpens, IsQuasiExcellent Γ(scheme, U.1)
  divisor : scheme.IdealSheafData
  cartier : divisor.IsInvertible
  singularSupport : ∀ x : scheme,
    ¬ IsRegularLocalRing (scheme.presheaf.stalk x) → x ∈ divisor.support
  divisorPresentation : ∃ (n : ℕ) (V : Fin n → Scheme.{u}) (K : Fin n → CommRingCat.{u})
    (s : ∀ i, V i ⟶ Spec (K i)),
    (∀ i, IsField (K i) ∧ CharZero (K i) ∧ LocallyOfFiniteType (s i) ∧
      QuasiCompact (s i)) ∧ Nonempty (divisor.subscheme ≅ ∐ V)

end AlgebraicGeometry
