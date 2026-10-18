/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q39
-/
module

public import WeilConjectures.AlgebraicGeometry.AbelianVariety.TateModule
public import WeilConjectures.Mathlib.FieldTheory.Finite.Basic
import Sheaf.FieldTheory.UniqueSubfieldOfClosure
import WeilConjectures.GroupTheory.TateModule
import WeilConjectures.NumberTheory.TateModule

/-!
# Frobenius-fixed vectors on the Tate modules of an abelian variety

Source: Weil conjectures blueprint, `sec-algebraic-groups-lie-algebras`, `sk-p-tate`,
`prop-av-tate-no-frobenius-fixed.md` and its proof, snapshot `main-20261015`
(blueprint: prop-av-tate-no-frobenius-fixed).
-/

@[expose] public section

universe u

open CategoryTheory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.IsAbelianVariety

/-- Arithmetic and geometric Frobenius have zero fixed submodules on both Tate modules.
The four conjuncts state, respectively, integral arithmetic, integral geometric, rational
arithmetic and rational geometric vanishing. The algebraic closure is the existing
`AlgebraicClosure k₀`, and the actions are the existing coordinatewise Galois actions.

Source: blueprint `sec-algebraic-groups-lie-algebras/sk-p-tate`, snapshot `main-20261015`,
`prop-av-tate-no-frobenius-fixed.md`
(blueprint: prop-av-tate-no-frobenius-fixed).

Proof plan, following the four steps of the node:
1. Apply `lem-weil-unique-subfield-of-closure` at degree one: the elements of the closure
   fixed by arithmetic Frobenius are exactly the image of the finite base field.
2. Cover the finite-type variety by finitely many affine charts. In each chart, geometric
   points are algebra maps to the closure. A Frobenius-fixed map corestricts uniquely to
   the base field. Its values on a finite generating set determine it, giving finitely
   many possibilities (`def-weil-affine-spectrum`).
3. Take the finite union of these chart sets. This identifies the fixed subgroup with
   the finite group of rational points. The coordinate action is a group automorphism.
4. Apply `lem-tate-module-no-fixed` to this finite fixed subgroup. For an integral fixed
   system, compatibility and the bounded orders in the finite subgroup kill every
   coordinate. For a rational fixed vector, clear a power-of-ℓ denominator and use the
   torsion-freeness of the integral Tate module. An automorphism and its inverse have
   the same fixed vectors, giving all four conclusions. -/
theorem frobenius_fixed_tateModules_eq_zero
    (k₀ : Type u) [Field k₀] [Fintype k₀]
    (p ℓ a : ℕ) [Fact p.Prime] [Fact ℓ.Prime] [CharP k₀ p]
    (ha : 1 ≤ a) (hcard : Fintype.card k₀ = p ^ a) (hℓp : ℓ ≠ p)
    (A₀ : Over (Spec (.of k₀))) [GrpObj A₀] [IsAbelianVariety A₀] :
    (∀ t : tateModule ℓ A₀,
      galoisRepresentation ℓ A₀
        (FiniteField.frobeniusAlgEquivOfAlgebraic k₀ (AlgebraicClosure k₀)) t = t → t = 0) ∧
    (∀ t : tateModule ℓ A₀,
      galoisRepresentation ℓ A₀
        (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic k₀ (AlgebraicClosure k₀)) t = t →
          t = 0) ∧
    (∀ v : rationalTateModule ℓ A₀,
      AddCommGroup.rationalTateModule.map
        (geometricPointsAddEquiv (A := A₀)
          (FiniteField.frobeniusAlgEquivOfAlgebraic k₀
            (AlgebraicClosure k₀))).toAddMonoidHom v = v → v = 0) ∧
    (∀ v : rationalTateModule ℓ A₀,
      AddCommGroup.rationalTateModule.map
        (geometricPointsAddEquiv (A := A₀)
          (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic k₀
            (AlgebraicClosure k₀))).toAddMonoidHom v = v → v = 0) := by
  sorry

end AlgebraicGeometry.IsAbelianVariety
