/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Extension.Cotangent.Basic
import Mathlib.RingTheory.AlgebraicIndependent.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Cartier equality

Source: Stacks Project, More on Algebra, Lemma Tag 07E1 (blueprint:
lem-weil-pbc-cartier-equality).
-/

universe u v

open Algebra

/-! The theorem below is the Cartier dimension formula for a finitely generated
field extension. -/
/--
For a finitely generated field extension, the Kähler differentials and the first
homology of the naive cotangent complex are finite-dimensional, and their
dimensions differ by the transcendence degree (stated without truncated
subtraction, as `trdeg + dim H₁ = dim Ω` in `Cardinal`).  If the extension is finite,
the transcendence degree is zero, so the dimensions are equal.  More on
Algebra, Lemma 07E1 proves this as follows: choose a finite transcendence basis
and the complete-intersection presentation supplied by the cited model lemmas;
the naive cotangent complex is the Jacobian map between free modules by the
regular-sequence conormal and polynomial Kähler-basis lemmas.  Jacobi--Zariski
identifies its cokernel with Kähler differentials, while presentation
functoriality identifies its kernel with `Algebra.H1Cotangent`.  Localization
and exactness carry these identifications from the model to `K`.  Rank--nullity
then gives the dimension difference as `n - c`, which is the cardinality of the
chosen transcendence basis and hence `Algebra.trdeg`; for a finite extension the
empty basis gives zero and the two finite dimensions are equal.  These are the
steps recorded in the node proof (blueprint: lem-weil-pbc-cartier-equality).
(blueprint: lem-weil-pbc-cartier-equality)
-/
theorem cartier_equality
    (k K : Type*) [Field k] [Field K] [Algebra k K]
    [Algebra.FiniteType k K] :
    Module.Finite K (KaehlerDifferential k K) ∧
      Module.Finite K (Algebra.H1Cotangent k K) ∧
      Algebra.trdeg k K + Module.finrank K (Algebra.H1Cotangent k K) =
        Module.finrank K (KaehlerDifferential k K) ∧
      (FiniteDimensional k K →
        Module.finrank K (KaehlerDifferential k K) =
          Module.finrank K (Algebra.H1Cotangent k K)) := by
  sorry
