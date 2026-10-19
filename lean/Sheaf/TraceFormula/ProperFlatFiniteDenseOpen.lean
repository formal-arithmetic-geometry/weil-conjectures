/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N9
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Pullbacks
import Sheaf.AlgebraicGeometry.LocallyQuasiFiniteRelativeDimension
import Sheaf.AlgebraicGeometry.QuasiFiniteLocallyQuasiFinite
import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
import Sheaf.TraceFormula.FlatFpRelativeDimensionDenseOpen
import WeilConjectures.AlgebraicGeometry.Morphisms.ProperQuasiFinite
import WeilConjectures.Mathlib.Topology.KrullDimension

/-! # Proper flat morphisms finite over a dense open are finite

Source: Stacks Project, `literature/stacks-project/flat.tex`, Tag 0B48,
lemma-proper-flat-finite-over-dense-open, locally-of-finite-presentation alternative (1)
(blueprint: lem-trf-proper-flat-finite-dense-open).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- If a proper, flat, locally finitely presented morphism is finite after restriction
along a dense open subscheme of the target, then it is finite.

Source: Stacks Project, `literature/stacks-project/flat.tex`, Tag 0B48,
lemma-proper-flat-finite-over-dense-open, locally-of-finite-presentation alternative (1)
(blueprint: lem-trf-proper-flat-finite-dense-open).

Proof:
1. The assumed finite morphism `X_U ⟶ U` is quasi-finite by `pqf-lem-finite-qf`, and
   hence locally quasi-finite by `pqf-lem-qf-locqf-qc`. By clause (3) of
   `pqf-def-quasifinite` it is of finite type, hence locally of finite type
   (`def-weil-finite-type-morphism`), so `lem-trf-locally-quasi-finite-relative-dimension-zero`
   applies to `X_U ⟶ U`. Its forward implication (locally quasi-finite implies relative
   dimension zero) gives `dim_x((X_U)_u) = 0` for every `x ∈ X_U` over `u ∈ U`; in
   particular `X_U ⟶ U` has relative dimension at most `0`.
2. Apply `lem-trf-flat-fp-relative-dimension-dense-open` with `e = 0`. Its hypotheses are
   the flatness and local finite presentation of `f`, the density of `U`, and the bound of
   step 1. Hence `dim_x(X_{f(x)}) ≤ 0` for every `x ∈ X`. The point of `X_{f(x)}` over `x`
   lies in every open neighbourhood used in `def-kun-topological-dimension-at-point`, so
   each such neighbourhood is nonempty of dimension `≥ 0`; thus `dim_x(X_{f(x)}) = 0` for
   every `x ∈ X`, i.e. `f` has relative dimension zero.
3. Since `f` is proper, it is of finite type by `def-weil-proper-morphism`, hence locally
   of finite type (`def-weil-finite-type-morphism`). The converse implication of
   `lem-trf-locally-quasi-finite-relative-dimension-zero` (relative dimension zero implies
   locally quasi-finite) and step 2 show that `f` is locally quasi-finite. The Mathlib leaf
   `pqf-lem-proper-lqf-finite` then gives that the proper locally quasi-finite morphism `f`
   is finite. -/
theorem proper_flat_finite_dense_open {X S : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f] (U : S.Opens)
    (hU : Dense (U : Set S)) [IsFinite (pullback.snd f U.ι)] : IsFinite f := by
  sorry

end AlgebraicGeometry
