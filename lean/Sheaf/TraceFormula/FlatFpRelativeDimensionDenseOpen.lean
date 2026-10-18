/-
Copyright (c) 2026. All rights reserved.
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import WeilConjectures.Mathlib.Topology.KrullDimension

import Sheaf.AlgebraicGeometry.DimensionExtension
import Sheaf.AlgebraicGeometry.FlatFibreDimensionStrataCore
import WeilConjectures.AlgebraicGeometry.AffineChartBaseChangeIso

/-! # Dense-open fibre-dimension bounds for flat finitely presented morphisms

Source: literature/stacks-project/flat.tex, Tag 081L, alternative (1)
(blueprint: lem-trf-flat-fp-relative-dimension-dense-open).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry

/-- A pointwise relative fibre-dimension bound on a dense open extends across a
flat locally finitely presented morphism.

Source: Stacks Project, Tag 081L, alternative (1)
(blueprint: lem-trf-flat-fp-relative-dimension-dense-open).

Proof:
1. For `s ∈ U`, identify `(X_U)_s` with `X_s`, preserving the point over each `x` with
   `f x = s`: the open-subscheme stalk at `s` is the stalk of `S`, so its residue field is
   `κ(s)`, and both schemes represent maps to `X` and to `Spec κ(s)` agreeing in `S` (the map
   to `U` is forced). The inverse homeomorphisms identify local dimensions, so
   `dim_x X_{f x} ≤ e` whenever `f x ∈ U`.
2. Apply `lem-sbc-flat-fibre-dimension-strata-core` to `f` and the open `S ⊆ S` (flatness and
   local finite presentation are its hypotheses): opens `V_n ⊆ X` with `dim_y X_{f y} = n` on
   `V_n` and union `W` whose inverse image `W_s` is dense open in every fibre `X_s`.
3. For `n > e`, if `V_n` were nonempty, `f(V_n)` would be a nonempty open of `S`
   (`lem-weil-pbc-flat-lfp-open`), hence meet the dense `U` at some `s = f y`, `y ∈ V_n`;
   step 2 gives `dim_y X_s = n` and step 1 gives `dim_y X_s ≤ e`, a contradiction. So every
   point of `W_s` has local dimension at most `e` in `X_s`.
4. Fix `x : X`, `s = f x`, `Y = X_s`. Choose affine opens `x ∈ V = Spec B`, `s ∈ T = Spec R`
   with `f(V) ⊆ T` and `B` finitely presented over `R`
   (`def-sbc-locally-finite-presentation`). By `lem-weil-pbc-affine-chart-base-change-iso` the
   open `A = (Y → X)⁻¹(V)`, containing the point over `x`, is `Spec (κ(s) ⊗_R B)`, generated
   over `κ(s)` by the images of the variables: `A` is of finite type over `κ(s)`.
5. `H = A ∩ W_s` is open and dense in `A` (a nonempty open of `A` is open in `Y`, so meets
   `W_s`). For `h ∈ H`, step 3 and `lem-weil-pbc-dimension-at-point-open-subspace` give
   `dim_h H = dim_h Y ≤ e`.
6. Choose for each `h ∈ H` an open neighbourhood `N_h` with `dim N_h = dim_h H ≤ e`; they cover
   `H`. `H` is quasi-sober and `T₀` (`lem-sc-scheme-sober`), so
   `lem-weil-pbc-dimension-bound-open-cover` gives `dim H ≤ e` (also for empty `H`).
7. `A` is of finite type over `κ(s)` and `H ⊆ A` is dense open, so the dense-open clause of
   `lem-kun-dimension-extension` gives `dim A = dim H ≤ e`. The whole `A` is a neighbourhood of
   the point `x̃` over `x`, so `dim_x̃ A ≤ dim A`, and
   `lem-weil-pbc-dimension-at-point-open-subspace` gives `dim_x X_s = dim_x̃ A ≤ e`. Empty `X`
   is vacuous; `e = 0` is allowed.
-/
theorem flat_finitePresentation_relativeDimension_denseOpen
    {X S U : Scheme.{u}} (f : X ⟶ S) [Flat f]
    [LocallyOfFinitePresentation f] (j : U ⟶ S) [IsOpenImmersion j]
    (hdense : Dense (Set.range j.base)) (e : ℕ)
    (hbound : ∀ x : pullback (C := Scheme.{u}) f j,
      topologicalKrullDimAt ((pullback.snd f j).asFiber x) ≤ e) :
    ∀ x : X, topologicalKrullDimAt (f.asFiber x) ≤ e := by
  sorry

end AlgebraicGeometry
