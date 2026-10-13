/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Algebra.Category.ModuleCat.Differentials.Basic
public import WeilConjectures.Mathlib.Topology.KrullDimension
import WeilConjectures.RingTheory.StandardSmoothDimensionAtPoints

/-!
# Differentials of a smooth morphism and fibre dimension

Source: Stacks Project, Morphisms, Lemma 02G1 (label lemma-smooth-omega-finite-locally-free).
(blueprint: lem-weil-pbc-smooth-differentials-free-rank-fibre-dimension)
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry

/-- Stacks Project, Morphisms, Lemma 02G1.
(blueprint: lem-weil-pbc-smooth-differentials-free-rank-fibre-dimension)
For a smooth morphism and a point, the relative Kähler differentials are free near
that point, with rank the dimension of the fibre at the corresponding point.

Proof:
1. By `lem-weil-pbc-smooth-locally-standard-smooth`, choose affine neighbourhoods
   on which the induced ring map has a standard smooth presentation in `n` variables
   with `c` equations and an invertible Jacobian minor.
2. By `lem-weil-pbc-standard-smooth-kahler-basis`, the differentials have the basis
   given by the last `n - c` coordinate differentials.
3. Identify the fibre near its point with the spectrum of the affine fibre ring,
   using `lem-weil-pbc-affine-opens-induced-ring-map-spec-square`,
   `lem-weil-pbc-spec-residue-field-identification`,
   `lem-weil-pbc-open-fibre-product`, and `lem-weil-pbc-fibre-product-affine-spectra`.
   The local dimension is unchanged by this open restriction and homeomorphism,
   by `lem-weil-pbc-dimension-at-point-open-subspace`.
4. Base change preserves the standard smooth presentation by
   `lem-weil-pbc-standard-smooth-base-change`. The field case
   `lem-weil-pbc-standard-smooth-over-field-dimension-at-points` gives dimension
   `n - c`. This is nonnegative and equals the basis cardinality from step 2. -/
theorem smooth_differentials_free_rank_fibre_dimension
    (X S : Scheme.{u}) (f : X ⟶ S) [Smooth f] (x : X) :
    ∃ (d : ℕ),
        topologicalKrullDimAt (f.asFiber x) = (d : WithBot ℕ∞) ∧
          ∃ (V : S.Opens) (W : X.Opens) (hWV : W ≤ f ⁻¹ᵁ V),
            x ∈ W ∧ IsAffineOpen V ∧ IsAffineOpen W ∧
              Nonempty (Module.Basis (Fin d) (Γ(X, W))
                (CommRingCat.KaehlerDifferential (f.appLE V W hWV))) := by
  sorry

end AlgebraicGeometry
