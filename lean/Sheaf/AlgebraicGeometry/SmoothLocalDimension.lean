/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q12
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Fiber
public import WeilConjectures.Mathlib.Topology.KrullDimension
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Sheaf.AlgebraicGeometry.SmoothDifferentialsFreeRankFibreDimension

import Mathlib.AlgebraicGeometry.AffineScheme
import Sheaf.AlgebraicGeometry.FlatConstantRelativeDimension
/-!
# Local topological dimension of a smooth morphism

Source: Stacks Project, Morphisms, Tag 0AFF, lemma-smoothness-dimension, and Tag 02G2,
definition-smooth-relative-dimension (blueprint: lem-per-smooth-local-dimension).

## Main statements

* `AlgebraicGeometry.topologicalKrullDimAt_eq_add_of_smooth`: the local dimension formula.
* `AlgebraicGeometry.topologicalKrullDimAt_asFiber_eq_of_smoothOfRelativeDimension`: the fibre
  summand is the constant relative dimension.

All dimensions are infima of dimensions of open neighbourhoods, not local-ring dimensions.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Stacks Project, Morphisms, Tag 0AFF, lemma-smoothness-dimension
(blueprint: lem-per-smooth-local-dimension).
For a smooth morphism of locally Noetherian schemes, local topological dimension at a
point is the local dimension at its image plus the local dimension in the fibre.

Proof:
1. Set `q = g p`. The finite nonnegative fibre dimension `d` is supplied by
   `lem-weil-pbc-smooth-differentials-free-rank-fibre-dimension`. By
   `sbc-lem-smooth-relative-dimension-locally-constant`, choose an open neighbourhood `U`
   of `p` on which the fibre dimension is constantly `d`.
2. The restriction `h : U → Q` is flat by `lem-pc-smooth-flat`,
   `def-weil-open-immersion`, and `def-weil-flat-morphism`: its stalk maps are those of `g`.
   It is locally Noetherian by `pqf-def-locnoeth`. On affine opens its ring maps are of
   finite presentation by `lem-weil-pbc-lfp-affine-opens-finite-presentation`, hence of
   finite type by taking the images of the polynomial generators, as required by
   `def-weil-finite-type-morphism`. No finite subcover is needed.
3. By `def-pc-scheme-fibre`, each fibre of `h` is an open subspace of the corresponding
   fibre of `g`. The equality of local dimensions on open subspaces from
   `lem-weil-pbc-dimension-at-point-open-subspace` makes every fibre dimension of `h`
   equal to `d`; empty fibres impose no condition.
4. Apply `lem-per-flat-constant-relative-dimension` to `h`, which is flat and locally of
   finite type between locally Noetherian schemes. It gives `dim_p U = dim_q Q + d`.
5. Apply `lem-weil-pbc-dimension-at-point-open-subspace` once more to replace `dim_p U`
   by `dim_p P`, and substitute `d = dim_p P_q`. Addition is in `WithBot ℕ∞`, so the
   equality includes infinite local dimension of the base. -/
theorem topologicalKrullDimAt_eq_add_of_smooth
    (P Q : Scheme.{u}) [IsLocallyNoetherian P] [IsLocallyNoetherian Q]
    (g : P ⟶ Q) [Smooth g] (p : P) :
    topologicalKrullDimAt p =
      topologicalKrullDimAt (g p) + topologicalKrullDimAt (g.asFiber p) := by
  sorry

/-- Stacks Project, Morphisms, Tag 02G2, definition-smooth-relative-dimension, and the
constant-dimension clause accompanying Tag 0AFF (blueprint: lem-per-smooth-local-dimension).
If the smooth morphism has constant relative dimension `d`, its fibre summand is `d`.

Proof (Step 6 of the node): `def-sbc-smooth-morphisms` identifies smoothness of relative
 dimension `d` with smoothness and local topological dimension `d` in each fibre. Apply
this at `p`, with the fibre point given by `g.asFiber p`. Equivalently, base change to
`Spec κ(g p)` preserves smoothness of relative dimension `d`, and the local dimension
of a scheme smooth of relative dimension `d` over a field is `d`. For the empty source
there is no `p`; `d = 0` and arbitrary characteristics are included. -/
theorem topologicalKrullDimAt_asFiber_eq_of_smoothOfRelativeDimension
    (P Q : Scheme.{u}) [IsLocallyNoetherian P] [IsLocallyNoetherian Q]
    (g : P ⟶ Q) (d : ℕ) [SmoothOfRelativeDimension d g] (p : P) :
    topologicalKrullDimAt (g.asFiber p) = (d : WithBot ℕ∞) := by
  sorry

end AlgebraicGeometry
