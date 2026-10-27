/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.Mathlib.Topology.KrullDimension
import WeilConjectures.AlgebraicGeometry.EtaleOpenOfSmoothZeroFibreDimension
import WeilConjectures.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints
import Mathlib.Topology.Defs.Induced

/-!
# An étale open with a singleton fibre at a smooth zero-dimensional point

Source: Stacks Project, Tag 057G, proof of `lemma-slice-smooth`, case `d = 0`;
fibre topology from Tag 01K1 (blueprint: lem-trf-smooth-zero-dimensional-singleton-open).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A point of fibre dimension zero in a smooth open neighbourhood admits a smaller étale
open whose scheme-theoretic fibre has image exactly that point in the original scheme.
The open inclusion is an immersion. No closed-point or separability assumption is needed.

Source: Stacks Project, Tag 057G, proof of `lemma-slice-smooth`, case `d = 0`, and Tag 01K1
(blueprint: lem-trf-smooth-zero-dimensional-singleton-open).

Proof:
1. Apply `lem-weil-pbc-etale-near-point-smooth-zero-fibre-dimension`, namely
   `exists_etale_open_of_smooth_of_fibre_dimension_zero`, to obtain an étale open `U`
   containing `x` and contained in `W`.
2. By `lem-weil-pbc-etale-fibre-discrete-separable-points`, the fibre of `U` over `f x`
   is discrete. Its singleton corresponding to `x` is open. The fibre homeomorphism
   (`def-pc-scheme-fibre`, Stacks 01K1) identifies it with the singleton in the subspace
   fibre of `U`. By `def-kun-subspace-topology`, choose an open `V` of `U` whose
   intersection with that fibre is exactly this singleton.
3. Regard `V` as an open `Z` of `X`, contained in `U` and hence in `W`, using
   `def-weil-open-immersion`. The fibre homeomorphism identifies the image of its fibre
   in `X` with `{x}`. The inclusion in `U` is open, hence étale, and composition with
   the étale map from `U` is étale (`lem-weil-pbc-etale-composition-cancellation`).
4. Factor `Z.ι` as the identity of `Z` followed by its open inclusion in `X`.
   The identity is a closed immersion (its image is the whole space and its sheaf map
   is the identity). This gives the immersion of `def-weil-closed-immersion`.
   These steps use neither closedness of `x` in `X` nor separability of its residue field. -/
theorem exists_etale_open_singleton_fibre_of_smooth_of_dimension_zero
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) (W : X.Opens) (hx : x ∈ W)
    (hSmooth : Smooth (W.ι ≫ f)) (hDim : topologicalKrullDimAt (f.asFiber x) = 0) :
    ∃ Z : X.Opens, Z ≤ W ∧ x ∈ Z ∧ Etale (Z.ι ≫ f) ∧
      Set.range ((Z.ι ≫ f).fiberι (f x) ≫ Z.ι) = {x} ∧ IsImmersion Z.ι := by
  sorry

end AlgebraicGeometry
