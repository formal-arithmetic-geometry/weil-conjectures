/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q08
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Fiber
public import WeilConjectures.Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor

import Sheaf.AlgebraicGeometry.SmoothDifferentialsFreeRankFibreDimension
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.ResidueField
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.RingTheory.Kaehler.TensorProduct
import WeilConjectures.RingTheory.SmoothAtPrimeOfDifferentialsDimensionBound
import Sheaf.AlgebraicGeometry.FlatSmoothFibreSmoothAtPrime
import WeilConjectures.RingTheory.SingularIdeal
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import WeilConjectures.AlgebraicGeometry.Thickening
import WeilConjectures.AlgebraicGeometry.FormallySmooth

/-!
# Smoothness at a point from relative differentials

Source: Stacks Project, Morphisms, Tag 01V9 (lemma-smooth-at-point), (1) iff (3),
and Definition 01V5 (blueprint: lem-trf-smooth-at-point-differential-criterion).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

/-- A locally finitely presented morphism is smooth on a neighbourhood of `x` precisely when
its local ring map at `x` is flat and its differential stalk has a spanning family of size
at most the dimension of the fibre at `x`. The fibre point is the canonical `f.asFiber x`.
Source: Stacks Project, Morphisms, Tag 01V9, (1) iff (3), and Definition 01V5
(blueprint: lem-trf-smooth-at-point-differential-criterion).

Proof:
1. If `f` is smooth on an open neighbourhood, its stalk map is flat by
   `lem-pc-smooth-flat` and `def-weil-flat-morphism`. Apply
   `lem-weil-pbc-smooth-differentials-free-rank-fibre-dimension` to the restriction.
   The open fibre identification (`lem-weil-pbc-open-fibre-product`) and
   `lem-weil-pbc-dimension-at-point-open-subspace` preserve the fibre dimension.
   Use `def-sc-relative-differential-sheaf` and
   `lem-weil-pbc-spec-tilde-stalk-localization` to localize the differential basis.
   Its localized vectors span the stalk, with the same number of generators.
2. Conversely, choose finite-presentation affine neighbourhoods `W = Spec A` and
   `V = Spec R` by `def-sbc-locally-finite-presentation`. Write `q` for the prime of `x`
   and `p` for its contraction, using
   `lem-weil-pbc-affine-opens-induced-ring-map-spec-square`. The stalk identifications
   `lem-weil-pbc-affine-open-stalk-localization` and
   `lem-weil-pbc-spec-map-stalk-localization` give flatness of `R_p → A_q`.
   The affine differential description and tilde-stalk localization identify the
   differential stalk with the localization of `Omega A/R`, preserving its generators.
3. Set `k = kappa(p)` and `F = k ⊗[R] A`. Use
   `lem-weil-pbc-affine-open-stalk-localization`,
   `lem-weil-pbc-spec-residue-field-identification`,
   `lem-weil-pbc-open-fibre-product`, and `lem-weil-pbc-fibre-product-affine-spectra`
   to identify `Spec F` with an open of the scheme fibre. The prime `Q` above `x`
   is the kernel of `F → kappa(q)`. Its contraction is `q`, and its dimension is `d`
   by `lem-weil-pbc-dimension-at-point-open-subspace` and `def-pc-scheme-fibre`.
   The algebra `F` is finite type over `k`, by base changing a finite presentation,
   so `lem-kun-dimension-finite-type` makes this dimension finite and nonnegative.
4. By `lem-weil-pbc-kahler-differentials-base-change`, tensoring the localized
   differential module with `L = kappa(Q)` gives `Omega F/k` tensored with `L`.
   The comparison sends `(omega/a) ⊗ lambda` to `(1 ⊗ omega) ⊗ (lambda/a)`;
   its inverse sends `(b ⊗ omega) ⊗ lambda` to `(omega/1) ⊗ (b*lambda)`.
   Tensor balancing and localization relations make these inverse. The images
   of the stalk generators span this vector space, so its dimension is at most `d`.
5. Apply `lem-weil-pbc-differentials-dimension-bound-smooth-at-prime` to `F/k` at `Q`.
   Apply `lem-weil-pbc-flat-smooth-fibre-smooth-at-prime` with localization parameter
   one to the original finite-presentation map `R → A`. Thus it is smooth at `q`.
   By `def-weil-pbc-singular-ideal`, some `g` outside `q` makes `R → A_g` smooth.
6. The principal localization is an open neighbourhood of `x` by
   `lem-weil-pbc-principal-localization-open-immersion`, and its map to `V` is smooth by
   `lem-weil-pbc-smooth-ring-map-iff-smooth-affine`. It is locally finitely presented
   over `S` by `def-sbc-locally-finite-presentation`. For a first-order thickening
   lifting problem over `S`, its two schemes have the same points
   (`def-sbc-first-order-thickening`), so the larger scheme also factors through `V`
   (`def-weil-open-immersion`). Formal smoothness over `V` supplies the lift
   (`def-sbc-formally-smooth`). Thus the neighbourhood map to `S` is smooth by
   `def-sbc-smooth-morphisms`, as required. -/
theorem smoothAtPoint_iff_flat_stalkMap_and_differentials_generators
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f] (x : X) :
    (∃ U : X.Opens, x ∈ U ∧ Smooth (U.ι ≫ f)) ↔
      (f.stalkMap x).hom.Flat ∧
        ∃ (n : ℕ)
          (v : Fin n → (RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj
            f.relativeDifferentials),
          (n : WithBot ℕ∞) ≤ topologicalKrullDimAt (f.asFiber x) ∧
            Submodule.span (X.presheaf.stalk x) (Set.range v) = ⊤ := by
  sorry

end AlgebraicGeometry.Scheme.Hom
