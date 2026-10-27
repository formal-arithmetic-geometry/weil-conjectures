/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q09
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Monoidal.Tor
public import WeilConjectures.AlgebraicGeometry.PullbackStalkTensorComparison
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Flat.Basic
import WeilConjectures.Algebra.Category.ModuleCat.TorSymmetry
import WeilConjectures.RingTheory.TorVanishingLocalizedAlgebra
import Sheaf.RingTheory.TorCoefficientLocalization
import WeilConjectures.RingTheory.TorVanishingLocalizedBase

/-! # Common-base changes of flat families are Tor independent

Source: Stacks Project, Tag 0661 (`lemma-base-change-comparison`), the free-resolution
computation, followed by localization of Tor (Tags 00M8 and 0B67).
(blueprint: lem-sfb-flat-families-tor-independent).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- An arbitrary morphism of flat S-schemes is Tor independent of the projection from
an arbitrary base change of its target. Tor independence quantifies over every pair
of points with the same target point and uses the actual transported stalk actions.
Source: Stacks Project, Tag 0661 (`lemma-base-change-comparison`), free-resolution
computation; Tags 00M8 and 0B67 for localization.
(blueprint: lem-sfb-flat-families-tor-independent).

Proof: (1) Fix points x and y' with common image y. Choose compatible affine
neighbourhoods Spec B in X, Spec A in Y, Spec R in S and Spec C in S'
[lem-weil-pbc-affine-opens-basis]. Their fibre product is the open Spec E,
E = A tensor_R C, containing y' [lem-weil-pbc-open-fibre-product,
lem-weil-pbc-fibre-product-affine-spectra]. Stalks and their maps are localizations
[lem-weil-pbc-affine-open-stalk-localization, lem-weil-pbc-spec-map-stalk-localization].
Flatness of the two structure morphisms gives flatness of A and B over R by the
local criterion [def-weil-flat-morphism, lem-pc-affine-sections-flat-over-base].
(2) Choose a free R-resolution P of C [def-weil-pbc-tor-modules]. Since A is R-flat,
A tensor_R P is a free A-resolution of E [lem-weil-pbc-flat-tensor-exact]. Tensoring
it over A with B gives P tensor_R B, exact in positive degrees since B is R-flat.
Thus Tor_i^A(E,B) vanishes for i > 0; symmetry gives Tor_i^A(B,E) = 0
[lem-weil-pbc-tor-symmetry].
(3) Localize B at the prime p of x [lem-pc-tor-vanishing-localized-algebra], then E
at the prime r of y' [lem-trf-tor-localization-on-spec]. Both resulting modules are
modules over A_q, where q is the common contraction. Localization of the base
therefore gives Tor_i^(A_q)(B_p,E_r) = 0 [lem-pc-tor-vanishing-localized-base].
(4) The affine stalk identifications identify these actions with the stalk maps
of f and the first projection, giving exactly stalkwise Tor independence
[def-pc-pullback-stalk-tensor-comparison]. The pullback universal property identifies
X times_S S' with X times_Y (Y times_S S') compatibly with projections
[def-pc-fibre-product]. Empty schemes are covered by the pointwise quantification.
-/
theorem flat_families_torIndependent {S X Y S' : Scheme.{u}}
    (p : X ⟶ S) (q : Y ⟶ S) [Flat p] [Flat q]
    (f : X ⟶ Y) (hf : f ≫ q = p) (a : S' ⟶ S) :
    PullbackStalkTensor.IsTorIndependent f (pullback.fst q a) := by
  sorry

end AlgebraicGeometry
