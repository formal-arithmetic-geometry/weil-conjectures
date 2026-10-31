/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.SmoothProjective
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.KrullDimension.Basic
public import WeilConjectures.Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.IsRegularScheme
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Kaehler.Basic
import WeilConjectures.AlgebraicGeometry.Dimension
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.Topology.KrullDimension
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.AlgebraicGeometry.AffineScheme
import WeilConjectures.RingTheory.SmoothOverFieldRegularLocal
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs
import WeilConjectures.AlgebraicGeometry.SmoothDifferentialsFreeRankFibreDimension
import Mathlib.RingTheory.Etale.Kaehler

/-!
# Closed stalks on smooth integral curves

Source: Stacks Project, Curves, Tag 0C1E, `lemma-uniformizer-works`, first and last
proof sentences; Properties, Tags 04MU and 02IZ; Morphisms, Tag 02G1
(blueprint: lem-a1-smooth-curve-closed-stalk-structure).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A closed stalk of a smooth integral curve is regular local of dimension one, hence
Noetherian and a DVR, and its differentials over the base field are free of rank one.
Every open neighbourhood of the point has dimension one, as does the dimension at the point.
The algebra structure on the stalk is the original structure morphism followed by the germ.
No separability of the residue extension is required.

Source: Stacks Project, Curves, Tag 0C1E, `lemma-uniformizer-works`, first and last
proof sentences; Properties, Tags 04MU and 02IZ; Morphisms, Tag 02G1
(blueprint: lem-a1-smooth-curve-closed-stalk-structure).

Proof:
1. By lem-pc-scheme-dimension-local-rings and def-pc-curve, the topological dimension
   of X is one. Integrality makes X nonempty and irreducible by
   lem-pc-integral-scheme-irreducible. By lem-sc-scheme-sober it has a generic point eta.
   This differs from the closed point x: otherwise X is a singleton and has dimension zero.
2. The strict chain x, eta gives stalk dimension at least one by
   lem-sc-scheme-stalk-dimension-generalization-chains; the global dimension bounds it
   above by one by lem-pc-scheme-dimension-local-rings. Every open neighbourhood N of x
   contains eta, whose closure in N is N. Thus {x} strictly contained in N is a chain
   of irreducible closed subsets. The lower bound one and the upper bound from
   lem-weil-pbc-open-subspace-dimension-monotone give dimension N = 1. Taking the
   infimum over these neighbourhoods gives dimension at x = 1 by def-kun-dimension.
3. Choose an affine neighbourhood Spec B of x. By
   lem-weil-pbc-smooth-restrict-open-subschemes and
   lem-weil-pbc-smooth-ring-map-iff-smooth-affine, B is smooth over k. Its localization
   at the prime of x is regular local by lem-weil-pbc-smooth-over-field-regular-local.
   Identify it with the stalk by lem-weil-pbc-affine-open-stalk-localization. Regular
   local rings are Noetherian by def-weil-regular-scheme, and the dimension-one result
   gives a DVR by lem-sc-regular-dim1-dvr.
4. The fibre of X over the unique point of Spec k is X, so its dimension at x is one.
   By lem-weil-pbc-smooth-differentials-free-rank-fibre-dimension there is an affine
   neighbourhood Spec C of x where the differentials are free on one generator e.
   By lem-weil-pbc-affine-open-stalk-localization and
   lem-weil-pbc-kahler-differentials-localization, the stalk differentials are the
   localization of C e at the prime of x. The maps c/s to c e/s and c e/s to c/s
   are mutually inverse: equality of module fractions is equality of their coefficients
   in the free basis e. This gives the stated linear equivalence over the stalk.
   All algebra maps come from the original structure morphism; no residue separability
   was used. -/
theorem smooth_curve_closed_stalk_structure
    (k : Type u) [Field k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
    [IsIntegralCurve f] [Smooth f] (x : X) (hx : IsClosed ({x} : Set X)) :
    ringKrullDim (X.presheaf.stalk x) = 1 ∧
      (∀ N : X.Opens, x ∈ N → topologicalKrullDim N = 1) ∧
      topologicalKrullDimAt x = 1 ∧
      IsRegularLocalRing (X.presheaf.stalk x) ∧
      IsNoetherianRing (X.presheaf.stalk x) ∧
      IsDiscreteValuationRing (X.presheaf.stalk x) ∧
      Nonempty ((X.presheaf.stalk x) ≃ₗ[X.presheaf.stalk x]
        @KaehlerDifferential k (X.presheaf.stalk x) _ _
          (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
            X.presheaf.germ ⊤ x trivial).hom.toAlgebra)) := by
  sorry

end AlgebraicGeometry
