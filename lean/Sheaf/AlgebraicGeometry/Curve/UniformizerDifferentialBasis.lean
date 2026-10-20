/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q132
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.SmoothProjective
public import WeilConjectures.ZetaSeries
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Kaehler.Basic
import WeilConjectures.AlgebraicGeometry.Dimension
import WeilConjectures.Mathlib.Topology.KrullDimension
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.AlgebraicGeometry.AffineScheme
import Sheaf.RingTheory.SmoothOverFieldRegularLocal
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs
import Sheaf.AlgebraicGeometry.SmoothDifferentialsFreeRankFibreDimension
import Mathlib.RingTheory.Etale.Kaehler
import WeilConjectures.AlgebraicGeometry.SeparableResidueCotangentInjective
import WeilConjectures.FieldTheory.SeparableExtension
import Mathlib.RingTheory.AlgebraicIndependent.Defs

/-!
# Differentials of uniformizers on smooth curves

Source: Stacks Project, Curves, Tag 0C1E, `lemma-uniformizer-works`
(blueprint: lem-a1-uniformizer-differential-basis).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- At a closed point with finite separable residue field on a smooth integral curve,
the stalk is a discrete valuation ring and the differential of every uniformizer is a basis.
The stalk algebra is induced by the structure morphism, global sections, and the germ map.
Source: Stacks Project, Curves, Tag 0C1E, `lemma-uniformizer-works`
(blueprint: lem-a1-uniformizer-differential-basis).

Proof:
1. By def-pc-curve and lem-pc-scheme-dimension-local-rings the integral scheme has
   dimension one. Its generic point (lem-sc-scheme-sober) differs from the closed point.
   The strict generalization chain and lem-sc-scheme-stalk-dimension-generalization-chains
   give stalk dimension at least one, and the global dimension bounds it above by one.
   Every open neighbourhood contains the generic point and the closed point, so its
   dimension is also one; hence def-kun-dimension gives dimension at the point one.
2. Choose an affine neighbourhood. Apply lem-weil-pbc-smooth-restrict-open-subschemes,
   lem-weil-pbc-smooth-ring-map-iff-smooth-affine, and
   lem-weil-pbc-affine-open-stalk-localization. The stalk is regular local by
   lem-weil-pbc-smooth-over-field-regular-local, and a DVR by lem-sc-regular-dim1-dvr.
3. Apply lem-weil-pbc-smooth-differentials-free-rank-fibre-dimension and
   lem-weil-pbc-kahler-differentials-localization to obtain a rank-one basis e of the
   stalk differentials, using lem-weil-pbc-affine-open-stalk-localization again.
4. For a uniformizer t, its class in m/m² is nonzero: otherwise t = t²b, and cancellation
   gives 1 = tb, contradicting t belonging to the maximal ideal.
5. Finite separability gives finite generation and separability in the sense of
   def-weil-pbc-separable-field-extension: every intermediate field is algebraic, has
   the empty transcendence basis (def-weil-pbc-transcendence-basis), and is separable
   algebraic (def-weil-pbc-separable-algebraic-extension). Apply
   lem-weil-pbc-separable-residue-cotangent-injective to get dt tensor 1 nonzero.
6. Write dt = a e. The residue of a is nonzero, so a is a unit of the local ring.
   Multiplication by dt therefore identifies the stalk with its differential module;
   in coordinates the inverse sends c e to c a⁻¹. This holds for every uniformizer. -/
theorem uniformizer_differential_basis
    (k : Type u) [Field k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
    [IsIntegralCurve f] [Smooth f] (x : X) (hx : IsClosed ({x} : Set X))
    (hfinite : (f.residueFieldAlgebraMap x).Finite)
    (hsep : @Algebra.IsSeparable k (X.residueField x) _ _
      (f.residueFieldAlgebraMap x).toAlgebra) :
    IsDiscreteValuationRing (X.presheaf.stalk x) ∧
      ∀ t : X.presheaf.stalk x,
        IsLocalRing.maximalIdeal (X.presheaf.stalk x) = Ideal.span {t} →
          Function.Bijective (fun a : X.presheaf.stalk x ↦
            a • @KaehlerDifferential.D k (X.presheaf.stalk x) _ _
              (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
                X.presheaf.germ ⊤ x trivial).hom.toAlgebra) t) := by
  sorry

end AlgebraicGeometry
