/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.SmoothProjective
public import WeilConjectures.ZetaSeries
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Localization.Submodule
import WeilConjectures.AlgebraicGeometry.DimensionLocallyAlgebraic
import WeilConjectures.RingTheory.ClosedPointDimensionLocalRing
import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.RingTheory.RegularLocalDimOneIffNormal
import WeilConjectures.RingTheory.RegularLocalSeparableResidueSmooth
import WeilConjectures.RingTheory.SingularIdeal

/-! # Smoothness of a normal curve at a separable closed point

Source: Stacks Project, Varieties, Tag 0B8Y, `lemma-regular-point-on-curve`,
implications (2) to (3) and (6) in the separable-residue-field case
(blueprint: lem-sfb-normal-curve-separable-point-smooth).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A closed point of an integral curve whose stalk is integrally closed and whose residue
field is finite separable over the base has a DVR stalk and a smooth open neighbourhood.
The residue-field extension is the canonical one induced by the structure morphism `f`.
No perfection assumption is made on the base field.

Source: Stacks Project, Varieties, Tag 0B8Y, `lemma-regular-point-on-curve`
(blueprint: lem-sfb-normal-curve-separable-point-smooth).

Proof:
1. Choose an affine neighbourhood U = Spec S of x using
   lem-weil-pbc-affine-open-spec-points. Its point q is maximal since x is closed.
   lem-weil-pbc-lft-affine-pairs makes S a finite type k-algebra, and
   lem-weil-pbc-affine-open-stalk-localization identifies the stalk with S_q.
   The germ maps preserve scalars, so this also identifies residue fields over k.
2. Fields are Noetherian. Apply lem-weil-pbc-finite-type-algebra-noetherian and
   lem-weil-pbc-localization-noetherian to make S and S_q Noetherian. The stalk is local
   and is an integrally closed domain by the hypotheses and integrality of the curve.
3. lem-sc-dimension-locally-algebraic gives dimension one for every nonempty open of X.
   Transport neighbourhoods through the affine chart: the dimension at q is one.
   lem-weil-pbc-closed-point-dimension-local-ring then gives dim S_q = 1.
4. lem-sc-normal-dim1-dvr makes the stalk a DVR. Independently,
   lem-weil-pbc-regular-local-dim-one-iff-normal makes S_q regular.
5. The residue field at q is finite separable over k. Every subextension is separable
   algebraic and has the empty transcendence basis, so it is separable in the general
   field-extension sense used by lem-weil-pbc-regular-local-separable-residue-smooth.
   Apply that criterion to obtain smoothness at q.
6. By def-weil-pbc-singular-ideal choose g outside q with S_g smooth over k.
   lem-weil-pbc-principal-localization-open-immersion identifies Spec S_g with D(g).
   Transport this neighbourhood into X. The map to Spec k is the given structure map;
   lem-weil-pbc-smooth-ring-map-iff-smooth-affine makes it smooth. -/
theorem IsIntegralCurve.isDiscreteValuationRing_and_smoothAt_of_isIntegrallyClosed
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [IsIntegralCurve f] (x : X) (hx : IsClosed ({x} : Set X))
    [IsIntegrallyClosed (X.presheaf.stalk x)]
    (hfin : (f.residueFieldAlgebraMap x).Finite)
    (hsep : @Algebra.IsSeparable k (X.residueField x) _ _
      (f.residueFieldAlgebraMap x).toAlgebra) :
    IsDiscreteValuationRing (X.presheaf.stalk x) ∧
      ∃ U : X.Opens, x ∈ U ∧ Smooth (U.ι ≫ f) := by
  sorry

end AlgebraicGeometry
