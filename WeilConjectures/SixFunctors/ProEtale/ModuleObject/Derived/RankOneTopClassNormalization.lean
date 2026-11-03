/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.RankOneDivisorClassIntegral

/-! # The top cohomology class of the canonical Thom map

Source: the rank-one Thom proof, Step 2.
(blueprint: lem-pur-rank-one-top-class-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open scoped CategoryTheory.Obj CategoryTheory.MonoidalCategory CategoryTheory.MonObj
open AlgebraicGeometry AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.CondensedRing
open Admissible

/-- In degree zero, the actual supported class gives the invertible signed generator.

Source: latest blueprint thm-pur-rank-one-thom.proof.md, Step 2, with its current
DAG correction cl(0) = -c0
(blueprint: lem-pur-rank-one-top-class-normalization).

Proof: for a finite admissible ring, pull back to a geometric point and trivialize
the line fibre. Retain the finite etale representative and the comparison maps.
The supported-origin Kummer calculation identifies the local divisor class with
the positive boundary of the coordinate. The proper-section identification used
in canonicalTau sends the supported unit to one. Apply extension by zero for the
standard A1 chart of P1, then its counit. Cartier naturality and uniqueness under
the supported-Hom adjunction identify the resulting global class with -h, where
h = c1(O(1)) is normalized by Picard degree. In degree two the map from compact
cohomology to projective cohomology is invertible by localization, and the degree
trace sends h to one. Consequently the degree-zero map displayed here is
multiplication by -1 between free rank-one modules; it is invertible over every
finite coefficient ring, also in characteristic two and for the zero ring.
Compact exchange and constructibility identify these with the geometric
pullbacks of the map on B, and geometric-point detection gives invertibility.
For integral coefficients retain the specified whole Kummer system, rather than
choosing individual lifts. Its scalar comparison and proper-section comparison
identify all finite-level degree-zero maps with the preceding signed generators.
The epimorphic free rank-one tower has no derived-limit correction; its limit
map is again the signed generator. Integral completeness identifies it with the
actual degree-zero map of canonicalTau. The same coefficient-change equation and
compact scalar exchange give the assertion for the rational and algebraic-closure
coefficients. Finally transport across the ring-object isomorphisms in the
admissibility predicate. No equality of derived arrows is inferred solely from
their individual reductions, and no invertibility of canonicalTau is assumed. -/
theorem rankOne_top_class_normalization
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {B : Scheme.{u}} (b : B ⟶ Spec (CommRingCat.of P.field.k))
    [IsSeparated b] [LocallyOfFiniteType b] [QuasiCompact b]
    (V : PurityVectorBundle P B b 1)
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (hΛ : IsAdmissibleCoefficientFor P.coefficients Λ)
    (c : Compactification V.p) :
    IsIso ((DerivedCategory.homologyFunctor (Modules Λ B) 0).map
      (canonicalTau P b V Λ hΛ c)) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
