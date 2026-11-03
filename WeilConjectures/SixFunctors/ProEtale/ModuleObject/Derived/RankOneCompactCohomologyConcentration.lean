/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.RankOneDivisorClassIntegral

/-! # Cohomological concentration for a rank-one bundle

Source: the rank-one Thom proof, Step 2.
(blueprint: lem-pur-rank-one-compact-cohomology-concentration).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open scoped CategoryTheory.Obj CategoryTheory.MonoidalCategory CategoryTheory.MonObj
open AlgebraicGeometry AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.CondensedRing
open Admissible

/-- The positive shifted compact-support object has no cohomology outside degree zero.

Source: latest blueprint, thm-pur-rank-one-thom.proof.md, Step 2, and the independent
projective-line calculation in the current DAG proof of thm-pur-rank-one-thom
(blueprint: lem-pur-rank-one-compact-cohomology-concentration).

Proof: first take finite coefficients A annihilated by a positive power of ell.
Over an algebraically closed geometric point, compactify the fibre line by P1.
The Kummer/Picard-degree calculation gives the two-term splitting of the ordinary
projective-line cohomology, with the unit in degree zero and A(-1) in degree two.
Restriction to infinity is the identity on the first summand and zero on the
second, because O(1) restricts to a trivial line at infinity. The open-closed
localization triangle therefore identifies the compact-support object for the
positive twist shifted by two with A in degree zero. The finite etale/pro-etale
comparison and canonical compact exchange transport this vanishing to the full
geometric pullbacks of the displayed object. Compact constructibility and
geometric-point detection applied to its cohomology sheaves give the assertion
on B, including the empty base.
For integral coefficients, compact-support scalar exchange identifies every
positive uniformizer reduction with that finite calculation. The input is lisse
of rank one and has finite Tor amplitude, so its compact-support image is
constructible and derived complete by the integral criterion. The whole reduction
tower has free rank-one cohomology in degree zero with surjective quotient
transitions; its derived inverse limit is therefore also concentrated in degree
zero. Completeness identifies this limit with the displayed object. Rational and
algebraic-closure coefficients follow from actual compact-support scalar exchange:
tensoring the free integral degree-zero object has no higher Tor. Transport along
the ring-object isomorphisms in admissibility handles all allowed presentations.
This calculation is independent of the supported class and does not assume that
the canonical Thom map is invertible. -/
theorem rankOne_compact_cohomology_concentration
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {B : Scheme.{u}} (b : B ⟶ Spec (CommRingCat.of P.field.k))
    [IsSeparated b] [LocallyOfFiniteType b] [QuasiCompact b]
    (V : PurityVectorBundle P B b 1)
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (hΛ : IsAdmissibleCoefficientFor P.coefficients Λ)
    (c : Compactification V.p) (q : ℤ) (hq : q ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (Modules Λ B) q).obj
      ((rightDerivedLowerShriekOfCompactification Λ.X c).obj
        (((DerivedCategory.singleFunctor (Modules Λ V.E) 0).obj
          (line P Λ hΛ V.E)) ⟦(2 : ℤ)⟧))) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
