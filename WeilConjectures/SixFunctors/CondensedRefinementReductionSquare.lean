/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CondensedRefinementCounitIdentification
public import WeilConjectures.SixFunctors.CondensedProjectionFactorScalarIdentities
public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.IntegralQuotientCoefficients
public import WeilConjectures.SixFunctors.ScalarSixCompactSupport

/-! # Finite scalar reduction and native compactification refinement

Source: literature/blueprint/latest/blueprint/sec-six-functors/sk-rem-sf-pf-done/
fix-prop-projection-formula.proof.md, the paragraph applying prop-sf-pf-reduction
with Lambda = A_{E,n} and J = pi_E^m A_{E,n}.
(blueprint: lem-sf-condensed-refinement-reduction-square).

The positive coefficient levels are indexed by n + 1 and m + 1, including m = 0.
The quotient transition is the existing IntegralQuotient.finiteMap, bundled by the
standard CommMon constructors. The equality uses ordinary uncompleted scalar extension,
the native clopen refinement map, and the normalized proper/open scalar comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open WeilConjectures
namespace WeilConjectures
/-- Finite reduction commutes with the native clopen compactification refinement map.
The map `scalarCompactSupportMap` is Rp_*(delta_j) after the scalar/direct-image mate
gamma_p, while `CompactificationReindexing.refinement` is c after Rp2_*(m_u).

Source: literature/blueprint/latest/blueprint/sec-six-functors/sk-rem-sf-pf-done/
fix-prop-projection-formula.proof.md, finite-reduction paragraph, the application of
prop-sf-pf-reduction to Lambda = A_{E,n}, J = pi_E^m A_{E,n}; the two proof steps of
DAG node lem-sf-condensed-refinement-reduction-square.
(blueprint: lem-sf-condensed-refinement-reduction-square).

Proof, Step 1 (the clopen adjunct square): write S for scalar extension and m_u for
the pullback/direct-image adjunct of the open base-change map followed by the clopen
projection on the section X -> u^{-1}(j2(X)). Transport internal modules to section-ring
module sheaves using lem-sfb-internal-module-operations-transport, which preserves the
pullback/direct-image and open adjunctions, their units and counits, and open base change.
The scalar adjunction is transported by lem-sfb-internal-section-scalar-adjunction.
Apply lem-pur-ringed-refinement-coefficient-square to the actual quotient ring-sheaf map.
Its hypotheses are properness of u, quasi-compactness of the two open immersions, and
u j1 = j2; no Cartesian or flatness assumption is required. Its clopen map is the same
m_u: both use V = u^{-1}(j2(X)), its clopen section, and the open base change normalized
as the adjunct of the pulled-back open unit. This is the normalization in
lem-sp-condensed-open-base-change-arbitrary and lem-sf-open-tensor-normalization.
Its direct-image comparison is gamma_u since both are the adjunct of scalar change of
the counit composed with the inverse-image/tensor comparison from
lem-sf-condensed-projection-factor-scalar-identities and
lem-weil-pbc-ringed-topoi-derived-tensor-pullback. Its open comparison is delta_j:
both restrict to the identity under the open-unit identifications, and full faithfulness
of j_! identifies them. The ringed coefficient square therefore gives
Ru_*(delta_j1) gamma_u S(m_u at n) = (m_u at m) delta_j2.

Step 2 (proper pushforward and pasting): substitute C_u = c Rp2_*(m_u) and
sigma_c = Rp_*(delta_j) gamma_p. The composition law of
lem-sfb-scalar-direct-image-mate-coherence for p1 = p2 u moves S(c at n) past gamma_p1
to c at m, Rp2_*(gamma_u), and gamma_p2. Naturality of c at delta_j1 and of gamma_p2
at m_u then makes the middle factor Rp2_* of the Step 1 square. Replace that factor
by Rp2_*((m_u at m) delta_j2), and regroup: the two resulting composites are C_u at m
and sigma_c2. This is the displayed equality. The argument holds on the ambient ordinary
derived categories, so applies to every bounded constructible T. Scalar extension of T
need not be bounded or have finite Tor amplitude, and no comparison map is inverted.
For equal levels the maps are the scalar unit identifications; for the identity refinement
the clopen adjunct is the open unit identification. -/
theorem condensed_refinement_reduction_square
    (D : WeilConjectures.FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra ℚ_[C.l] E]
    [FiniteDimensional ℚ_[C.l] E] (n m : ℕ) (hmn : m ≤ n)
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    [IsSeparated (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c₁ c₂ : Compactification f) (r : c₁.Refinement c₂)
    (T : ConstantModelBoundedConstructible
      (IntegralQuotient.finite C.l E n) X) :
    (scalarSixChange (CommMon.homMk
        (A := CommMon.mk (IntegralQuotient.finite C.l E n))
        (B := CommMon.mk (IntegralQuotient.finite C.l E m))
        (Mon.Hom.mk (IntegralQuotient.finiteMap C.l E n m hmn))) Y).map
      ((CompactificationReindexing.refinement
        (IntegralQuotient.finite C.l E n) r).app T.obj) ≫
        (AlgebraicGeometry.ProEtale.CondensedRing.scalarCompactSupportMap
          (CommMon.homMk
            (A := CommMon.mk (IntegralQuotient.finite C.l E n))
            (B := CommMon.mk (IntegralQuotient.finite C.l E m))
            (Mon.Hom.mk (IntegralQuotient.finiteMap C.l E n m hmn))) c₁.i c₁.g).app T.obj =
      (AlgebraicGeometry.ProEtale.CondensedRing.scalarCompactSupportMap
          (CommMon.homMk
            (A := CommMon.mk (IntegralQuotient.finite C.l E n))
            (B := CommMon.mk (IntegralQuotient.finite C.l E m))
            (Mon.Hom.mk (IntegralQuotient.finiteMap C.l E n m hmn))) c₂.i c₂.g).app T.obj ≫
        (CompactificationReindexing.refinement
          (IntegralQuotient.finite C.l E m) r).app
          ((scalarSixChange (CommMon.homMk
            (A := CommMon.mk (IntegralQuotient.finite C.l E n))
            (B := CommMon.mk (IntegralQuotient.finite C.l E m))
            (Mon.Hom.mk (IntegralQuotient.finiteMap C.l E n m hmn))) X).obj T.obj) := by
  sorry

end WeilConjectures
