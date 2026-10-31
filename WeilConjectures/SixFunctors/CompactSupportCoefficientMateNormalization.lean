/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.NormalizedDVRTower
public import WeilConjectures.AlgebraicGeometry.CompactSupportReductionTowerData
public import WeilConjectures.SecSmoothPurity.IntrinsicCompactSupportRestriction
public import WeilConjectures.SecSmoothPurity.ReductionExceptional

/-! # The restriction transpose of the proper/open coefficient mate

Source: the evaluated-support proof, step 4; Stacks 07A6, 0D6E and 0GL1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale

namespace WeilConjectures.DualizingSupportEvaluation

/-- The specified proper/open coefficient map in intrinsic coordinates.
Source: blueprint paragraph 2
(blueprint: lem-coef-compact-support-coefficient-mate-normalization). -/
def coefficientMateComparison
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    {m n : ℕ} (h : n ≤ m) :
    sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (m + 1)) ⋙
        scalarExtensionFunctor (compactSupportLevelQuotient l E m n h) Y ⟶
      scalarExtensionFunctor (compactSupportLevelQuotient l E m n h) X ⋙
        sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1)) :=
  let A := Padic.coefficientExtensionRing l E (m + 1)
  let B := Padic.coefficientExtensionRing l E (n + 1)
  let φ := compactSupportLevelQuotient l E m n h
  let eA := Functor.isoWhiskerLeft (sfIntrinsicExtensionByZero c.i A).mapDerivedCategory
    (eqToIso (reductionConstantPush_eq A c.g))
  let eB := Functor.isoWhiskerLeft (sfIntrinsicExtensionByZero c.i B).mapDerivedCategory
    (eqToIso (reductionConstantPush_eq B c.g))
  Functor.whiskerRight eA.inv (scalarExtensionFunctor φ Y) ≫
    reductionDirectImageComparison φ c.i c.g ≫
      Functor.whiskerLeft (scalarExtensionFunctor φ X) eB.hom

/-- Scalar-adjunction arrow for the specified proper/open coefficient map.
Source: blueprint paragraph 2 (blueprint: lem-coef-compact-support-coefficient-mate-normalization).
The expression is factored once so downstream applications share its derived-category data. -/
def coefficientMateRestrictionArrow
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    {m n : ℕ} (h : n ≤ m)
    {M : normalizedDVRDerived l E X m} {N : normalizedDVRDerived l E X n}
    (s : M ⟶ (scalarRestriction (compactSupportLevelQuotient l E m n h) X).obj N) :
    (sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (m + 1))).obj M ⟶
      (scalarRestriction (compactSupportLevelQuotient l E m n h) Y).obj
        ((sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1))).obj N) :=
    let A := Padic.coefficientExtensionRing l E (m + 1)
    let B := Padic.coefficientExtensionRing l E (n + 1)
    let φ := compactSupportLevelQuotient l E m n h
    let γ := coefficientMateComparison l E c h
    (proEtaleRingDerivedExtensionAdjunction (proEtaleConstantRingMap (T := Y) φ)).unit.app
        ((sfIntrinsicCompactSupport c A).obj M) ≫
      (scalarRestriction φ Y).map (γ.app M ≫ (sfIntrinsicCompactSupport c B).map
        (((proEtaleRingDerivedExtensionAdjunction
          (proEtaleConstantRingMap (T := X) φ)).homEquiv _ _).symm s))

/-- The actual proper/open tensor map, in sectionwise direct-image coordinates,
carries the scalar adjunct of an arbitrary restriction-form arrow to compact support
of that arrow followed by the canonical restriction comparison.

Source: blueprint prop-coef-integral-dualizing.proof.md, paragraph 2; the argument
of lem-coef-dualizing-support-evaluation, step 4; Stacks 07A6, 0D6E and 0GL1.
(blueprint: lem-coef-compact-support-coefficient-mate-normalization).
Proof: use the canonical tensor/restriction adjunction at the source and target.
The proper coefficient map is the counit mate of scalar/pullback comparison.
The open coefficient map is the comparison of the two composite left adjoints,
whose common right adjoint is open pullback followed by scalar restriction.
Transpose the composite proper/open map. Mate pasting replaces the proper factor
by the K-injective-normalized direct-image restriction comparison, and replaces
the open factor by the exact sectionwise open restriction comparison. These are
the two factors defining sfCompactSupportRestriction. Naturality moves the scalar
unit at the input through these factors. The displayed direct-image model changes
are induced by equality of the constant-section structure maps, so preserve both
adjunction normalizations. Cancelling these model isomorphisms gives the asserted
unit equation. Put alpha equal to the scalar adjunct of s. Postcompose that equation
by restriction of F_B(alpha). Naturality of sfCompactSupportRestriction moves alpha to
F_A(Res_X(alpha)); functoriality combines this with F_A(eta_X). The adjunction identity
Res_X(alpha) after eta_X equals s gives the asserted formula. This applies to every
input in the unbounded ordinary derived category. No flatness,
constructibility or boundedness hypothesis is used; for the identity ring map both
sides are the unit-normalized identity comparison. -/
theorem compactSupportCoefficientMateNormalization
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    {m n : ℕ} (h : n ≤ m)
    {M : normalizedDVRDerived l E X m} {N : normalizedDVRDerived l E X n}
    (s : M ⟶ (scalarRestriction (compactSupportLevelQuotient l E m n h) X).obj N) :
    coefficientMateRestrictionArrow l E c h s =
      (sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (m + 1))).map s ≫
        (sfCompactSupportRestriction c (compactSupportLevelQuotient l E m n h)).hom.app N := by
  sorry

end WeilConjectures.DualizingSupportEvaluation
