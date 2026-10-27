/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G6
-/
module

public import Sheaf.Paper.PointTransportConeComparisonDescent
public import Sheaf.Paper.SfIntegralConstructible

/-! # Completeness of the actual quotient-cone augmentation at the point
Source: blueprint rational Frobenius integral model, clause (3), completion step.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
namespace WeilConjectures

attribute [local instance 5000] integralTowerHasDerivedCategory
attribute [local irreducible] CategoryTheory.Limits.limit
  completedIntegralCoefficientSheafUnrestricted completedIntegralCommRingSheafUnrestricted
  HasDerivedCategory.standard HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions DerivedCategory.Q
  integralDerivedPullback integralDerivedPullbackComparison
  Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  unrestrictedTowerUnit unrestrictedIntegralTransition

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The zero-shifted-coordinate augmentation into the actual quotient tower is
invertible after localization on good integral constructible representatives.
Source: blueprint main-20261015, prop-trf-rational-frobenius-integral-model.proof.md,
clause (3), realization steps 3--4
(blueprint: lem-trf-point-reduction-augmentation-complete).

Proof: use the normalized identity-extension completion comparison of
pointSectionsCompletionCone. Identify the identity-extension finite coefficient
presentation with ordinary quotient reduction by the canonical balanced tensor
identification: on every generator it sends 1 tensor x to 1 tensor x. Naturality
of reduction makes these level identifications an isomorphism of whole strict
towers, including their quotient transitions. Realize it by the diagonal map on
both cone coordinates. The composite of its sectionwise comparison with the
identity-extension completion unit has quotient units on the unshifted coordinate
and zero on the shifted coordinate. These two coordinates jointly determine a
map to the concrete Roos cone, so the composite is exactly PointTransportCone.augmentation.
Derived completeness makes the identity-extension unit invertible, and all the
other comparisons are isomorphisms. Thus this specified augmentation is invertible.
This also covers the zero complex and unbounded good representatives; no individual
finite evaluation is used to detect equality in the derived category. -/
theorem pointReductionAugmentation_isIso
    (hl : l ≠ D.p)
    (P : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
    (hP : sfIntegralConstructible l E (Spec (.of D.k)) (DerivedCategory.Q.obj P.obj)) :
    IsIso ((PointTransportCone.moduleQ l E).map
      (PointTransportCone.augmentation D l E P.obj)) := by
  sorry

end WeilConjectures
