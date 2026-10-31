/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FrobeniusCohomologyCoefficientCocycle

/-! # Rational cohomology coefficient cocycle

Source: Deligne, Weil II (1.1.1)(d), (1.1.14), coefficient extension and cohomology
(blueprint: lem-weil-frobenius-cohomology-rational-cocycle).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 128
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures
namespace CohomologyRealization
open AlgebraicallyClosedCoefficients (Index)
open GeneralAlgebraicallyClosedCoefficients (stageSystem)

attribute [local irreducible] Scheme.residueField HasDerivedCategory.standard

set_option allowUnsafeReducibility true in
attribute [local irreducible] frobeniusCohomologyCoefficientExtension
  frobeniusCohomologyRationalFunctor frobeniusCohomologyRationalScalar
  operationStageTransitionIso frobeniusCoefficientTower DerivedCategory.fieldScalarTower
attribute [local irreducible] rationalStage rationalComparison
  coefficientComparison fieldAssociator

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
  [IsSeparated Y₀.hom] (c₀ : Compactification Y₀.hom) (compact : Bool)

/-- The rational cohomology scalar mate obeys the stage associator equation.
Source: Deligne, Weil II (1.1.1)(d), (1.1.14), coefficient enlargement;
Step 1 of lem-weil-frobenius-cohomology-realization-transport
(blueprint: lem-weil-frobenius-cohomology-rational-cocycle).

Proof: on the integral operation models, expand the normalized scalar mate into
the direct-image mate, or the retained proper/open compact-support mates. Mate
pasting and the normalized scalar-adjunction units and counits identify their
two-step composite with the direct mate after the tensor associator. The total
limit and scalar restriction preserve this identity. Apply rational localization;
the component normalization of frobeniusCohomologyRationalOperationScalar fixes
these localized maps. The point-sections comparison has the same tower identity:
compute it on integral representatives, use tensor associativity and the
normalization of pointRationalFibreScalarIso, and detect equality through the
fully faithful size lift. Whisker the operation identity with point fibre and
compose with this point identity. Naturality moves the intermediate operation
mate through the point comparison. Finally insert the inverse
operationStageTransitionIso factors in rationalComparison; their canonical
coherence changes the raw scalar associator into the specified stage-system
associator. Include the finite-dimensional target into D(N). This gives the
stated equation on every object, including zero objects and repeated stages.
Writing H, F, c and q for the specified record fields, the predicate says
F_LN(q_EL,K) ≫ q_LN,T_EL(K) ≫ H_N(a_ELN,K) = c_ELN,H_E(K) ≫ q_EN,K.
This equation is in D(N). It uses only these four fields and ignores A and p,
so the final scalar-and-size extension into Ω does not enter the equation. -/
theorem rationalComparison_cocycle :
    factorRationalCocycle (bCategory := coefficientDerivedCategoryFamily.{u, v} l Ω)
      (realizationParts D l hl Y₀ Ω c₀ compact) := by sorry

end CohomologyRealization
end WeilConjectures
