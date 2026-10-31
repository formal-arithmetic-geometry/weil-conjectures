/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothOperationCoefficientModels
public import WeilConjectures.AlgebraicGeometry.PurFrameworkPbcCoefficientCategoryComparison
public import WeilConjectures.AlgebraicGeometry.RationalScalarComparisonIdentification
public import WeilConjectures.AlgebraicGeometry.PbcDescentFunctors
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Whiskering

/-! # Identification of smooth operations on common coefficient stages

Source: smooth-purity transport, Step 2, common-stage morphisms and inverse equations
(blueprint: def-pur-smooth-operation-coefficient-comparisons).

The finite PBC operations are the specified localized integral operations transported
through the identity coefficient-presentation equivalences. The conclusion fixes
all comparison components, representative actions, shifts and transformation equations.
-/

@[expose] public noncomputable section
set_option Elab.async false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u v w z
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
  AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.CommonStageSmoothOperationIdentification
set_option allowUnsafeReducibility true
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.Stage
  pbcFiniteField pbcFiniteFieldField pbcFiniteFieldAlgebra
attribute [local irreducible] HasDerivedCategory.standard
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
  {X Y : Scheme.{max u v}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [sepX : IsSeparated (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [sepY : IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (d : ℕ) [smooth : SmoothOfRelativeDimension d f]
  (S : ConstructibleExceptionalCoefficients.System.{u, v} l Ω D hl (f := f))
  [IsNoetherian X] [IsNoetherian Y]
  [dX : Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
  [dY : Fact (∃ n : ℕ, topologicalKrullDim Y ≤ n)]
  [iX : Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
  [iY : Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y))]
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]
  (JX : FdCoefficientComparison l Ω X) (JY : FdCoefficientComparison l Ω Y)

attribute [local semireducible] finiteOperation
/-- The actual strict source scalar comparison, with the stage-system-to-tensor maps
at both endpoints. Source: smooth-purity transport Step 2, strict source comparison
(blueprint: def-pur-smooth-operation-coefficient-comparisons). -/
@[irreducible] def strictComparison (exceptional : Bool)
    {E F : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F)
    (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω Y E) :
    ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).T h).obj
        ((finiteOperation l Ω D hl f d S exceptional E).obj K) ≅
      (finiteOperation l Ω D hl f d S exceptional F).obj
        (((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Y).T h).obj K) :=
  match exceptional with
  | true =>
    (operationStageTransitionIso l Ω X E F h).app _ ≪≫
      (S.fields.rationalComparison (integralExceptionalCompactification D f)
        (ConstructibleExceptionalCoefficients.commonField.{u, v} l Ω E)
        (ConstructibleExceptionalCoefficients.commonField.{u, v} l Ω F)
        (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω E F h)).b.app K ≪≫
      (finiteOperation l Ω D hl f d S true F).mapIso
        ((operationStageTransitionIso l Ω Y E F h).app K).symm
  | false =>
    (operationStageTransitionIso l Ω X E F h).app _ ≪≫
      RationalSmoothPurityCanonical.sourceScalar l
        (AlgebraicallyClosedCoefficients.Coefficient.{max u v} l Ω E)
        (AlgebraicallyClosedCoefficients.Coefficient.{max u v} l Ω F)
        (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω E F h) f d K ≪≫
      (finiteOperation l Ω D hl f d S false F).mapIso
        ((operationStageTransitionIso l Ω Y E F h).app K).symm


/-- The specified completeness normalization of the actual common-stage object.
Source: smooth-purity transport Step 2, normalization before descent
(blueprint: def-pur-smooth-operation-coefficient-comparisons). -/
@[irreducible] def objectComparison (exceptional : Bool)
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω Y) :
    (commonOperation l Ω D hl f d S exceptional).obj K ≅
      ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).ι K.stage).obj
        ((finiteOperation l Ω D hl f d S exceptional K.stage).obj K.obj) :=
  match exceptional with
  | false => RationalSmoothPurityCanonical.commonSourceComparison l Ω f d K
  | true =>
    ((S.common.commonComparison (integralExceptionalCompactification D f) K.stage).b.app
      K.obj).symm

attribute [local irreducible] finiteOperation commonOperation


end WeilConjectures.CommonStageSmoothOperationIdentification
