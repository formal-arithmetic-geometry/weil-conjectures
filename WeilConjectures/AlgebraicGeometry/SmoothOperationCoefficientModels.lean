/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurFrameworkPbcCoefficientCategoryComparison
public import WeilConjectures.AlgebraicGeometry.RationalScalarComparisonIdentification
public import WeilConjectures.AlgebraicGeometry.PbcDescentFunctors
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Whiskering

/-! # Identification of smooth operations on common coefficient stages

Source: smooth-purity transport, Step 2, common-stage morphisms and inverse equations
(blueprint: def-pur-smooth-operation-coefficient-models).

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

/-- The two actual framework operations, indexed by false (twisted pullback) and
true (exceptional inverse image). Source: smooth-purity transport Step 2
(blueprint: def-pur-smooth-operation-coefficient-models). -/
def finiteOperation (exceptional : Bool) (E : Padic.FiniteCoefficientFields l Ω) :
    GeneralAlgebraicallyClosedCoefficients.Stage l Ω Y E ⥤
      GeneralAlgebraicallyClosedCoefficients.Stage l Ω X E :=
  if exceptional then
    (S.ring.operation (integralExceptionalCompactification D f)
      (.rational (ConstructibleExceptionalCoefficients.commonField.{u, v} l Ω E))).G
  else RationalSmoothPurityCanonical.rationalSource l
    (AlgebraicallyClosedCoefficients.Coefficient.{max u v} l Ω E) f d

/-- The actual common-stage operation, including the literal tensor object formula.
Source: smooth-purity transport Step 2
(blueprint: def-pur-smooth-operation-coefficient-models). -/
def commonOperation (exceptional : Bool) :
    generalAlgebraicallyClosedConstructibleCategory l Ω Y ⥤
      generalAlgebraicallyClosedConstructibleCategory l Ω X :=
  if exceptional then
    (S.ring.operation (integralExceptionalCompactification D f) .closed).G
  else RationalSmoothPurityCanonical.commonSource l Ω f d

/-- The finite comparison equivalence on the named framework stage.
Source: finite coefficient comparison (blueprint:
def-pur-smooth-operation-coefficient-models). -/
def stageEquivalence (W : Scheme.{max u v}) [IsNoetherian W]
    [Fact (∃ n : ℕ, topologicalKrullDim W ≤ n)]
    [Fact (∀ w : W, IsUnit (l : W.presheaf.stalk w))]
    (J : FdCoefficientComparison l Ω W) (E : Padic.FiniteCoefficientFields l Ω) :
    GeneralAlgebraicallyClosedCoefficients.Stage l Ω W E ≌ pbcStageCategory l Ω W E :=
  (J.stage E).rational

attribute [local irreducible] stageEquivalence

attribute [local irreducible] finiteOperation

/-- Change only the two presentations of an operation, using specified equivalences.
Source: finite coefficient identification (blueprint:
def-pur-smooth-operation-coefficient-models). -/
def conjugate {A B C E : Type w}
    [Category.{z} A] [Category.{z} B]
    [Category.{z} C] [Category.{z} E]
    (JA : A ≌ B) (JC : C ≌ E) (F : A ⥤ C) : B ⥤ E :=
  JA.inverse ⋙ F ⋙ JC.functor

/-- The unit-normalized finite presentation comparison.
Source: finite coefficient identification (blueprint:
def-pur-smooth-operation-coefficient-models). -/
def conjugateIso {A B C E : Type w}
    [Category.{z} A] [Category.{z} B]
    [Category.{z} C] [Category.{z} E]
    (JA : A ≌ B) (JC : C ≌ E) (F : A ⥤ C) :
    F ⋙ JC.functor ≅ JA.functor ⋙ conjugate JA JC F :=
  (Functor.leftUnitor _).symm ≪≫ isoWhiskerRight JA.unitIso _ ≪≫
    Functor.associator _ _ _

attribute [local irreducible] conjugate conjugateIso

/-- The same localized integral operation in the PBC presentation.
Source: finite coefficient identification (blueprint:
def-pur-smooth-operation-coefficient-models). -/
def pbcOperation (exceptional : Bool) (E : Padic.FiniteCoefficientFields l Ω) :
    pbcStageCategory l Ω Y E ⥤ pbcStageCategory l Ω X E :=
  conjugate (stageEquivalence l Ω Y JY E) (stageEquivalence l Ω X JX E)
    (finiteOperation l Ω D hl f d S exceptional E)

/-- The identity-induced finite comparison r, retaining the equivalence unit.
Source: finite coefficient identification (blueprint:
def-pur-smooth-operation-coefficient-models). -/
def finiteComparison (exceptional : Bool) (E : Padic.FiniteCoefficientFields l Ω) :
    finiteOperation l Ω D hl f d S exceptional E ⋙ (stageEquivalence l Ω X JX E).functor ≅
      (stageEquivalence l Ω Y JY E).functor ⋙
        pbcOperation l Ω D hl f d S JX JY exceptional E :=
  conjugateIso (stageEquivalence l Ω Y JY E) (stageEquivalence l Ω X JX E)
    (finiteOperation l Ω D hl f d S exceptional E)

/-- The finite comparison evaluated at its actual framework object.
Source: finite coefficient identification (blueprint:
def-pur-smooth-operation-coefficient-models). -/
@[irreducible] def finiteComparisonAt (exceptional : Bool)
    (E : Padic.FiniteCoefficientFields l Ω)
    (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω Y E) :
    (stageEquivalence l Ω X JX E).functor.obj
        ((finiteOperation l Ω D hl f d S exceptional E).obj K) ≅
      (pbcOperation l Ω D hl f d S JX JY exceptional E).obj
        ((stageEquivalence l Ω Y JY E).functor.obj K) :=
  (finiteComparison l Ω D hl f d S JX JY exceptional E).app K

attribute [local irreducible] pbcOperation finiteComparison


end WeilConjectures.CommonStageSmoothOperationIdentification
