/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.ConstructiblePullbackComparisonData

/-! # Constructible point comparison data

The unchanged point-realization definitions and canonical scalar components.
Source: Bhatt--Scholze 6.8.14(2)
(blueprint: def-a1-constructible-point-comparison-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u v uC vC uB vB uD vD uA vA

open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated AlgebraicGeometry

namespace WeilConjectures

-- Keep the point targets in their published small derived Hom universe when the chart API
-- imports the residue-lisse standard-size localization instance. This preference is file-local.
attribute [local instance 2000] HasDerivedCategory.ofIsGrothendieckAbelian

attribute [local irreducible] sfRationalStandardTStructure sfCommonStageStandardTStructure
  pointRationalFibre
  DerivedCategory.TStructure.t ModuleCat.extendScalars

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)

attribute [local irreducible] constructiblePullbackResidueUnits

open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)
open GeneralAlgebraicallyClosedCoefficients (Stage inclusion stageTransition)

/-- The rational point fibre, followed by its recorded fully faithful inclusion in
D(E). This is the given fibre functor, not a new evaluation construction.
Source: blueprint order 1509, clause 3
(blueprint: lem-a1-constructible-pullback-t-exact). -/
abbrev constructiblePointRationalRealization
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :=
  pointRationalFibre D l hl E ⋙ (DerivedCategory.pointFiniteDimensional E).ι

/-- The common-stage point fibre with its recorded faithful realization in D(Ω).
Source: blueprint order 1509, clause 4
(blueprint: lem-a1-constructible-pullback-t-exact). -/
abbrev constructiblePointCommonStageRealization
    (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω] :=
  pointQbarFibre D l hl Ω ⋙ DerivedCategory.pointFdQbarRealization l Ω

/-- Exact point evaluation, the natural point-fibre cohomology formula, and the
assertion that a pulled-back heart object has no nonzero-degree point cohomology.
The cohomology on D(E) is for its usual standard t-structure, so is the ordinary
cohomology module regarded as a degree-zero complex.
Source: Bhatt--Scholze Example 6.5.2, 6.8.11(3), 6.8.14(2)
(blueprint: lem-a1-constructible-pullback-t-exact). -/
def ConstructiblePointRationalComparison
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X : Scheme.{u}} [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    (x : Spec (.of D.k) ⟶ X) : Prop :=
  letI := constructiblePullbackResidueUnits D l hl X
  letI := constructiblePullbackResidueUnits D l hl (Spec (.of D.k))
  ∃ (d : ConstructibleRationalPullbackComparison D l hl E x)
    (f : ConstructiblePullbackComparison
      (sfRationalStandardTStructure l E (Spec (.of D.k)) D hl)
      (DerivedCategory.TStructure.t (C := ModuleCat.{u} E))
      (sfRationalHeartProperty l E (Spec (.of D.k)))
      (DerivedCategory.TStructure.t (C := ModuleCat.{u} E)).heart
      (constructiblePointRationalRealization D l hl E)),
    (∀ j : ℤ, ∃ γ :
        constructibleTruncationCohomology (sfRationalStandardTStructure l E X D hl) j ⋙
          rationalDerivedPullback l E x ⋙ constructiblePointRationalRealization D l hl E ≅
        rationalDerivedPullback l E x ⋙ constructiblePointRationalRealization D l hl E ⋙
          constructibleTruncationCohomology
            (DerivedCategory.TStructure.t (C := ModuleCat.{u} E)) j,
      ∀ K : sfRationalConstructibleCategory l E X,
        γ.app K = (constructiblePointRationalRealization D l hl E).mapIso
            ((d.cohomology j).app K) ≪≫
          (f.cohomology j).app ((rationalDerivedPullback l E x).obj K)) ∧
    ∀ (F : sfRationalHeart l E X) (j : ℤ), j ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} E) j).obj
        ((constructiblePointRationalRealization D l hl E).obj
          ((rationalDerivedPullback l E x).obj F.obj)))

/-- The same point-fibre clauses at the actual common-stage coefficient category.
The realization is fully faithful, hence expresses the isomorphism of fibre complexes.
Source: Bhatt--Scholze 6.8.14(2) and the common-stage convention
(blueprint: lem-a1-constructible-pullback-t-exact). -/
def ConstructiblePointCommonStageComparison
    (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {X : Scheme.{u}} [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    (x : Spec (.of D.k) ⟶ X) : Prop :=
  letI := constructiblePullbackResidueUnits D l hl X
  letI := constructiblePullbackResidueUnits D l hl (Spec (.of D.k))
  ∃ (d : ConstructibleCommonStagePullbackComparison D l hl Ω x)
    (f : ConstructiblePullbackComparison
      (sfCommonStageStandardTStructure l (Spec (.of D.k)) Ω D hl)
      (DerivedCategory.TStructure.t (C := ModuleCat.{u} Ω))
      (sfCommonStageHeartProperty l (Spec (.of D.k)) Ω)
      (DerivedCategory.TStructure.t (C := ModuleCat.{u} Ω)).heart
      (constructiblePointCommonStageRealization D l hl Ω)),
    (∀ j : ℤ, ∃ γ :
        constructibleTruncationCohomology (sfCommonStageStandardTStructure l X Ω D hl) j ⋙
          commonStageDerivedPullback l Ω x ⋙ constructiblePointCommonStageRealization D l hl Ω ≅
        commonStageDerivedPullback l Ω x ⋙ constructiblePointCommonStageRealization D l hl Ω ⋙
          constructibleTruncationCohomology
            (DerivedCategory.TStructure.t (C := ModuleCat.{u} Ω)) j,
      ∀ K : generalAlgebraicallyClosedConstructibleCategory l Ω X,
        γ.app K = (constructiblePointCommonStageRealization D l hl Ω).mapIso
            ((d.cohomology j).app K) ≪≫
          (f.cohomology j).app ((commonStageDerivedPullback l Ω x).obj K)) ∧
    ∀ (F : sfCommonStageHeart l X Ω) (j : ℤ), j ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} Ω) j).obj
        ((constructiblePointCommonStageRealization D l hl Ω).obj
          ((commonStageDerivedPullback l Ω x).obj F.obj)))

/-- Point comparison data at a finite stage, in the existing small coefficient model.
Source: Bhatt--Scholze 6.8.14(2); blueprint point-fibre clause
(blueprint: lem-a1-constructible-pullback-t-exact). -/
abbrev ConstructibleRationalPointData
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :=
  ConstructiblePullbackComparison
    (sfRationalStandardTStructure l E (Spec (.of D.k)) D hl)
    (DerivedCategory.TStructure.t (C := ModuleCat.{u} E))
    (sfRationalHeartProperty l E (Spec (.of D.k)))
    (DerivedCategory.TStructure.t (C := ModuleCat.{u} E)).heart
    (constructiblePointRationalRealization D l hl E)

/-- Common-stage point comparison data, with the actual fibre realization.
Source: Bhatt--Scholze 6.8.14(2); blueprint point-fibre clause
(blueprint: lem-a1-constructible-pullback-t-exact). -/
abbrev ConstructibleCommonStagePointData
    (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω] :=
  ConstructiblePullbackComparison
    (sfCommonStageStandardTStructure l (Spec (.of D.k)) Ω D hl)
    (DerivedCategory.TStructure.t (C := ModuleCat.{u} Ω))
    (sfCommonStageHeartProperty l (Spec (.of D.k)) Ω)
    (DerivedCategory.TStructure.t (C := ModuleCat.{u} Ω)).heart
    (constructiblePointCommonStageRealization D l hl Ω)

/-- The standard-t-structure comparison data for the recorded exact field extension.
Source: Bhatt--Scholze 6.8.14(2), exact scalar extension
(blueprint: lem-a1-constructible-pullback-t-exact). -/
abbrev ConstructibleFieldScalarData {E L : Type u} [Field E] [Field L] (a : E →+* L) :=
  ConstructiblePullbackComparison
    (DerivedCategory.TStructure.t (C := ModuleCat.{u} E))
    (DerivedCategory.TStructure.t (C := ModuleCat.{u} L))
    (DerivedCategory.TStructure.t (C := ModuleCat.{u} E)).heart
    (DerivedCategory.TStructure.t (C := ModuleCat.{u} L)).heart
    (DerivedCategory.fieldDerivedScalarExtension a)

/-- The finite-stage point square is exactly the recorded sections/scalar comparison,
with the full-subcategory inclusions and transition identification inserted.
Source: blueprint order 1509, point-section scalar comparison
(blueprint: lem-a1-constructible-pullback-t-exact). -/
def constructiblePointFiniteScalarBeta
    (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (E L : Index l Ω) (a : E ≤ L) :
    constructiblePointRationalRealization D l hl (Coefficient.{u} l Ω E) ⋙
        DerivedCategory.fieldDerivedScalarExtension
          (coefficientInclusion l Ω E L a).toRingHom ≅
      stageTransition l Ω (Spec (.of D.k)) E L a ⋙
        constructiblePointRationalRealization D l hl (Coefficient.{u} l Ω L) :=
  Functor.associator
      (pointRationalFibre D l hl (Coefficient.{u} l Ω E))
      (DerivedCategory.pointFiniteDimensional (Coefficient.{u} l Ω E)).ι
      (DerivedCategory.fieldDerivedScalarExtension
        (coefficientInclusion l Ω E L a).toRingHom) ≪≫
    Functor.isoWhiskerLeft (pointRationalFibre D l hl (Coefficient.{u} l Ω E))
      ((DerivedCategory.pointFiniteDimensional (Coefficient.{u} l Ω L)).liftCompιIso
        ((DerivedCategory.pointFiniteDimensional (Coefficient.{u} l Ω E)).ι ⋙
          DerivedCategory.fieldDerivedScalarExtension
            (coefficientInclusion l Ω E L a).toRingHom)
        (fun K ↦ DerivedCategory.fieldDerivedScalarExtension_preserves
          (coefficientInclusion l Ω E L a).toRingHom K.obj K.property)).symm ≪≫
    (Functor.associator (pointRationalFibre D l hl (Coefficient.{u} l Ω E))
      (DerivedCategory.pointFdScalarExtension (coefficientInclusion l Ω E L a).toRingHom)
      (DerivedCategory.pointFiniteDimensional (Coefficient.{u} l Ω L)).ι).symm ≪≫
    Functor.isoWhiskerRight
      (pointRationalFibreScalarIso D l hl (Coefficient.{u} l Ω E)
        (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L a)).symm
      (DerivedCategory.pointFiniteDimensional (Coefficient.{u} l Ω L)).ι ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerRight
      (operationStageTransitionIso l Ω (Spec (.of D.k)) E L a).symm _

/-- The recorded coefficient-model equivalence, with its source carrier explicit.
Source: blueprint common-stage coefficient convention; Shrink.algEquiv
(blueprint: lem-a1-constructible-pullback-t-exact). -/
def constructiblePointCoefficientMap
    (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (E : Index l Ω) : Coefficient.{u} l Ω E →+* E.val :=
  (Shrink.algEquiv (Padic l) E.val).toRingHom

/-- The actual common-stage fibre object's defining identification after realization.
Source: blueprint order 1509, clause 4; pointQbarFibre's defining object formula
(blueprint: lem-a1-constructible-pullback-t-exact). -/
def constructiblePointCommonStageObjectIso
    (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (E : Index l Ω) (K : Stage l Ω (Spec (.of D.k)) E) :
    (constructiblePointCommonStageRealization D l hl Ω).obj
        ((inclusion (l := l) (Ω := Ω) (Y := Spec (.of D.k)) E).obj K) ≅
      (DerivedCategory.fieldDerivedScalarExtension E.val.subtype).obj
        ((DerivedCategory.fieldDerivedScalarExtension
          (constructiblePointCoefficientMap l Ω E)).obj
            (((pointRationalFibre D l hl (Coefficient.{u} l Ω E)).obj K).obj)) :=
  (DerivedCategory.pointFdQbarRealization l Ω).mapIso
    (eqToIso ((pointQbarFibre_existsUnique D l hl Ω).exists.choose_spec.1
      ((inclusion (l := l) (Ω := Ω) (Y := Spec (.of D.k)) E).obj K)))

/-- The canonical finite-stage to common-stage point comparison component.
It first expands the field tensor tower, then uses the recorded fibre object formula.
Source: blueprint order 1509, clause 4, and Bhatt--Scholze 6.8.14(2)
(blueprint: lem-a1-constructible-pullback-t-exact). -/
def constructiblePointCommonStageScalarComponent
    (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (E : Index l Ω) (K : Stage l Ω (Spec (.of D.k)) E) :
    (DerivedCategory.fieldDerivedScalarExtension
        (E.val.subtype.comp (constructiblePointCoefficientMap l Ω E))).obj
          ((constructiblePointRationalRealization D l hl (Coefficient.{u} l Ω E)).obj K) ≅
      (constructiblePointCommonStageRealization D l hl Ω).obj
        ((inclusion (l := l) (Ω := Ω) (Y := Spec (.of D.k)) E).obj K) :=
  (DerivedCategory.fieldScalarTower (K := Coefficient.{u} l Ω E) (L := E.val)
    (M := Ω) (constructiblePointCoefficientMap l Ω E) E.val.subtype).symm.app
      (((pointRationalFibre D l hl (Coefficient.{u} l Ω E)).obj K).obj) ≪≫
    (constructiblePointCommonStageObjectIso D l hl Ω E K).symm

/-- The scalar compatibility of point cohomology, at finite extensions and from a
finite field to the closure. The latter beta is fixed by the actual fibre object
identity and the canonical field tensor tower map. Thus the Qbar point comparison
is the scalar extension of the finite-stage comparison, not an unrelated isomorphism.
Source: Bhatt--Scholze 6.8.14(2); point-sections scalar-extension convention
(blueprint: lem-a1-constructible-pullback-t-exact). -/
def ConstructiblePointScalarCompatibility
    (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω] : Prop :=
  ∃ (f : ∀ E : Index l Ω, ConstructibleRationalPointData D l hl (Coefficient.{u} l Ω E))
    (g : ConstructibleCommonStagePointData D l hl Ω),
    (∀ (E L : Index l Ω) (a : E ≤ L),
      ∃ (s : ConstructiblePullbackComparison
          (sfRationalStandardTStructure l (Coefficient.{u} l Ω E) (Spec (.of D.k)) D hl)
          (sfRationalStandardTStructure l (Coefficient.{u} l Ω L) (Spec (.of D.k)) D hl)
          (sfRationalHeartProperty l (Coefficient.{u} l Ω E) (Spec (.of D.k)))
          (sfRationalHeartProperty l (Coefficient.{u} l Ω L) (Spec (.of D.k)))
          (stageTransition l Ω (Spec (.of D.k)) E L a))
        (t : ConstructibleFieldScalarData (coefficientInclusion l Ω E L a).toRingHom),
        t.commShift = (inferInstance :
          (DerivedCategory.fieldDerivedScalarExtension
            (coefficientInclusion l Ω E L a).toRingHom).CommShift ℤ) ∧
        ConstructiblePullbackScalarSquare (f E) (f L) s t
          (constructiblePointFiniteScalarBeta D l hl Ω E L a)) ∧
    (∀ E : Index l Ω,
      ∃ (s : ConstructiblePullbackComparison
          (sfRationalStandardTStructure l (Coefficient.{u} l Ω E) (Spec (.of D.k)) D hl)
          (sfCommonStageStandardTStructure l (Spec (.of D.k)) Ω D hl)
          (sfRationalHeartProperty l (Coefficient.{u} l Ω E) (Spec (.of D.k)))
          (sfCommonStageHeartProperty l (Spec (.of D.k)) Ω)
          (inclusion (l := l) (Ω := Ω) (Y := Spec (.of D.k)) E))
        (t : ConstructibleFieldScalarData
          (E.val.subtype.comp (constructiblePointCoefficientMap l Ω E)))
        (β : constructiblePointRationalRealization D l hl (Coefficient.{u} l Ω E) ⋙
            DerivedCategory.fieldDerivedScalarExtension
              (E.val.subtype.comp (constructiblePointCoefficientMap l Ω E)) ≅
          inclusion (l := l) (Ω := Ω) (Y := Spec (.of D.k)) E ⋙
            constructiblePointCommonStageRealization D l hl Ω),
        t.commShift = (inferInstance :
          (DerivedCategory.fieldDerivedScalarExtension
            (E.val.subtype.comp (constructiblePointCoefficientMap l Ω E))).CommShift ℤ) ∧
        (∀ K : Stage l Ω (Spec (.of D.k)) E,
          β.app K = constructiblePointCommonStageScalarComponent D l hl Ω E K) ∧
        ConstructiblePullbackScalarSquare (f E) g s t β)


end WeilConjectures
