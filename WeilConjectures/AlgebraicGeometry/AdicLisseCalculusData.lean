/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorHom
public import WeilConjectures.AlgebraicGeometry.PbcQbarCategory
public import WeilConjectures.AlgebraicGeometry.LisseAdicFiberFunctors
public import WeilConjectures.AlgebraicGeometry.CurveMiddleExtension
public import WeilConjectures.AlgebraicGeometry.CompletedCoefficientPresentationTransport
public import WeilConjectures.AlgebraicGeometry.IntegralTStructure
public import WeilConjectures.AlgebraicGeometry.PointSectionsScalarExtension
public import WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.LinearAlgebra.Dual.Defs

/-! # Normalized models for adic lisse cohomology

These are the unchanged model definitions formerly declared in
`AdicLisseCohomologyCalculus`. Source: Bhatt--Scholze 6.8.1--6.8.15.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.Scheme

variable (l : ℕ) [Fact l.Prime] (Qbar : Type (u + 1)) [Field Qbar]
  [Algebra ℚ_[l] Qbar] [IsAlgClosure ℚ_[l] Qbar] (X : Scheme.{u})
  [IsNoetherian X] [X.IsSeparated]
  [hDim : Fact (∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))]
  [hInv : Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]


/-- The coefficient prime is invertible in residue fields because it is a unit in each
stalk. This supplies the interface used by the recorded lisse and completed operations.
Source: scheme coefficient conventions
(blueprint: lem-per-adic-lisse-cohomology-calculus). -/
noncomputable instance adicCalculusPrimeInvertible (x : X) :
    Invertible (l : X.residueField x) :=
  (Eq.mp (congrArg IsUnit (map_natCast (X.residue x).hom l))
    ((hInv.out x).map (X.residue x).hom)).invertible

/-- Integral localization followed by the recorded common-stage inclusion.
Source: Bhatt--Scholze 6.8.14 (blueprint: lem-per-adic-lisse-cohomology-calculus). -/
def adicCalculusIntegralInclusion (E : Padic.FiniteCoefficientFields l Qbar) :
    pbcIntegralStage.{u, u + 1} l Qbar X E ⥤ pbcQbarCategory.{u + 1, u} l Qbar X :=
  pbcStageLocalization.{u, u + 1} l Qbar X E ⋙ (pbcScalarSystem l Qbar X hDim.out hInv.out).ι E

/-- Integral cohomology, retained as a degree-zero object of the completed category.
Source: Bhatt--Scholze 6.8.11; localized t-structure
(blueprint: lem-per-adic-lisse-cohomology-calculus). -/
def adicCalculusIntegralCohomology (E : Padic.FiniteCoefficientFields l Qbar) (a : ℤ) :
    pbcIntegralStage.{u, u + 1} l Qbar X E ⥤ pbcIntegralStage.{u, u + 1} l Qbar X E :=
  shiftFunctor _ a ⋙ (pbcIntegralTStructure.{u} X l (pbcFiniteField.{u} l Qbar E)).homology₀ ⋙
    ObjectProperty.ι _

/-- The actual inverse-limit realization; the identity direct image in the existing
level functor identifies the étale site with itself before passage to the pro-étale site.
Source: Bhatt--Scholze 6.8.4(1),(4)
(blueprint: lem-per-adic-lisse-cohomology-calculus). -/
def adicCalculusIntegralRealization (E : Padic.FiniteCoefficientFields l Qbar) :
    LisseIntegralSheaf l E.val X ⥤ pbcAmbientStage.{u, u + 1} l Qbar X E :=
  ObjectProperty.ι _ ⋙
    (Functor.whiskeringRight _ _ _).obj (middleExtensionLevelFunctor l Qbar E (𝟙 X)) ⋙
    lim ⋙ DerivedCategory.singleFunctor
      (pbcModules X (pbcAdicCompletion X (pbcStageDatum.{u} l Qbar E))) 0

/-- Restriction to the exact bounded constructible complete category. The argument is
only the membership proof; all object and map data are the specified inverse limit.
Source: Bhatt--Scholze 6.8.4,6.8.11
(blueprint: lem-per-adic-lisse-cohomology-calculus). -/
def adicCalculusIntegralRealizationLift (E : Padic.FiniteCoefficientFields l Qbar)
    (h : ∀ F : LisseIntegralSheaf l E.val X,
      PbcIsBoundedConstructibleComplete X (pbcStageDatum.{u} l Qbar E)
        ((adicCalculusIntegralRealization l Qbar X E).obj F)) :
    LisseIntegralSheaf l E.val X ⥤ pbcIntegralStage.{u, u + 1} l Qbar X E :=
  ObjectProperty.lift _ (adicCalculusIntegralRealization l Qbar X E) h

/-- The canonical integral coefficient-presentation transport, restricted by a membership
proof. There is no independent choice of a coefficient model or of a map.
Source: Bhatt--Scholze 6.8.11; completed coefficient presentation transport
(blueprint: lem-per-adic-lisse-cohomology-calculus). -/
def adicCalculusIntegralModel (E : Padic.FiniteCoefficientFields l Qbar)
    (h : ∀ K : pbcIntegralStage.{u, u + 1} l Qbar X E,
      sfIntegralConstructible l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Qbar E) X
        ((purCoefficientModel.{u} l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Qbar E) X).functor.obj K.obj)) :
    pbcIntegralStage.{u, u + 1} l Qbar X E ⥤
      sfIntegralConstructibleCategory l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Qbar E) X :=
  ObjectProperty.lift _
    (pbcStageInclusion.{u, u + 1} l Qbar X E ⋙
      (purCoefficientModel.{u} l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Qbar E) X).functor) h

/-- Geometric fibres use completed derived pullback, degree-zero cohomology, and sections
on the geometric point; only then are coefficients extended to the algebraic closure.
In particular this definition does not commute an ordinary stalk with an inverse limit.
Source: Bhatt--Scholze 6.8.4 and the normalized point-sections construction
(blueprint: lem-per-adic-lisse-cohomology-calculus). -/
def adicCalculusIntegralFiber (E : Padic.FiniteCoefficientFields l Qbar)
    (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (.of k) ⟶ X) :
    pbcIntegralStage.{u, u + 1} l Qbar X E ⥤ ModuleCat.{u + 1} Qbar :=
  pbcStageInclusion.{u, u + 1} l Qbar X E ⋙
    pbcActualCompletedPull x (pbcStageDatum.{u} l Qbar E) ⋙
    (purCoefficientModel.{u} l (pbcFiniteField.{u} l Qbar E) (Spec (.of k))).functor ⋙
    DerivedCategory.homologyFunctor
      (integralTowerModules.{u, u} l (pbcFiniteField.{u} l Qbar E) (Spec (.of k))) 0 ⋙
    pointCompletedSections k l (pbcFiniteField.{u} l Qbar E) ⋙
    ModuleCat.extendScalars
      (E.val.subtype.comp ((Shrink.algEquiv ℚ_[l] E.val).toRingHom.comp
        (Padic.coefficientExtensionIntegers l (pbcFiniteField.{u} l Qbar E)).subtype))

/-- Transport of the recorded completed common-stage tensor to the exact pbc presentation.
Source: Bhatt--Scholze 6.8.15
(blueprint: lem-per-adic-lisse-cohomology-calculus). -/
def adicCalculusTensor
    (C : pbcQbarCategory.{u + 1, u} l Qbar X ≌
      generalAlgebraicallyClosedConstructibleCategory l Qbar X) :
    pbcQbarCategory.{u + 1, u} l Qbar X × pbcQbarCategory.{u + 1, u} l Qbar X ⥤
      pbcQbarCategory.{u + 1, u} l Qbar X :=
  (C.functor.prod C.functor) ⋙ commonStageDerivedTensor l Qbar X ⋙ C.inverse

/-- Normalized models for the adic lisse calculation.
The integral normalization fixes the coefficient presentation, cohomology, realization,
and fibres; global functoriality expresses independence of representatives and finite
coefficient extension in the recorded common-stage localizations.
Source: Bhatt--Scholze 6.8.1--6.8.15 and the lisse tensor argument in the blueprint
(blueprint: lem-per-adic-lisse-cohomology-calculus). -/
structure AdicLisseCalculusModels where
  /-- The existing coefficient model preserves the exact integral predicate. -/
  model_mem : ∀ (E : Padic.FiniteCoefficientFields l Qbar)
    (K : pbcIntegralStage.{u, u + 1} l Qbar X E),
    sfIntegralConstructible l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Qbar E) X
      ((purCoefficientModel.{u} l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Qbar E) X).functor.obj K.obj)
  /-- The equivalence of the two recorded coefficient presentations. -/
  comparison : pbcQbarCategory.{u + 1, u} l Qbar X ≌
    generalAlgebraicallyClosedConstructibleCategory l Qbar X
  /-- At every integral stage the equivalence is the specified coefficient transport. -/
  comparison_integral : ∀ E : Padic.FiniteCoefficientFields l Qbar,
    adicCalculusIntegralInclusion l Qbar X E ⋙ comparison.functor ≅
      adicCalculusIntegralModel l Qbar X E (model_mem E) ⋙
        sfRationalConstructibleLocalization l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Qbar E) X ⋙
          (GeneralAlgebraicallyClosedCoefficients.stageSystem.{u, u + 1} l Qbar X).ι E
  /-- Inverse-limit lisse realizations have uniform constructible reduction towers. -/
  realization_mem : ∀ (E : Padic.FiniteCoefficientFields l Qbar)
    (F : LisseIntegralSheaf l E.val X),
    PbcIsBoundedConstructibleComplete X (pbcStageDatum.{u} l Qbar E)
      ((adicCalculusIntegralRealization l Qbar X E).obj F)
  /-- Realization on the coefficient-localized adic lisse category. -/
  realization : LisseAlgebraicSheaf l X Qbar ⥤ pbcQbarCategory.{u + 1, u} l Qbar X
  /-- Its values are the integral inverse-limit realizations, rationalized. -/
  realization_integral : ∀ (E : Padic.FiniteCoefficientFields l Qbar)
    (F : LisseIntegralSheaf l E.val X),
    realization.obj (lisseAlgebraicOfModel l X Qbar E ⟨F⟩) ≅
      (adicCalculusIntegralInclusion l Qbar X E).obj
        ((adicCalculusIntegralRealizationLift l Qbar X E (realization_mem E)).obj F)
  /-- Morphisms are the prescribed rationalization of integral morphisms. -/
  realization_map : ∀ (E : Padic.FiniteCoefficientFields l Qbar)
    (F G : LisseIntegralSheaf l E.val X) (a : E.val) (f : F ⟶ G),
    realization.map (lisseAlgebraicModelMap l X Qbar E
        (F := ⟨F⟩) (H := ⟨G⟩) (TensorProduct.tmul _ a f)) =
      (realization_integral E F).hom ≫
        pbcQbarScalarAction l Qbar X (E.val.subtype a)
          ((adicCalculusIntegralInclusion l Qbar X E).map
            ((adicCalculusIntegralRealizationLift l Qbar X E (realization_mem E)).map f)) ≫
        (realization_integral E G).inv
  /-- Adic cohomology is defined on the coefficient quotient, in every integer degree. -/
  cohomology : ℤ → pbcQbarCategory.{u + 1, u} l Qbar X ⥤ pbcQbarCategory.{u + 1, u} l Qbar X
  /-- It is exactly integral cohomology followed by rationalization at each finite field. -/
  cohomology_integral : ∀ (E : Padic.FiniteCoefficientFields l Qbar) (a : ℤ),
    adicCalculusIntegralInclusion l Qbar X E ⋙ cohomology a ≅
      adicCalculusIntegralCohomology l Qbar X E a ⋙
        adicCalculusIntegralInclusion l Qbar X E
  /-- Lisse realization is in degree zero, including the zero-rank case. -/
  realization_cohomology : ∀ (L : LisseAlgebraicSheaf l X Qbar),
    (cohomology 0).obj (realization.obj L) ≅ realization.obj L
  /-- All other cohomology of a lisse realization vanishes. -/
  realization_vanishing : ∀ (L : LisseAlgebraicSheaf l X Qbar) (a : ℤ), a ≠ 0 →
    IsZero ((cohomology a).obj (realization.obj L))
  /-- The geometric fibre on the coefficient quotient. -/
  fiber : ∀ (k : Type u) [Field k] [IsAlgClosed k] (_x : Spec (.of k) ⟶ X),
    pbcQbarCategory.{u + 1, u} l Qbar X ⥤ ModuleCat.{u + 1} Qbar
  /-- At each finite stage this is completed pullback followed by point sections. -/
  fiber_integral : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (.of k) ⟶ X)
    (E : Padic.FiniteCoefficientFields l Qbar),
    adicCalculusIntegralInclusion l Qbar X E ⋙ fiber k x ≅
      adicCalculusIntegralFiber l Qbar X E k x
  /-- On lisse sheaves it agrees with the already recorded adic fibre functor. -/
  fiber_lisse : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (.of k) ⟶ X),
    realization ⋙ fiber k x ≅ lisseAlgebraicFiberFunctor l X x Qbar

end AlgebraicGeometry.Scheme
