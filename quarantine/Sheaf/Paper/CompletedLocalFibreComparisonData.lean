/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q38
-/
module

public import Sheaf.Paper.ClassicalLocalFrobeniusData
public import Sheaf.AlgebraicGeometry.ProEtaleComparisonStalk
public import Sheaf.Paper.LissePointNormalization

/-! # Classical realization and every local Frobenius period

Source: Bhatt--Scholze, Proposition 6.8.4(1),(4), Remark 6.8.15;
blueprint real-mixed-by-curves, first paragraph
(blueprint: def-zl-completed-local-fibre-comparison-data).

The classical factors use the existing finite-etale paths and the actual
inverse-limit/rationalized automorphism fibre comparison. Positive exponents are
indexed by n+1, as in the published local Frobenius construction.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open Opposite
open scoped TensorProduct ChangeOfRings
namespace WeilConjectures.ClassicalLocalFrobenius

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type (u + 1)) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
  [IsSeparated Y₀.hom]
  [hUnits : Fact (∀ x : (D.geometricFiber Y₀).left,
    IsUnit (l : (D.geometricFiber Y₀).left.presheaf.stalk x))]
  (R : ZlClassicalRealization D l hl Ω Y₀)

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The finite model supplied in the pinning field of this very realization datum.
Source: BS 6.8.4(1),(4), 6.8.15; blueprint proof step 1
(blueprint: def-zl-completed-local-fibre-comparison-data). -/
def pinnedModels (E : Padic.FiniteCoefficientFields l Ω) :
    ZlClassicalPullbackModels D l hl Ω Y₀ E :=
  (R.pullback_pinning E).choose

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The same finite-stage realization isomorphism as in the Frobenius pinning equation.
Source: blueprint proof step 1 (blueprint: def-zl-completed-local-fibre-comparison-data). -/
def pinnedStage (E : Padic.FiniteCoefficientFields l Ω) :
    zlClassicalModel D l Ω Y₀ E ⋙ R.functor ≅
      (pinnedModels l Ω D hl Y₀ R E).finite ⋙
        GeneralAlgebraicallyClosedCoefficients.inclusion E :=
  (R.pullback_pinning E).choose_spec.choose_spec.2.choose_spec.2.choose

attribute [irreducible] pinnedModels pinnedStage

/-- Ordinary sections of the realized finite model after geometric inverse image.
Source: BS 6.8.14(2), 6.8.15
(blueprint: def-zl-completed-local-fibre-comparison-data). -/
def finiteSections (E : Padic.FiniteCoefficientFields l Ω)
    (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) :=
  (pinnedModels l Ω D hl Y₀ R E).finite ⋙
    (pinnedModels l Ω D hl Y₀ R E).realization.sheaf D l hl
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) ⋙
    LisseRealization.ordinaryPull l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) x ⋙
    LisseRealization.sections D l hl
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) ⋙
    ModuleCat.extendScalars (LocalFrobeniusLarge.embedding l Ω E)

/-- Inclusion of the normalized finite-stage point fibre into the fibre of R(M).
Source: BS 6.8.4(4); blueprint proof step 1
(blueprint: def-zl-completed-local-fibre-comparison-data). -/
def fromFinite (E : Padic.FiniteCoefficientFields l Ω)
    (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left)
    (F : AlgebraicGeometry.ProEtale.CompletedLisse.RawRational l
      (zlCompletedBase D l Ω Y₀ E)) :=
  (LocalFrobeniusLarge.pointFibre D l hl Ω).map
    (@LocalFrobeniusLarge.pullbackStage l _ Ω _ _ _ _ _ x
      (frobeniusPointPrimeInvertible D l hl) (sfWeilPrimeInvertible D l hl Y₀)
      ((GeneralAlgebraicallyClosedCoefficients.inclusion E).obj
        ((pinnedModels l Ω D hl Y₀ R E).finite.obj F))).inv ≫
  (LocalFrobeniusLarge.stalk D l hl Ω Y₀ x).map
    ((pinnedStage l Ω D hl Y₀ R E).inv.app F)

/-- The actual germ map for ordinary rational module inverse image.
Source: Stacks 03Q1; BS 6.8.15
(blueprint: def-zl-completed-local-fibre-comparison-data). -/
def sectionGerm (E : Padic.FiniteCoefficientFields l Ω)
    (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left)
    (M : LisseRealization.Modules D l hl
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)
      (zlRealizationBase D l hl Y₀)) (U : (D.geometricFiber Y₀).left.ProEt)
    (z : Spec (.of D.k) ⟶ U.left) (hz : z ≫ U.hom = x)
    (v : M.val.obj (op U)) :=
  ((LisseRealization.ordinaryPull l
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) x).obj M).val.map
      (MorphismProperty.Over.homMk
        (A := ProEt.mk (𝟙 (Spec (.of D.k))))
        (B := (proEtaleBaseChange x).obj U) (pullback.lift z (𝟙 _) (by simpa using hz))
        (pullback.lift_snd _ _ _) trivial).op
    (ContinuousRational.moduleUnit x
      (LisseRealization.coefficientPull l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) x) M U v)

/-- The etale/pro-etale finite-level stalk comparison with its canonical germ prescription.
Source: Stacks 03Q1; BS 5.1.5
(blueprint: def-zl-completed-local-fibre-comparison-data). -/
def finiteStalkComparison
    (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) :=
  (Scheme.proEtale_comparison_stalk (D.geometricFiber Y₀).left D.k x).2.1.choose

/-- A completed local section represents v precisely when every finite stalk projection
is its reduction germ. This tests an inverse limit, never an arbitrary pro-etale stalk.
Source: BS 6.8.4(1),(4); blueprint proof steps 1,3
(blueprint: def-zl-completed-local-fibre-comparison-data). -/
def RepresentsCompletedGerm (E : Padic.FiniteCoefficientFields l Ω)
    (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left)
    (F : AlgebraicGeometry.ProEtale.CompletedLisse.RawRational l
      (zlCompletedBase D l Ω Y₀ E))
    (U : (D.geometricFiber Y₀).left.ProEt)
    (z : Spec (.of D.k) ⟶ U.left) (hz : z ≫ U.hom = x)
    (v : ((pinnedModels l Ω D hl Y₀ R E).completed.equivalence.inverse.obj
      ⟨F.obj.integral, F.property⟩).obj.val.obj (op U))
    (w : lisseIntegralFiber l E.val (D.geometricFiber Y₀).left x F.obj.integral) : Prop :=
  ∀ j : ℕ,
    ((pointSmallEtale x).ulift.{u + 1}.sheafFiberCompIso
      (forget₂ (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E.val))
        AddCommGrpCat)).inv.app (F.obj.integral.obj.obj (op j))
      (limit.π (F.obj.integral.obj ⋙ (pointSmallEtale x).ulift.{u + 1}.sheafFiber)
        (op j) w) =
    ((pointSmallEtale x).uliftSheafFiberIso AddCommGrpCat.{u + 1}).inv.app
      ((AlgebraicGeometry.ProEtale.CompletedLisse.etaleDiagram l
        (zlCompletedBase D l Ω Y₀ E) ⟨F.obj.integral, F.property⟩).obj (op j))
    ((finiteStalkComparison D Y₀ x).hom.app
      ((AlgebraicGeometry.ProEtale.CompletedLisse.etaleDiagram l
        (zlCompletedBase D l Ω Y₀ E) ⟨F.obj.integral, F.property⟩).obj (op j))
      (colimit.ι
        (proEtaleGeometricStalkDiagram x
          ((AlgebraicGeometry.ProEtale.CompletedLisse.proEtaleDiagram l
            (zlCompletedBase D l Ω Y₀ E) ⟨F.obj.integral, F.property⟩).obj (op j)))
        (op (StructuredArrow.mk (Y := U) (Over.homMk z hz)))
        ((((pinnedModels l Ω D hl Y₀ R E).completed.completion
          ⟨F.obj.integral, F.property⟩).app (op j)).hom.app (op U) v)))

attribute [irreducible] fromFinite finiteStalkComparison RepresentsCompletedGerm

/-- A rationalized completed section in the SAME finite-stage sheaf realization.
Source: BS 6.8.4(4); blueprint proof step 1
(blueprint: def-zl-completed-local-fibre-comparison-data). -/
def completedSection (E : Padic.FiniteCoefficientFields l Ω)
    (F : AlgebraicGeometry.ProEtale.CompletedLisse.RawRational l
      (zlCompletedBase D l Ω Y₀ E)) (U : (D.geometricFiber Y₀).left.ProEt)
    (b : E.val)
    (v : ((pinnedModels l Ω D hl Y₀ R E).completed.equivalence.inverse.obj
      ⟨F.obj.integral, F.property⟩).obj.val.obj (op U)) :=
  ((pinnedModels l Ω D hl Y₀ R E).sheaf.inv.app F).hom.app (op U)
    (((pinnedModels l Ω D hl Y₀ R E).completed.rationalObject F).inv.val.app (op U)
      (completedAdicChangeTensor (D.geometricFiber Y₀).left
        ((pinnedModels l Ω D hl Y₀ R E).completed.coefficientIso.inv ≫
          AlgebraicGeometry.ProEtale.lisseIntegerToFieldSized l E.val (D.geometricFiber Y₀).left)
        ((pinnedModels l Ω D hl Y₀ R E).completed.equivalence.inverse.obj
          ⟨F.obj.integral, F.property⟩).obj (op U)
        (AlgebraicGeometry.ProEtale.lisseFieldConstantSized l E.val
          (D.geometricFiber Y₀).left (op U) b) v))

-- Retain the existing implicit algebraic-closure parameter.
set_option linter.unusedSectionVars false in
/-- Carrier lift commutes with the actual Ω tensor by a specified pure-tensor map.
Source: Weil II (1.1.1)d), blueprint coefficient-size convention
(blueprint: def-zl-completed-local-fibre-comparison-data).
Proof: send a tensor v to a tensor up v and send a tensor up v back to a tensor v.
These respect all balanced relations. The formulas are inverse on tensor generators,
and commute with every coefficient-linear map, which also gives uniqueness. -/
theorem stageLift_existsUnique (E : Padic.FiniteCoefficientFields l Ω) :
    ∃! e : ModuleCat.extendScalars.{u, u + 1, u}
        (LocalFrobeniusLarge.embedding l Ω E) ≅
        ModuleCat.uliftFunctor.{u + 1, u}
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) ⋙
        ModuleCat.extendScalars.{u, u + 1, u + 1}
          (LocalFrobeniusLarge.embedding l Ω E),
      ∀ (V : ModuleCat.{u} (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E))
        (a : Ω) (v : V),
        e.hom.app V (a ⊗ₜ[AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E,
          LocalFrobeniusLarge.embedding l Ω E] v) =
        a ⊗ₜ[AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E,
          LocalFrobeniusLarge.embedding l Ω E] ULift.up v := by
  let := (LocalFrobeniusLarge.embedding l Ω E).toAlgebra
  let e : ModuleCat.extendScalars.{u, u + 1, u}
      (LocalFrobeniusLarge.embedding l Ω E) ≅
      ModuleCat.uliftFunctor.{u + 1, u}
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) ⋙
      ModuleCat.extendScalars.{u, u + 1, u + 1}
        (LocalFrobeniusLarge.embedding l Ω E) :=
    NatIso.ofComponents (fun V ↦
      ((ULift.moduleEquiv : ULift.{u + 1} V ≃ₗ[
        AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E] V).symm.baseChange
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) Ω V
          (ULift.{u + 1} V)).toModuleIso) (by
      intro V W f
      apply ModuleCat.ExtendScalars.hom_ext
      intro v
      rfl)
  refine ⟨e, ?_, ?_⟩
  · intro V a v
    rfl
  · intro e' he'
    apply Iso.ext
    apply NatTrans.ext
    funext V
    apply ModuleCat.ExtendScalars.hom_ext
    intro v
    exact he' V 1 v

/-- The uniquely tensor-normalized carrier-lift comparison.
Source: Weil II (1.1.1)d)
(blueprint: def-zl-completed-local-fibre-comparison-data). -/
def stageLift (E : Padic.FiniteCoefficientFields l Ω) :=
  (stageLift_existsUnique l Ω E).exists.choose

/-- Exact finite-stage point-fibre object, with its prescribed tensor extension.
Source: common-stage point convention; BS 6.8.14(2)
(blueprint: def-zl-completed-local-fibre-comparison-data). -/
def pointStageObject (E : Padic.FiniteCoefficientFields l Ω)
    (N : sfRationalConstructibleCategory l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) (Spec (.of D.k))) :
    (LocalFrobeniusLarge.pointFibre D l hl Ω).obj
        ((GeneralAlgebraicallyClosedCoefficients.inclusion E).obj N) ≅
      (LocalFrobeniusLarge.stageFibre D l hl Ω E).obj N :=
  Iso.refl _

-- Retain the existing separatedness and stalk-unit parameters.
set_option linter.unusedSectionVars false in
/-- The pullback on an included object has precisely its given finite-stage object.
Source: common-stage pullback object prescription, BS 6.8.15
(blueprint: def-zl-completed-local-fibre-comparison-data).
Proof: apply commonStageDerivedPullback_existsUnique to the included object.
The inclusion's object is the pair (E,K), so its stage and object are E and K. -/
theorem finitePullObject (E : Padic.FiniteCoefficientFields l Ω)
    (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left)
    (K : sfRationalConstructibleCategory l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) (D.geometricFiber Y₀).left) :
    (@commonStageDerivedPullback l _ Ω _ _ _ _ _ x
      (frobeniusPointPrimeInvertible D l hl) (sfWeilPrimeInvertible D l hl Y₀)).obj
      ((GeneralAlgebraicallyClosedCoefficients.inclusion E).obj K) =
    (GeneralAlgebraicallyClosedCoefficients.inclusion E).obj
      ((@rationalDerivedPullback l _
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) _ _ _ _ _ x
        (frobeniusPointPrimeInvertible D l hl) (sfWeilPrimeInvertible D l hl Y₀)).obj K) := by
  exact ((@commonStageDerivedPullback_existsUnique l _ Ω _ _ _ _ _ x
    (frobeniusPointPrimeInvertible D l hl) (sfWeilPrimeInvertible D l hl Y₀)).exists.choose_spec.1
      ((GeneralAlgebraicallyClosedCoefficients.inclusion E).obj K))

/-- The canonical object comparison with all finite-stage endpoints explicit.
Source: common-stage pullback prescription; BS 6.8.15
(blueprint: def-zl-completed-local-fibre-comparison-data). -/
def finitePullFibre (E : Padic.FiniteCoefficientFields l Ω)
    (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left)
    (K : sfRationalConstructibleCategory l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) (D.geometricFiber Y₀).left) :
    (LocalFrobeniusLarge.stalk D l hl Ω Y₀ x).obj
      ((GeneralAlgebraicallyClosedCoefficients.inclusion E).obj K) ≅
    (LocalFrobeniusLarge.stageFibre D l hl Ω E).obj
      ((@rationalDerivedPullback l _
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) _ _ _ _ _ x
        (frobeniusPointPrimeInvertible D l hl) (sfWeilPrimeInvertible D l hl Y₀)).obj K) :=
  (LocalFrobeniusLarge.pointFibre D l hl Ω).mapIso
    (eqToIso (finitePullObject l Ω D hl Y₀ E x K)) ≪≫
  pointStageObject l Ω D hl E
    ((@rationalDerivedPullback l _
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) _ _ _ _ _ x
      (frobeniusPointPrimeInvertible D l hl) (sfWeilPrimeInvertible D l hl Y₀)).obj K)

attribute [irreducible] finitePullFibre pointStageObject

/-- The carrier-size comparison at a fixed raw point object.
Source: BS 6.8.14(2) (blueprint: def-zl-completed-local-fibre-comparison-data). -/
def pointStageLift (E : Padic.FiniteCoefficientFields l Ω)
    (K : LisseRealization.Raw D l hl
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)
      (LisseRealization.point D l hl)) :
    (LocalFrobeniusLarge.stageFibre D l hl Ω E).obj K ≅
      (ModuleCat.extendScalars (LocalFrobeniusLarge.embedding l Ω E)).obj
        ((LisseRealization.fibre D l hl
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)).obj K) :=
  (stageLift l Ω E).app
    ((DerivedCategory.coefficientFdCohomology
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) 0).obj
      ((pointRationalFibre D l hl
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)).obj K))

/-- Normalized point sections, after the explicit carrier-size tensor comparison.
Source: BS 6.8.14(2) (blueprint: def-zl-completed-local-fibre-comparison-data). -/
def pointSectionIso (E : Padic.FiniteCoefficientFields l Ω)
    (a : LisseRealization.At D l hl
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)
      (LisseRealization.point D l hl))
    (p : LisseRealization.PointAt D l hl
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) a)
    (K : LisseRealization.Raw D l hl
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)
      (LisseRealization.point D l hl))
    (hK : LisseRealization.Lisse D l hl
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)
      (LisseRealization.point D l hl) K) :=
  pointStageLift l Ω D hl E K ≪≫
    (ModuleCat.extendScalars (LocalFrobeniusLarge.embedding l Ω E)).mapIso
      (p.comparison.app ⟨K, hK⟩)

/-- The normalized finite point comparison followed by ordinary inverse-image sections.
Source: BS 6.8.14(2), 6.8.15
(blueprint: def-zl-completed-local-fibre-comparison-data). -/
def finiteSectionIso (E : Padic.FiniteCoefficientFields l Ω)
    (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left)
    (a : LisseRealization.At D l hl
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)
      (LisseRealization.point D l hl))
    (p : LisseRealization.PointAt D l hl
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) a)
    (ax : LisseRealization.Along D l hl
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) x a
        (pinnedModels l Ω D hl Y₀ R E).realization)
    (F : AlgebraicGeometry.ProEtale.CompletedLisse.RawRational l
      (zlCompletedBase D l Ω Y₀ E)) :=
  pointSectionIso l Ω D hl E a p _
    (ax.preserves _ ((pinnedModels l Ω D hl Y₀ R E).lisse F)) ≪≫
  (ModuleCat.extendScalars (LocalFrobeniusLarge.embedding l Ω E)).mapIso
    ((LisseRealization.sections D l hl
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)).mapIso
      (ax.comparison _ ((pinnedModels l Ω D hl Y₀ R E).lisse F)))

/-- The completed-fibre comparison is fixed through normalized ordinary sections.
The finite-section formula retains every inverse-limit projection and the SAME stage
isomorphism used by R.pullback_pinning, including its inverse on fibres.
Source: BS 6.8.4(1),(4), 6.8.14(2), 6.8.15; blueprint proof steps 1--3
(blueprint: def-zl-completed-local-fibre-comparison-data). -/
def CompletedNormalization
    (c : ∀ x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left,
      R.functor ⋙ LocalFrobeniusLarge.stalk D l hl Ω Y₀ x ≅ fibre l Ω x) : Prop :=
  ∀ (E : Padic.FiniteCoefficientFields l Ω)
    (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left),
  ∃ (a : LisseRealization.At D l hl
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)
      (LisseRealization.point D l hl))
    (p : LisseRealization.PointAt D l hl
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) a)
    (_pn : LisseRealization.PointNormalized D l hl
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) a p)
    (ax : LisseRealization.Along D l hl
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) x a
        (pinnedModels l Ω D hl Y₀ R E).realization)
    (_nx : LisseRealization.PullNormalized D l hl
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) x a
        (pinnedModels l Ω D hl Y₀ R E).realization ax),
  ∃ e : (pinnedModels l Ω D hl Y₀ R E).finite ⋙
      GeneralAlgebraicallyClosedCoefficients.inclusion E ⋙
      LocalFrobeniusLarge.stalk D l hl Ω Y₀ x ≅ finiteSections l Ω D hl Y₀ R E x,
  (∀ F : AlgebraicGeometry.ProEtale.CompletedLisse.RawRational l
      (zlCompletedBase D l Ω Y₀ E),
    HEq (e.hom.app F)
      ((finitePullFibre l Ω D hl Y₀ E x
        ((pinnedModels l Ω D hl Y₀ R E).finite.obj F)).hom ≫
        (finiteSectionIso l Ω D hl Y₀ R E x a p ax F).hom)) ∧
  (∀ (F : AlgebraicGeometry.ProEtale.CompletedLisse.RawRational l
      (zlCompletedBase D l Ω Y₀ E)) (U : (D.geometricFiber Y₀).left.ProEt)
      (z : Spec (.of D.k) ⟶ U.left) (hz : z ≫ U.hom = x)
      (v : ((pinnedModels l Ω D hl Y₀ R E).completed.equivalence.inverse.obj
        ⟨F.obj.integral, F.property⟩).obj.val.obj (op U))
      (w : lisseIntegralFiber l E.val (D.geometricFiber Y₀).left x F.obj.integral)
      (_hw : RepresentsCompletedGerm l Ω D hl Y₀ R E x F U z hz v w)
      (a₀ : Ω) (b : E.val),
    (c x).hom.app ((zlClassicalModel D l Ω Y₀ E).obj F)
      ((LocalFrobeniusLarge.stalk D l hl Ω Y₀ x).map
        ((pinnedStage l Ω D hl Y₀ R E).inv.app F)
        (e.inv.app F
          (a₀ ⊗ₜ[AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E,
            LocalFrobeniusLarge.embedding l Ω E]
            sectionGerm l Ω D hl Y₀ E x _ U z hz
              (completedSection l Ω D hl Y₀ R E F U b v)))) =
    (eqToIso (lisseAlgebraicFiber_ofModel l (D.geometricFiber Y₀).left x Ω E F.obj)).inv
      (a₀ ⊗ₜ[E.val] (b ⊗ₜ[Padic.coefficientExtensionIntegers l E.val] w)))

end WeilConjectures.ClassicalLocalFrobenius
