/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q31
-/
module

public import Sheaf.Paper.ClassicalWeilFiltrationHeartTransport
public import Sheaf.Paper.NormalizedClassicalWeilRealization
public import Sheaf.Paper.LisseCompletedSystemData
public import Sheaf.Paper.ConstantExtensionWeilHeartEquivalence
public import Sheaf.Paper.CommonStageLocallyFree
public import Sheaf.Paper.AdicLocalCharacteristicFactor
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Normalized curve restriction and finite stalk data

These are the existing curve-restriction definitions, publicly reexported by the
filtration-spectrum theorem module. The finite inclusion isomorphism packages the
same equality comparison without repeating its large proof term in a structure.
Source: blueprint latest, real-mixed-by-curves, paragraph 2; BS 6.8; Weil II (1.1.8).
(blueprint: def-zl-curve-restriction-filtration-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.defProp false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Endofunctor (IsoAlgebra)
open Opposite
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type (u + 1)) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
  [IsSeparated X₀.hom]

variable (m : ℕ) (hm : 1 ≤ m)
  (C₀ : Over (Spec (.of (D.extensionSubfield m hm))))
  [LocallyOfFiniteType C₀.hom] [QuasiCompact C₀.hom]
  (h₀ : C₀ ⟶ constantExtensionModel D m hm X₀) [IsClosedImmersion h₀.left]

/-- The actual arithmetic composite, whose residue degree is used below.
Source: blueprint paragraph 2, points of the curve over X₀
(blueprint: lem-zl-curve-restriction-filtration-spectrum). -/
def zlCurveArithmeticMap := h₀.left ≫ (constantExtensionProjection D m hm X₀).left

/-- The geometric composite under the canonical associativity identification.
Source: blueprint paragraph 2, ordinary geometric pullback
(blueprint: lem-zl-curve-restriction-filtration-spectrum). -/
def zlCurveGeometricMap := zlFiberMap (constantExtensionDatum D m hm) h₀ ≫
  (constantExtensionFiberIso D m hm X₀).hom

/-- Constant restriction followed by the actual Weil inverse image on the curve.
Source: blueprint paragraph 2, R_m
(blueprint: lem-zl-curve-restriction-filtration-spectrum). -/
def zlCurveRestriction
    (R : sfCommonStageWeilSheaf D l hl X₀ Ω ⥤
      sfCommonStageWeilSheaf (constantExtensionDatum D m hm) l hl
        (constantExtensionModel D m hm X₀) Ω) :=
  R ⋙ zlWeilPull (constantExtensionDatum D m hm) l hl Ω h₀

/-- Separatedness of the actual constant model, inherited by base change.
Source: Stacks 01KU, blueprint paragraph 2
(blueprint: lem-zl-curve-restriction-filtration-spectrum). -/
@[instance_reducible]
def zlCurveModelSeparated : IsSeparated (constantExtensionModel D m hm X₀).hom :=
  inferInstanceAs (IsSeparated (pullback.snd X₀.hom
    (Spec.map (CommRingCat.ofHom (D.extensionEmbedding m hm)))))

/-- Separatedness is inherited from the specified closed immersion.
Source: Stacks 01KU and 035C, blueprint paragraph 2
(blueprint: lem-zl-curve-restriction-filtration-spectrum). -/
@[instance_reducible]
def zlCurveSeparated : IsSeparated C₀.hom :=
  letI := zlCurveModelSeparated D X₀ m hm
  h₀.w ▸ inferInstanceAs (IsSeparated
    (h₀.left ≫ (constantExtensionModel D m hm X₀).hom))

/-- A normalized comparison on all finite locally free systems. The global system
contains the identity/composition equations, including rational maps and inverse limits.
Source: BS 6.8.4(1),(4), 6.8.15, blueprint paragraph 2
(blueprint: lem-zl-curve-restriction-filtration-spectrum). -/
structure ZlCurveClassicalPullback
    [IsSeparated C₀.hom]
    [Fact (∀ x : (D.geometricFiber X₀).left,
      IsUnit (l : (D.geometricFiber X₀).left.presheaf.stalk x))]
    [Fact (∀ x : ((constantExtensionDatum D m hm).geometricFiber C₀).left,
      IsUnit (l : ((constantExtensionDatum D m hm).geometricFiber C₀).left.presheaf.stalk x))]
    (RX : ZlClassicalRealization D l hl Ω X₀)
    (RC : ZlClassicalRealization (constantExtensionDatum D m hm) l hl Ω C₀)
    (R : sfCommonStageWeilSheaf D l hl X₀ Ω ⥤
      sfCommonStageWeilSheaf (constantExtensionDatum D m hm) l hl
        (constantExtensionModel D m hm X₀) Ω) where
  systems : AlgebraicGeometry.ProEtale.CompletedLisse.System l
  classical : ZlClassicalWeil D l Ω X₀ ⥤
    ZlClassicalWeil (constantExtensionDatum D m hm) l Ω C₀
  geometric : LisseAlgebraicSheaf l (D.geometricFiber X₀).left Ω ⥤
    LisseAlgebraicSheaf l ((constantExtensionDatum D m hm).geometricFiber C₀).left Ω
  forget : classical ⋙ IsoAlgebra.forget
      (lisseAlgebraicAutomorphismPullback
        ((constantExtensionDatum D m hm).geometricFrobenius C₀) l Ω) ≅
    IsoAlgebra.forget (lisseAlgebraicAutomorphismPullback (D.geometricFrobenius X₀) l Ω) ⋙
      geometric
  models : ∀ E : Padic.FiniteCoefficientFields l Ω,
    zlClassicalModel D l Ω X₀ E ⋙ geometric ≅
      (systems.operation
        (AlgebraicGeometry.ProEtale.CompletedLisse.Arrow.mk
          (zlCurveGeometricMap D X₀ m hm C₀ h₀) (AlgHom.id ℚ_[l] E.val))).raw ⋙
        zlClassicalModel (constantExtensionDatum D m hm) l Ω C₀ E
  underlying : zlCurveRestriction D l hl Ω X₀ m hm C₀ h₀ R ⋙
      constantExtensionHeartForget (constantExtensionDatum D m hm) l hl Ω C₀ ≅
    constantExtensionHeartForget D l hl Ω X₀ ⋙
      @commonStageDerivedPullback l _ Ω _ _ _ _ _
        (zlCurveGeometricMap D X₀ m hm C₀ h₀)
        (sfWeilPrimeInvertible (constantExtensionDatum D m hm) l hl C₀)
        (sfWeilPrimeInvertible D l hl X₀)
  constant_comparison : R ⋙
      constantExtensionHeartForget (constantExtensionDatum D m hm) l hl Ω
        (constantExtensionModel D m hm X₀) ≅
    constantExtensionHeartForget D l hl Ω X₀ ⋙
      constantExtensionFiberPull D m hm X₀ l hl Ω
  constant_weil : ∀ F,
    (sfCommonStageWeilFrobeniusPullback (constantExtensionDatum D m hm) l hl
        (constantExtensionModel D m hm X₀) Ω).map (constant_comparison.hom.app F) ≫
      (constantExtensionRestrictionComparison D m hm X₀ l hl Ω F.obj.carrier).hom ≫
      (constantExtensionFiberPull D m hm X₀ l hl Ω).map
        (constantExtensionWeilIterate D l hl Ω X₀ F.obj (m - 1)).hom =
      (R.obj F).obj.str.hom ≫ constant_comparison.hom.app F
  underlying_normalization :
    ∀ F, HEq (underlying.hom.app F)
      ((@commonStageDerivedPullback l _ Ω _ _ _ _ _
          (zlFiberMap (constantExtensionDatum D m hm) h₀)
          (sfWeilPrimeInvertible (constantExtensionDatum D m hm) l hl C₀)
          (sfWeilPrimeInvertible (constantExtensionDatum D m hm) l hl
            (constantExtensionModel D m hm X₀))).map
            (constant_comparison.hom.app F) ≫
        (@zlPullComp l _ Ω _ _ _ _ _ _
          (sfWeilPrimeInvertible (constantExtensionDatum D m hm) l hl C₀)
          (sfWeilPrimeInvertible (constantExtensionDatum D m hm) l hl
            (constantExtensionModel D m hm X₀))
          (sfWeilPrimeInvertible D l hl X₀)
          (zlFiberMap (constantExtensionDatum D m hm) h₀)
          (constantExtensionFiberIso D m hm X₀).hom).inv.app F.obj.carrier)
  geometric_realization : RX.functor ⋙
      @commonStageDerivedPullback l _ Ω _ _ _ _ _
        (zlCurveGeometricMap D X₀ m hm C₀ h₀)
        (sfWeilPrimeInvertible (constantExtensionDatum D m hm) l hl C₀)
        (sfWeilPrimeInvertible D l hl X₀) ≅ geometric ⋙ RC.functor
  realization : RX.weil D l hl Ω X₀ ⋙ zlCurveRestriction D l hl Ω X₀ m hm C₀ h₀ R ≅
    classical ⋙ RC.weil (constantExtensionDatum D m hm) l hl Ω C₀
  realization_underlying : ∀ F,
    (constantExtensionHeartForget (constantExtensionDatum D m hm) l hl Ω C₀).map
        (realization.hom.app F) =
      underlying.hom.app ((RX.weil D l hl Ω X₀).obj F) ≫
        geometric_realization.hom.app F.carrier ≫ RC.functor.map (forget.inv.app F)

/-- The identity of the normalized point-sections models when only the finite base
field changes. Both sides use the same algebraic closure k and the same coefficients.
Source: BS 6.8.14, blueprint paragraph 2
(blueprint: lem-zl-curve-restriction-filtration-spectrum). -/
def zlCurvePointBaseIso (E : Padic.FiniteCoefficientFields l Ω)
    (V : sfRationalConstructibleCategory l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) (Spec (.of D.k))) :=
  ((ModuleCat.uliftFunctor.{u + 1, u} _).mapDerivedCategoryHomologyFunctorIso 0).app
      ((pointRationalFibre (constantExtensionDatum D m hm) l hl
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)).obj V).obj ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat.{u + 1}
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)) 0).mapIso
        (pointRationalNormalization (constantExtensionDatum D m hm) l hl _ V ≪≫
          (pointRationalNormalization D l hl _ V).symm) ≪≫
    (((ModuleCat.uliftFunctor.{u + 1, u} _).mapDerivedCategoryHomologyFunctorIso 0).app
      ((pointRationalFibre D l hl
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)).obj V).obj).symm

/-- The canonical finite-stage stalk comparison: pull back the carrier identification,
invert the pullback compositor, identify the geometric lifts, and apply H^0 and scalar
extension. The point-base comparison is fixed by the same normalized point sections.
Source: Weil II (1.1.8)--(1.1.10), BS 6.8.14--6.8.15, blueprint paragraph 2
(blueprint: lem-zl-curve-restriction-filtration-spectrum). -/
def zlCurveFiniteStalkIso (E : Padic.FiniteCoefficientFields l Ω)
    (K : sfWeilComplex D l hl X₀ (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E))
    (K' : sfWeilComplex (constantExtensionDatum D m hm) l hl C₀
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E))
    (a : K'.carrier ≅
      (@rationalDerivedPullback l _ (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)
        _ _ _ ((constantExtensionDatum D m hm).geometricFiber C₀).left
        (D.geometricFiber X₀).left (zlCurveGeometricMap D X₀ m hm C₀ h₀)
        (sfWeilPrimeInvertible (constantExtensionDatum D m hm) l hl C₀)
        (sfWeilPrimeInvertible D l hl X₀)).obj K.carrier)
    (zbar : Spec (.of D.k) ⟶ ((constantExtensionDatum D m hm).geometricFiber C₀).left)
    (xbar : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left)
    (heq : zbar ≫ zlCurveGeometricMap D X₀ m hm C₀ h₀ = xbar) :
    zlExtendedFiniteFibre (constantExtensionDatum D m hm) l hl Ω C₀ E K' zbar ≅
      zlExtendedFiniteFibre D l hl Ω X₀ E K xbar :=
  letI : ∀ x : ((constantExtensionDatum D m hm).geometricFiber C₀).left,
      Invertible (l : ((constantExtensionDatum D m hm).geometricFiber C₀).left.residueField x) :=
    sfWeilPrimeInvertible (constantExtensionDatum D m hm) l hl C₀
  letI : ∀ x : (D.geometricFiber X₀).left,
      Invertible (l : (D.geometricFiber X₀).left.residueField x) :=
    sfWeilPrimeInvertible D l hl X₀
  letI : ∀ x : Spec (.of D.k), Invertible (l : (Spec (.of D.k)).residueField x) :=
    frobeniusPointPrimeInvertible D l hl
  let c : localDerivedStalk l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)
      (constantExtensionDatum D m hm) hl C₀ K' zbar ≅
      localDerivedStalk l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)
        D hl X₀ K xbar :=
    (@rationalDerivedPullback l _ (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)
        _ _ _ (Spec (.of D.k))
        ((constantExtensionDatum D m hm).geometricFiber C₀).left zbar
        (frobeniusPointPrimeInvertible D l hl)
        (sfWeilPrimeInvertible (constantExtensionDatum D m hm) l hl C₀)).mapIso a ≪≫
      (@localPullbackComposition l _ (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)
        _ _ _ (Spec (.of D.k))
        ((constantExtensionDatum D m hm).geometricFiber C₀).left
        (D.geometricFiber X₀).left zbar (zlCurveGeometricMap D X₀ m hm C₀ h₀)
        (frobeniusPointPrimeInvertible D l hl)
        (sfWeilPrimeInvertible (constantExtensionDatum D m hm) l hl C₀)
        (sfWeilPrimeInvertible D l hl X₀) K.carrier).symm ≪≫
      eqToIso (congrArg (fun f ↦
        (@rationalDerivedPullback l _ (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)
          _ _ _ (Spec (.of D.k)) (D.geometricFiber X₀).left f
          (frobeniusPointPrimeInvertible D l hl)
          (sfWeilPrimeInvertible D l hl X₀)).obj K.carrier) heq)
  (ModuleCat.extendScalars (sfAdicCoefficientEmbedding.{u} l Ω E)).mapIso
    (zlCurvePointBaseIso D l hl Ω m hm E
        (localDerivedStalk l _ (constantExtensionDatum D m hm) hl C₀ K' zbar) ≪≫
      (ModuleCat.uliftFunctor.{u + 1, u}
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)).mapIso
        ((DerivedCategory.coefficientFdCohomology
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) 0).mapIso
          ((pointRationalFibre D l hl
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)).mapIso c)))

attribute [local irreducible] zlCurveFiniteStalkIso zlCurvePointBaseIso

/-- The scalar-extended degree-zero local operator at the displayed finite stage.
Source: Weil II (1.1.8), blueprint paragraph 2
(blueprint: lem-zl-curve-restriction-filtration-spectrum). -/
def zlCurveFiniteFrobenius (Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (E : Padic.FiniteCoefficientFields l Ω)
    (K : sfWeilComplex D l hl Y₀ (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E))
    (y : {y : Y₀.left // y ∈ closedPoints Y₀.left})
    (ι : Y₀.left.residueField y.val →+* D.k)
    (hι : ι.comp (Y₀.hom.residueFieldAlgebraMap y.val) = algebraMap D.k₀ D.k) :=
  (ModuleCat.extendScalars (sfAdicCoefficientEmbedding.{u} l Ω E)).map
    ((ModuleCat.uliftFunctor.{u + 1, u}
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)).map
      (localClosedFrobeniusCohomology l _ D hl Y₀ K y ι hι 0))

attribute [local irreducible] zlCurveFiniteFrobenius

/-- The literal finite-stage object formula for the geometric curve pullback,
packaged as an isomorphism so that normalization fields do not repeat its proof term.
Source: the common-stage pullback object clause, blueprint paragraph 2
(blueprint: def-zl-curve-restriction-filtration-data). -/
@[irreducible]
def zlCurveFiniteInclusionIso (E : Padic.FiniteCoefficientFields l Ω)
    (K : sfWeilComplex D l hl X₀ (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)) :
    (@commonStageDerivedPullback l _ Ω _ _ _ _ _
      (zlCurveGeometricMap D X₀ m hm C₀ h₀)
      (sfWeilPrimeInvertible (constantExtensionDatum D m hm) l hl C₀)
      (sfWeilPrimeInvertible D l hl X₀)).obj
        ((GeneralAlgebraicallyClosedCoefficients.inclusion E).obj K.carrier) ≅
      (GeneralAlgebraicallyClosedCoefficients.inclusion E).obj
        ((@rationalDerivedPullback l _ (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)
          _ _ _ ((constantExtensionDatum D m hm).geometricFiber C₀).left
          (D.geometricFiber X₀).left (zlCurveGeometricMap D X₀ m hm C₀ h₀)
          (sfWeilPrimeInvertible (constantExtensionDatum D m hm) l hl C₀)
          (sfWeilPrimeInvertible D l hl X₀)).obj K.carrier) :=
  eqToIso ((@commonStageDerivedPullback_existsUnique l _ Ω _ _ _
    ((constantExtensionDatum D m hm).geometricFiber C₀).left
    (D.geometricFiber X₀).left (zlCurveGeometricMap D X₀ m hm C₀ h₀)
    (sfWeilPrimeInvertible (constantExtensionDatum D m hm) l hl C₀)
    (sfWeilPrimeInvertible D l hl X₀)).exists.choose_spec.1
      ((GeneralAlgebraicallyClosedCoefficients.inclusion E).obj K.carrier))

/-- Finite-stage form of the canonical carrier comparison. Its equality after inclusion
pins it to the geometric pullback comparison of the prescribed common-stage objects.
Source: BS 6.8.14, blueprint paragraph 2
(blueprint: lem-zl-curve-restriction-filtration-spectrum). -/
structure ZlCurveFiniteModel
    (R : sfCommonStageWeilSheaf D l hl X₀ Ω ⥤
      sfCommonStageWeilSheaf (constantExtensionDatum D m hm) l hl
        (constantExtensionModel D m hm X₀) Ω)
    (α : zlCurveRestriction D l hl Ω X₀ m hm C₀ h₀ R ⋙
        constantExtensionHeartForget (constantExtensionDatum D m hm) l hl Ω C₀ ≅
      constantExtensionHeartForget D l hl Ω X₀ ⋙
        @commonStageDerivedPullback l _ Ω _ _ _ _ _
          (zlCurveGeometricMap D X₀ m hm C₀ h₀)
          (sfWeilPrimeInvertible (constantExtensionDatum D m hm) l hl C₀)
          (sfWeilPrimeInvertible D l hl X₀))
    (H : sfCommonStageWeilSheaf D l hl X₀ Ω) where
  field : Padic.FiniteCoefficientFields l Ω
  source : sfWeilComplex D l hl X₀ (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω field)
  target : sfWeilComplex (constantExtensionDatum D m hm) l hl C₀
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω field)
  source_iso : sfWeilStageObject D l hl X₀ Ω field source ≅ H.obj
  target_iso : sfWeilStageObject (constantExtensionDatum D m hm) l hl C₀ Ω field target ≅
    ((zlCurveRestriction D l hl Ω X₀ m hm C₀ h₀ R).obj H).obj
  carrier : target.carrier ≅
    (@rationalDerivedPullback l _ (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω field)
      _ _ _ ((constantExtensionDatum D m hm).geometricFiber C₀).left
        (D.geometricFiber X₀).left (zlCurveGeometricMap D X₀ m hm C₀ h₀)
      (sfWeilPrimeInvertible (constantExtensionDatum D m hm) l hl C₀)
      (sfWeilPrimeInvertible D l hl X₀)).obj source.carrier
  normalization :
    (GeneralAlgebraicallyClosedCoefficients.inclusion field).map carrier.hom =
      target_iso.hom.hom.f ≫ α.hom.app H ≫
        (@commonStageDerivedPullback l _ Ω _ _ _ _ _
          (zlCurveGeometricMap D X₀ m hm C₀ h₀)
          (sfWeilPrimeInvertible (constantExtensionDatum D m hm) l hl C₀)
          (sfWeilPrimeInvertible D l hl X₀)).map source_iso.inv.hom.f ≫
        (zlCurveFiniteInclusionIso D l hl Ω X₀ m hm C₀ h₀ field source).hom

/-- The local conclusions for the canonical composite stalk map, for every finite
presentation of a term or quotient. Spectrum means the roots of the reverse local
factor reversed back, with algebraic multiplicities retained.
Source: Weil II (1.1.8)--(1.1.10), blueprint paragraph 2
(blueprint: lem-zl-curve-restriction-filtration-spectrum). -/
def ZlCurveLocalConclusions
    [IsSeparated C₀.hom]
    (R : sfCommonStageWeilSheaf D l hl X₀ Ω ⥤
      sfCommonStageWeilSheaf (constantExtensionDatum D m hm) l hl
        (constantExtensionModel D m hm X₀) Ω)
    (α : zlCurveRestriction D l hl Ω X₀ m hm C₀ h₀ R ⋙
        constantExtensionHeartForget (constantExtensionDatum D m hm) l hl Ω C₀ ≅
      constantExtensionHeartForget D l hl Ω X₀ ⋙
        @commonStageDerivedPullback l _ Ω _ _ _
          ((constantExtensionDatum D m hm).geometricFiber C₀).left
          (D.geometricFiber X₀).left (zlCurveGeometricMap D X₀ m hm C₀ h₀)
          (sfWeilPrimeInvertible (constantExtensionDatum D m hm) l hl C₀)
          (sfWeilPrimeInvertible D l hl X₀))
    (H : sfCommonStageWeilSheaf D l hl X₀ Ω) : Prop :=
  Nonempty (ZlCurveFiniteModel D l hl Ω X₀ m hm C₀ h₀ R α H) ∧
  ∀ z : {z : C₀.left // z ∈ closedPoints C₀.left},
    ∃ hx : zlCurveArithmeticMap D X₀ m hm C₀ h₀ z.val ∈ closedPoints X₀.left,
      1 ≤ (zlCurveArithmeticMap D X₀ m hm C₀ h₀).residueDegree z.val ∧
      Nat.card (C₀.left.residueField z.val) =
        Nat.card (X₀.left.residueField (zlCurveArithmeticMap D X₀ m hm C₀ h₀ z.val)) ^
          (zlCurveArithmeticMap D X₀ m hm C₀ h₀).residueDegree z.val ∧
      (sfLocalCharacteristicFactor (constantExtensionDatum D m hm) l hl Ω C₀
          ((zlCurveRestriction D l hl Ω X₀ m hm C₀ h₀ R).obj H) z).reverse.roots =
        (sfLocalCharacteristicFactor D l hl Ω X₀ H
          ⟨zlCurveArithmeticMap D X₀ m hm C₀ h₀ z.val, hx⟩).reverse.roots.map
            (fun a ↦ a ^ (zlCurveArithmeticMap D X₀ m hm C₀ h₀).residueDegree z.val) ∧
      ∀ (M : ZlCurveFiniteModel D l hl Ω X₀ m hm C₀ h₀ R α H)
        (ιz : C₀.left.residueField z.val →+* D.k)
        (hz : ιz.comp (C₀.hom.residueFieldAlgebraMap z.val) =
          algebraMap (D.extensionSubfield m hm) D.k)
        (ιx : X₀.left.residueField (zlCurveArithmeticMap D X₀ m hm C₀ h₀ z.val) →+* D.k)
        (hxι : ιx.comp (X₀.hom.residueFieldAlgebraMap
            (zlCurveArithmeticMap D X₀ m hm C₀ h₀ z.val)) = algebraMap D.k₀ D.k)
        (heq : localClosedPoint (constantExtensionDatum D m hm) C₀ z ιz hz ≫
            zlCurveGeometricMap D X₀ m hm C₀ h₀ =
          localClosedPoint D X₀ ⟨zlCurveArithmeticMap D X₀ m hm C₀ h₀ z.val, hx⟩ ιx hxι),
        zlCurveFiniteFrobenius (constantExtensionDatum D m hm) l hl Ω C₀ M.field
            M.target z ιz hz ≫
          (zlCurveFiniteStalkIso D l hl Ω X₀ m hm C₀ h₀ M.field M.source M.target M.carrier
            (localClosedPoint (constantExtensionDatum D m hm) C₀ z ιz hz)
            (localClosedPoint D X₀ ⟨zlCurveArithmeticMap D X₀ m hm C₀ h₀ z.val, hx⟩
              ιx hxι) heq).hom =
        (zlCurveFiniteStalkIso D l hl Ω X₀ m hm C₀ h₀ M.field M.source M.target M.carrier
            (localClosedPoint (constantExtensionDatum D m hm) C₀ z ιz hz)
            (localClosedPoint D X₀ ⟨zlCurveArithmeticMap D X₀ m hm C₀ h₀ z.val, hx⟩
              ιx hxι) heq).hom ≫
          (End.of (zlCurveFiniteFrobenius D l hl Ω X₀ M.field M.source
            ⟨zlCurveArithmeticMap D X₀ m hm C₀ h₀ z.val, hx⟩ ιx hxι)) ^
              (zlCurveArithmeticMap D X₀ m hm C₀ h₀).residueDegree z.val

/-- Exactness, lissity, normalized realization and local powers for the prescribed
classical filtration. Naturality of the functor isomorphism includes every arrow,
composite and inverse Weil map; the two transport records include all point periods.
Source: blueprint paragraph 2; BS 6.8.4, 6.8.14, 6.8.15
(blueprint: lem-zl-curve-restriction-filtration-spectrum). -/
def ZlCurveRestrictionFiltrationSpectrum (iota : Ω ≃+* ℂ) : Prop :=
  letI := zlCurveSeparated D X₀ m hm C₀ h₀
  letI : Fact (∀ x : (D.geometricFiber X₀).left,
      IsUnit (l : (D.geometricFiber X₀).left.presheaf.stalk x)) :=
    ⟨fun x ↦ @isUnit_of_invertible _ _ _ (zlClassicalStalkInvertible D l hl X₀ x)⟩
  letI : Fact (∀ x : ((constantExtensionDatum D m hm).geometricFiber C₀).left,
      IsUnit (l : ((constantExtensionDatum D m hm).geometricFiber C₀).left.presheaf.stalk x)) :=
    ⟨fun x ↦ @isUnit_of_invertible _ _ _
      (zlClassicalStalkInvertible (constantExtensionDatum D m hm) l hl C₀ x)⟩
  ∀ (R : sfCommonStageWeilSheaf D l hl X₀ Ω ⥤
      sfCommonStageWeilSheaf (constantExtensionDatum D m hm) l hl
        (constantExtensionModel D m hm X₀) Ω),
    ConstantExtensionRestrictionSpec D m hm X₀ l hl Ω R →
    ∀ (RX : ZlClassicalRealization D l hl Ω X₀)
      (RC : ZlClassicalRealization (constantExtensionDatum D m hm) l hl Ω C₀),
    ∃ c : ZlCurveClassicalPullback D l hl Ω X₀ m hm C₀ h₀ RX RC R,
      ∀ (r : ℕ) (F : ZlClassicalFiltration D l Ω X₀ r)
        (G : sfCommonStageWeilSheaf D l hl X₀ Ω)
        (e : (RX.weil D l hl Ω X₀).obj (F.terms (Fin.last r)) ≅ G),
      ∃ F' : ZlClassicalFiltration (constantExtensionDatum D m hm) l Ω C₀ r,
        F'.terms = (fun j ↦ c.classical.obj (F.terms j)) ∧
        F'.quotients = (fun j ↦ c.classical.obj (F.quotients j)) ∧
        (∀ j : Fin r, HEq (F'.inclusion j) (c.classical.map (F.inclusion j))) ∧
        (∀ j : Fin r, HEq (F'.quotient j) (c.classical.map (F.quotient j))) ∧
        Nonempty (ZlFiltrationTransport D l hl Ω X₀ RX r F G e iota) ∧
        (∃ e' : (RC.weil (constantExtensionDatum D m hm) l hl Ω C₀).obj
            (F'.terms (Fin.last r)) ≅
              (zlCurveRestriction D l hl Ω X₀ m hm C₀ h₀ R).obj G,
          HEq e' ((c.realization.app (F.terms (Fin.last r))).symm ≪≫
            (zlCurveRestriction D l hl Ω X₀ m hm C₀ h₀ R).mapIso e) ∧
          Nonempty (ZlFiltrationTransport (constantExtensionDatum D m hm) l hl Ω C₀
            RC r F' ((zlCurveRestriction D l hl Ω X₀ m hm C₀ h₀ R).obj G) e' iota)) ∧
        IsZero ((zlCurveRestriction D l hl Ω X₀ m hm C₀ h₀ R).obj
          ((RX.weil D l hl Ω X₀).obj (F.terms 0))) ∧
        (∀ j : Fin r, ∃ hz :
          (zlCurveRestriction D l hl Ω X₀ m hm C₀ h₀ R).map
              ((RX.weil D l hl Ω X₀).map (F.inclusion j)) ≫
            (zlCurveRestriction D l hl Ω X₀ m hm C₀ h₀ R).map
              ((RX.weil D l hl Ω X₀).map (F.quotient j)) = 0,
          (ShortComplex.mk _ _ hz).ShortExact) ∧
        (∀ H : ZlClassicalWeil D l Ω X₀,
          (∃ j, H = F.terms j) ∨ (∃ j, H = F.quotients j) →
          (@IsCommonStageLisse l _ Ω _ _ _
            ((constantExtensionDatum D m hm).geometricFiber C₀).left
            (sfWeilPrimeInvertible (constantExtensionDatum D m hm) l hl C₀)
            ((zlCurveRestriction D l hl Ω X₀ m hm C₀ h₀ R).obj
              ((RX.weil D l hl Ω X₀).obj H)).obj.carrier) ∧
          ZlCurveLocalConclusions D l hl Ω X₀ m hm C₀ h₀ R c.underlying
            ((RX.weil D l hl Ω X₀).obj H)) ∧
        (SfIsReal D l hl Ω X₀ iota.toRingHom G →
          SfIsReal (constantExtensionDatum D m hm) l hl Ω C₀ iota.toRingHom
            ((zlCurveRestriction D l hl Ω X₀ m hm C₀ h₀ R).obj G))

end WeilConjectures
