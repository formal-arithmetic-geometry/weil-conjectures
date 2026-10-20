/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q14
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Sheaf.AlgebraicGeometry.PureDimension
public import Sheaf.SixFunctors.CoefQbarVerdier
public import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
public import Sheaf.Paper.SfLocalizationAllStages
public import Sheaf.Paper.RationalCoefficientCategoryComparison
public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.Paper.SfWeilSheafComplex
public import Sheaf.Paper.WeilIndSheafCategory
public import Sheaf.Paper.FrobeniusCoefficientTwistsCanonical
public import Sheaf.Paper.FieldWeilShriekShiftData
public import Sheaf.Paper.PuritySourceTransports
public import Sheaf.Paper.ConstantWeilStructure
public import Sheaf.Paper.CommonStageCompactWeilCohomology

/-!
# Rational Verdier duality on a geometric finite-field curve

Source: the blueprint of the Weil conjectures, `thm-a1-curve-perverse-heart.proof.md`,
Steps 2--3 (blueprint: lem-a1-qbar-curve-duality).

All operations below refer to the recorded coefficient-passage constructions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option linter.style.setOption false
set_option maxHeartbeats 800000
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme

namespace WeilConjectures
namespace QbarCurve


open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)
open GeneralAlgebraicallyClosedCoefficients (Stage inclusion transition)

variable (D : FiniteFieldDatum.{u}) (P : D.CoefficientDatum)

/-- The rational pullback with the residue-field units furnished by the fixed datum.
Source: curve-heart proof, Steps 2--3 (blueprint: lem-a1-qbar-curve-duality). -/
def finitePull {X Y : Scheme.{u}} [X.Over (Spec (.of D.k))]
    [Y.Over (Spec (.of D.k))] (f : X ⟶ Y) (E : Index P.l P.Qbar) :
    Stage P.l P.Qbar Y E ⥤ Stage P.l P.Qbar X E :=
  @rationalDerivedPullback P.l _ (Coefficient.{u} P.l P.Qbar E) _ _ _ X Y f
    (RationalVerdier.units D P.l P.different X)
    (RationalVerdier.units D P.l P.different Y)

variable (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

/-- Duality on T means the specified internal Hom into the actual exceptional
pullback of the coefficient unit, with evaluation-normalized biduality.
Source: curve-heart proof, Step 2 (blueprint: lem-a1-qbar-curve-duality). -/
structure Dual where
  [noetherian : IsNoetherian X]
  [dimension : Fact (∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))]
  [invertible : Fact (∀ x : X, IsUnit (P.l : X.presheaf.stalk x))]
  verdier : CoefQbarVerdier.Duality D P.l P.different P.Qbar X
  internalHom : CoefQbarVerdier.InternalHom D P.l P.different P.Qbar X verdier
  exceptional : CoefQbarVerdier.Dualizing D P.l P.different P.Qbar X verdier

/-- The actual source comparison on a finite representative: first identify the
Verdier dual by its recorded finite-stage comparison, then use canonical pullback.
Source: curve-heart proof, scalar clause (blueprint: lem-a1-qbar-curve-duality). -/
def sourceComparison (B : Dual D P X)
    {T : Scheme.{u}} [T.Over (Spec (.of D.k))] (f : T ⟶ X)
    (E : Index P.l P.Qbar) (K : Stage P.l P.Qbar X E) :
    (CoefQbarPullback D P.l P.different P.Qbar f).obj
        (B.verdier.duality.dual.obj (op ((inclusion E).obj K))) ≅
      (inclusion E).obj
        ((finitePull D P f E).obj ((B.verdier.finite.datum E).dual.obj (op K))) :=
  (CoefQbarPullback D P.l P.different P.Qbar f).mapIso
      ((B.verdier.comparison E).symm.app (op K)) ≪≫
    (CoefQbarVerdier.pullbackInclusion D P.l P.different P.Qbar T f E
      ((B.verdier.finite.datum E).dual.obj (op K))).symm

/-- The actual scalar/pullback comparison, conjugated by the recorded transitions.
Source: curve-heart proof, scalar clause (blueprint: lem-a1-qbar-curve-duality). -/
def pullScalar {T : Scheme.{u}} [T.Over (Spec (.of D.k))] (f : T ⟶ X)
    (E F : Index P.l P.Qbar) (h : E ≤ F) (K : Stage P.l P.Qbar X E) :
    (transition P.l P.Qbar T E F h).obj ((finitePull D P f E).obj K) ≅
      (finitePull D P f F).obj ((transition P.l P.Qbar X E F h).obj K) :=
  (@rationalPullbackScalarComparison P.l _ (Coefficient.{u} P.l P.Qbar E) _ _ _
    (Coefficient.{u} P.l P.Qbar F) _ _ _ (coefficientInclusion P.l P.Qbar E F h)
    T X f (RationalVerdier.units D P.l P.different T)
      (RationalVerdier.units D P.l P.different X)).app K

/-- The finite-stage smooth orientation, with the actual exceptional dualizing object
and the recorded Tate line as endpoints. Its common-stage map is obtained by inclusion.
Source: curve-heart proof, Step 2 (blueprint: lem-a1-qbar-curve-duality). -/
abbrev SmoothOrientation (B : Dual D P X) (d : ℕ) (E : Index P.l P.Qbar) :=
  (sfRationalConstructibleLocalization P.l (Coefficient.{u} P.l P.Qbar E) X).obj
      (B.verdier.finite.omega E).omega ≅
    (shiftFunctor (Stage P.l P.Qbar X E) (2 * (d : ℤ))).obj
      (@sfRationalTwistingCoefficient P.l _ (Coefficient.{u} P.l P.Qbar E) _ _ _ X
        (RationalVerdier.units D P.l P.different X) (d : ℤ))

/-- The smooth common-stage identification is this finite orientation followed by
its canonical inclusion/shift comparison, so it is a finite-coefficient map.
Source: curve-heart proof, Step 2 (blueprint: lem-a1-qbar-curve-duality). -/
def smoothIdentification (B : Dual D P X) (d : ℕ)
    (o : SmoothOrientation D P X B d (Padic.finiteCoefficientBase P.l P.Qbar)) :
    B.verdier.omega ≅
      (shiftFunctor (generalAlgebraicallyClosedConstructibleCategory P.l P.Qbar X)
        (2 * (d : ℤ))).obj
        (@sfQbarTwistingCoefficient P.l _ X (RationalVerdier.units D P.l P.different X)
          P.Qbar _ _ _ (d : ℤ)) :=
  (B.verdier.omegaComparison (Padic.finiteCoefficientBase P.l P.Qbar)).symm ≪≫
    (inclusion (Padic.finiteCoefficientBase P.l P.Qbar)).mapIso o ≪≫
    ((inclusion (Y := X) (Padic.finiteCoefficientBase P.l P.Qbar)).commShiftIso
      (2 * (d : ℤ))).app _

/-- Scalar transport of the shifted Tate line, with the recorded root-line and
shift comparisons. Source: curve-heart proof, scalar clause
(blueprint: lem-a1-qbar-curve-duality). -/
def orientationTargetScalar (d : ℕ) (E F : Index P.l P.Qbar) (h : E ≤ F) :
    (transition P.l P.Qbar X E F h).obj
        ((shiftFunctor (Stage P.l P.Qbar X E) (2 * (d : ℤ))).obj
          (@sfRationalTwistingCoefficient P.l _ (Coefficient.{u} P.l P.Qbar E) _ _ _ X
            (RationalVerdier.units D P.l P.different X) (d : ℤ))) ≅
      (shiftFunctor (Stage P.l P.Qbar X F) (2 * (d : ℤ))).obj
        (@sfRationalTwistingCoefficient P.l _ (Coefficient.{u} P.l P.Qbar F) _ _ _ X
          (RationalVerdier.units D P.l P.different X) (d : ℤ)) :=
  (Functor.commShiftIso (transition P.l P.Qbar X E F h)
    (self := GeneralAlgebraicallyClosedCoefficients.transitionCommShift P.l P.Qbar X E F h)
    (2 * (d : ℤ))).app _ ≪≫
    (shiftFunctor _ (2 * (d : ℤ))).mapIso
      (@RationalSmoothPurityCanonical.lineScalar P.l _ (Coefficient.{u} P.l P.Qbar E) _ _ _
        (Coefficient.{u} P.l P.Qbar F) _ _ _ (coefficientInclusion P.l P.Qbar E F h) X
        (RationalVerdier.units D P.l P.different X) (d : ℤ))

/-- The finite smooth orientations commute with the actual dualizing and Tate-line
scalar maps, including identity extensions. Source: curve-heart proof, scalar clause
(blueprint: lem-a1-qbar-curve-duality). -/
def OrientationScalar (B : Dual D P X) (d : ℕ)
    (o : ∀ E : Index P.l P.Qbar, SmoothOrientation D P X B d E) : Prop :=
  ∀ (E F : Index P.l P.Qbar) (h : E ≤ F),
    (transition P.l P.Qbar X E F h).map (o E).hom ≫
        (orientationTargetScalar D P X d E F h).hom =
      (B.verdier.finite.scalar E F h).omega.hom ≫ (o F).hom

variable (C U Z : Scheme.{u})
  [C.Over (Spec (.of D.k))] [U.Over (Spec (.of D.k))] [Z.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (C ↘ Spec (.of D.k))] [QuasiCompact (C ↘ Spec (.of D.k))]
  [IsSeparated (C ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (U ↘ Spec (.of D.k))] [QuasiCompact (U ↘ Spec (.of D.k))]
  [IsSeparated (U ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Z ↘ Spec (.of D.k))] [QuasiCompact (Z ↘ Spec (.of D.k))]
  [IsSeparated (Z ↘ Spec (.of D.k))]
  (j : U ⟶ C) (i : Z ⟶ C)
  [openImmersion : IsOpenImmersion j] [closedImmersion : IsClosedImmersion i]

/-- The actual closed direct-image adjunction at all finite fields and the common
stage; these are the counit-normalized operations of supported localization.
Source: curve-heart proof, Step 3 (blueprint: lem-a1-qbar-curve-duality). -/
abbrev Localization := SfAlgebraicallyClosedLocalization P.l P.Qbar D.k
  (finiteFieldDatumPrimeUnit D P.l P.different) (C ↘ Spec (.of D.k)) i j

/-- The right endpoint of the open comparison on a finite representative.
Source: curve-heart proof, scalar clause (blueprint: lem-a1-qbar-curve-duality). -/
def openTargetComparison (BU : Dual D P U)
    (E : Index P.l P.Qbar) (K : Stage P.l P.Qbar C E) :
    BU.verdier.duality.dual.obj
        (op ((CoefQbarPullback D P.l P.different P.Qbar j).obj ((inclusion E).obj K))) ≅
      (inclusion E).obj
        ((BU.verdier.finite.datum E).dual.obj (op ((finitePull D P j E).obj K))) :=
  BU.verdier.duality.dual.mapIso
      (CoefQbarVerdier.pullbackInclusion D P.l P.different P.Qbar U j E K).op ≪≫
    (BU.verdier.comparison E).symm.app (op ((finitePull D P j E).obj K))

/-- The right endpoint of the closed comparison, using precisely the localization
right adjoint and its recorded finite-stage exceptional comparison.
Source: curve-heart proof, scalar clause (blueprint: lem-a1-qbar-curve-duality). -/
def closedTargetComparison (BZ : Dual D P Z) (L : Localization D P C U Z j i)
    (E : Index P.l P.Qbar) (K : Stage P.l P.Qbar C E) :
    BZ.verdier.duality.dual.obj (op (L.supported.exceptional.obj ((inclusion E).obj K))) ≅
      (inclusion E).obj
        ((BZ.verdier.finite.datum E).dual.obj (op ((L.stages E).supported.exceptional.obj K))) :=
  BZ.verdier.duality.dual.mapIso ((L.comparison E).exceptional.symm.app K).op ≪≫
    (BZ.verdier.comparison E).symm.app (op ((L.stages E).supported.exceptional.obj K))

/-- The common and finite comparison maps, with descent equations on their actual
components. Naturality concerns the entire functors. Scalar equations include E = F.
Source: curve-heart proof, Steps 2--3 and scalar clause
(blueprint: lem-a1-qbar-curve-duality). -/
structure Comparisons (BC : Dual D P C) (BU : Dual D P U) (BZ : Dual D P Z)
    (L : Localization D P C U Z j i) where
  openIso : BC.verdier.duality.dual ⋙ CoefQbarPullback D P.l P.different P.Qbar j ≅
    (CoefQbarPullback D P.l P.different P.Qbar j).op ⋙ BU.verdier.duality.dual
  closedIso : BC.verdier.duality.dual ⋙ CoefQbarPullback D P.l P.different P.Qbar i ≅
    L.supported.exceptional.op ⋙ BZ.verdier.duality.dual
  finiteOpen (E : Index P.l P.Qbar) :
    (BC.verdier.finite.datum E).dual ⋙ finitePull D P j E ≅
      (finitePull D P j E).op ⋙ (BU.verdier.finite.datum E).dual
  finiteClosed (E : Index P.l P.Qbar) :
    (BC.verdier.finite.datum E).dual ⋙ finitePull D P i E ≅
      (L.stages E).supported.exceptional.op ⋙ (BZ.verdier.finite.datum E).dual
  exceptionalScalar (E F : Index P.l P.Qbar) (h : E ≤ F) :
    (L.stages E).supported.exceptional ⋙ transition P.l P.Qbar Z E F h ≅
      transition P.l P.Qbar C E F h ⋙ (L.stages F).supported.exceptional

/-- Descent and scalar equations on the specified natural comparison maps.
Source: curve-heart proof, scalar clause (blueprint: lem-a1-qbar-curve-duality). -/
def ComparisonProperties (BC : Dual D P C) (BU : Dual D P U) (BZ : Dual D P Z)
    (L : Localization D P C U Z j i)
    (B : Comparisons D P C U Z j i BC BU BZ L) : Prop :=
  (∀ (E F : Index P.l P.Qbar) (h : E ≤ F)
      (K : Stage P.l P.Qbar C E),
    HEq
      ((inclusion F).map ((B.exceptionalScalar E F h).hom.app K) ≫
        (L.comparison F).exceptional.inv.app ((transition P.l P.Qbar C E F h).obj K))
      ((CoefQbarVerdier.inclusionTransition P.l P.Qbar Z E F h).hom.app
          ((L.stages E).supported.exceptional.obj K) ≫
        (L.comparison E).exceptional.inv.app K ≫
        L.supported.exceptional.map
          ((CoefQbarVerdier.inclusionTransition P.l P.Qbar C E F h).inv.app K))) ∧
  (∀ (E : Index P.l P.Qbar) (K : Stage P.l P.Qbar C E),
    HEq
      (B.openIso.hom.app (op ((inclusion E).obj K)))
      ((sourceComparison D P C BC j E K).hom ≫
        (inclusion E).map ((B.finiteOpen E).hom.app (op K)) ≫
          (openTargetComparison D P C U j BU E K).inv)) ∧
  (∀ (E F : Index P.l P.Qbar) (h : E ≤ F) (K : Stage P.l P.Qbar C E),
    HEq
      ((transition P.l P.Qbar U E F h).map ((B.finiteOpen E).hom.app (op K)) ≫
        (BU.verdier.finite.beta E F h).hom.app (op ((finitePull D P j E).obj K)) ≫
        (BU.verdier.finite.datum F).dual.map ((pullScalar D P C j E F h K).inv).op)
      ((pullScalar D P C j E F h ((BC.verdier.finite.datum E).dual.obj (op K))).hom ≫
        (finitePull D P j F).map ((BC.verdier.finite.beta E F h).hom.app (op K)) ≫
        (B.finiteOpen F).hom.app (op ((transition P.l P.Qbar C E F h).obj K)))) ∧
  (∀ (E : Index P.l P.Qbar) (K : Stage P.l P.Qbar C E),
    HEq
      (B.closedIso.hom.app (op ((inclusion E).obj K)))
      ((sourceComparison D P C BC i E K).hom ≫
        (inclusion E).map ((B.finiteClosed E).hom.app (op K)) ≫
          (closedTargetComparison D P C U Z j i BZ L E K).inv)) ∧
  (∀ (E F : Index P.l P.Qbar) (h : E ≤ F) (K : Stage P.l P.Qbar C E),
    HEq
      ((transition P.l P.Qbar Z E F h).map ((B.finiteClosed E).hom.app (op K)) ≫
        (BZ.verdier.finite.beta E F h).hom.app
          (op ((L.stages E).supported.exceptional.obj K)) ≫
        (BZ.verdier.finite.datum F).dual.map ((B.exceptionalScalar E F h).inv.app K).op)
      ((pullScalar D P C i E F h ((BC.verdier.finite.datum E).dual.obj (op K))).hom ≫
        (finitePull D P i F).map ((BC.verdier.finite.beta E F h).hom.app (op K)) ≫
        (B.finiteClosed F).hom.app (op ((transition P.l P.Qbar C E F h).obj K))))

/-- All data in the curve-duality statement.  The three dualities are the
recorded coefficient-passage Verdier dualities, rather than arbitrary
contravariant functors.  The internal-Hom and dualizing fields therefore bind
`D_T` to `RHom(-,Ra_T^! Lambda)` and its evaluation, while `localization` binds
the exceptional functor to the closed supported-localization construction.
Source: the blueprint proof, Steps 2--3 (blueprint: lem-a1-qbar-curve-duality). -/
structure Data where
  dualC : Dual D P C
  dualU : Dual D P U
  dualZ : Dual D P Z
  coefficientSystem : FdCoefficientComparisonSystem.{u} P.l P.Qbar
  orientationC : ∀ E : Index P.l P.Qbar, SmoothOrientation D P C dualC 1 E
  orientationU : ∀ E : Index P.l P.Qbar, SmoothOrientation D P U dualU 1 E
  orientationZ : ∀ E : Index P.l P.Qbar, SmoothOrientation D P Z dualZ 0 E
  scalarC : OrientationScalar D P C dualC 1 orientationC
  scalarU : OrientationScalar D P U dualU 1 orientationU
  scalarZ : OrientationScalar D P Z dualZ 0 orientationZ
  localization : Localization D P C U Z j i
  comparisons : Comparisons D P C U Z j i dualC dualU dualZ localization
  comparisonProperties :
    ComparisonProperties D P C U Z j i dualC dualU dualZ localization comparisons
end QbarCurve

namespace QbarCurve


variable (D : FiniteFieldDatum.{u}) (P : D.CoefficientDatum)
  (T₀ : Over (Spec (.of D.k₀)))
  [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom] [IsSeparated T₀.hom]

/-- Finite type on the geometric fibre is the base-change instance for its second
projection. Source: curve-heart proof, finite-field scope
(blueprint: lem-a1-qbar-curve-duality). -/
instance fiberLocallyOfFiniteType :
    LocallyOfFiniteType
      (((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).obj T₀).left ↘
        Spec (.of D.k)) :=
  inferInstanceAs (LocallyOfFiniteType (pullback.snd T₀.hom
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))

/-- Quasi-compactness is inherited by the geometric base change.
Source: curve-heart proof, finite-field scope (blueprint: lem-a1-qbar-curve-duality). -/
instance fiberQuasiCompact :
    QuasiCompact
      (((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).obj T₀).left ↘
        Spec (.of D.k)) :=
  inferInstanceAs (QuasiCompact (pullback.snd T₀.hom
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))

/-- Separatedness is inherited by the geometric base change.
Source: curve-heart proof, finite-field scope (blueprint: lem-a1-qbar-curve-duality). -/
instance fiberSeparated :
    IsSeparated
      (((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).obj T₀).left ↘
        Spec (.of D.k)) :=
  inferInstanceAs (IsSeparated (pullback.snd T₀.hom
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))

/-- Separatedness for the named geometric fibre follows from the same pullback instance.
Source: curve-heart proof, finite-field scope (blueprint: lem-a1-qbar-curve-duality). -/
instance geometricFiberSeparated :
    IsSeparated ((D.geometricFiber T₀).left ↘ Spec (.of D.k)) :=
  inferInstanceAs (IsSeparated (pullback.snd T₀.hom
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))

/-- The right-adjoint Frobenius comparison is precisely the mate of inverse compact-support
exchange. This generic formula keeps all category endpoints explicit.
Source: curve-heart proof, Weil clause; purity and trace
(blueprint: lem-a1-qbar-curve-duality). -/
def ExceptionalFrobeniusNormalized
    {A B : Type (u + 1)} [Category.{u + 1} A] [Category.{u + 1} B]
    (F : A ⥤ B) (G : B ⥤ A) (ΦA : A ⥤ A) (ΦB : B ⥤ B)
    (adj : F ⊣ G) (exchange : F ⋙ ΦB ≅ ΦA ⋙ F)
    (comparison : G ⋙ ΦA ≅ ΦB ⋙ G) : Prop :=
  comparison.hom =
    (mateEquiv adj adj (TwoSquare.mk ΦA F F ΦB exchange.inv)).natTrans

/-- The actual exceptional operation at the structure map of the finite-field model.
Its Frobenius comparison is fixed by the counit equation for the canonical compact-support
exchange. The carrier equality normalizes the dualizing object as the value of this
right adjoint on the canonical constant point object; no smooth orientation occurs here.
Source: curve-heart proof, Steps 2--3 and Weil clause; thm-pur-weil-equivariance-of-purity-
and-trace (blueprint: lem-a1-qbar-curve-duality). -/
structure WeilDualizing (B : Dual D P (D.geometricFiber T₀).left) where
  compactification : Compactification T₀.hom
  right : generalAlgebraicallyClosedConstructibleCategory P.l P.Qbar
      (D.geometricFiber (sfWeilCohomologyPoint D)).left ⥤
    generalAlgebraicallyClosedConstructibleCategory P.l P.Qbar (D.geometricFiber T₀).left
  adjunction : zlCommonStageShriek D P.l P.different P.Qbar
    (Over.homMk T₀.hom : T₀ ⟶ sfWeilCohomologyPoint D) compactification ⊣ right
  frobenius : right ⋙ sfCommonStageWeilFrobeniusPullback D P.l P.different T₀ P.Qbar ≅
    sfCommonStageWeilFrobeniusPullback D P.l P.different (sfWeilCohomologyPoint D) P.Qbar ⋙
      right
  normalized : ExceptionalFrobeniusNormalized
    (zlCommonStageShriek D P.l P.different P.Qbar
      (Over.homMk T₀.hom : T₀ ⟶ sfWeilCohomologyPoint D) compactification) right
    (sfCommonStageWeilFrobeniusPullback D P.l P.different T₀ P.Qbar)
    (sfCommonStageWeilFrobeniusPullback D P.l P.different (sfWeilCohomologyPoint D) P.Qbar)
    adjunction (zlShriekFrobenius D P.l P.different P.Qbar
      (Over.homMk T₀.hom : T₀ ⟶ sfWeilCohomologyPoint D) compactification) frobenius
  omega_eq : B.verdier.omega = right.obj
    (constantWeilAlgebraicallyClosedComplex P.l D P.different
      (sfWeilCohomologyPoint D) P.Qbar).carrier

/-- The induced dualizing Frobenius is the exceptional-adjunction mate evaluated on the
canonical coefficient unit, followed by exceptional image of its canonical Weil action.
Only the carrier equality is transported. In particular this construction has no
orientation argument. Source: curve-heart proof, Weil clause; purity and trace
(blueprint: lem-a1-qbar-curve-duality). -/
def omegaFrobenius (B : Dual D P (D.geometricFiber T₀).left)
    (A : WeilDualizing D P T₀ B) :
    (sfCommonStageWeilFrobeniusPullback D P.l P.different T₀ P.Qbar).obj
      B.verdier.omega ≅ B.verdier.omega :=
  (sfCommonStageWeilFrobeniusPullback D P.l P.different T₀ P.Qbar).mapIso
      (eqToIso A.omega_eq) ≪≫
    A.frobenius.app (constantWeilAlgebraicallyClosedComplex P.l D P.different
      (sfWeilCohomologyPoint D) P.Qbar).carrier ≪≫
    A.right.mapIso (constantWeilAlgebraicallyClosedComplex P.l D P.different
      (sfWeilCohomologyPoint D) P.Qbar).str ≪≫ (eqToIso A.omega_eq).symm

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- The prescribed Frobenius of the shifted Tate coefficient, built solely from the
root-line action and canonical shift comparison.
Source: curve-heart proof, Step 2 and Weil clause
(blueprint: lem-a1-qbar-curve-duality). -/
def tateFrobenius (d : ℕ) :
    (sfCommonStageWeilFrobeniusPullback D P.l P.different T₀ P.Qbar).obj
      ((shiftFunctor (generalAlgebraicallyClosedConstructibleCategory P.l P.Qbar
        (D.geometricFiber T₀).left) (2 * (d : ℤ))).obj
        (@sfQbarTwistingCoefficient P.l _ (D.geometricFiber T₀).left
          (RationalVerdier.units D P.l P.different (D.geometricFiber T₀).left)
          P.Qbar _ _ _ (d : ℤ))) ≅
      (shiftFunctor (generalAlgebraicallyClosedConstructibleCategory P.l P.Qbar
        (D.geometricFiber T₀).left) (2 * (d : ℤ))).obj
        (@sfQbarTwistingCoefficient P.l _ (D.geometricFiber T₀).left
          (RationalVerdier.units D P.l P.different (D.geometricFiber T₀).left)
          P.Qbar _ _ _ (d : ℤ)) :=
  ((sfCommonStageWeilFrobeniusPullback D P.l P.different T₀ P.Qbar).commShiftIso
      (2 * (d : ℤ))).app _ ≪≫
    (shiftFunctor _ (2 * (d : ℤ))).mapIso
      (@FrobeniusCoefficientTwists.commonDerivedLineMap P.l _ P.Qbar _ _ _ _ _
        (D.geometricFrobenius T₀).hom (CategoryTheory.Iso.isIso_hom _)
        (sfWeilPrimeInvertible D P.l P.different T₀)
        (sfWeilPrimeInvertible D P.l P.different T₀) (d : ℤ))

/-- Smooth purity is equivariant for the exceptional-adjunction action and the
prescribed shifted Tate action. This is an equation on the orientation already chosen
in the ordinary conclusion, not a definition of the dualizing action.
Source: curve-heart proof, Step 2; thm-pur-weil-equivariance-of-purity-and-trace
(blueprint: lem-a1-qbar-curve-duality). -/
def WeilOrientation (B : Dual D P (D.geometricFiber T₀).left)
    (A : WeilDualizing D P T₀ B) (d : ℕ)
    (o : SmoothOrientation D P (D.geometricFiber T₀).left B d
      (Padic.finiteCoefficientBase P.l P.Qbar)) : Prop :=
  (sfCommonStageWeilFrobeniusPullback D P.l P.different T₀ P.Qbar).map
      (smoothIdentification D P (D.geometricFiber T₀).left B d o).hom ≫
        (tateFrobenius D P T₀ d).hom =
    (omegaFrobenius D P T₀ B A).hom ≫
      (smoothIdentification D P (D.geometricFiber T₀).left B d o).hom

/-- A dual functor on actual fixed pairs, with its underlying functor fixed
literally to the recorded Verdier dual. Evaluation below determines its
contragredient Frobenius structure uniquely.
Source: curve-heart proof, Step 7 (blueprint: lem-a1-qbar-curve-duality). -/
structure WeilDual (B : Dual D P (D.geometricFiber T₀).left) where
  functor : (sfCommonStageWeilComplex D P.l P.different T₀ P.Qbar)ᵒᵖ ⥤
    sfCommonStageWeilComplex D P.l P.different T₀ P.Qbar
  underlying : functor ⋙ sfCommonStageWeilForget D P.l P.different T₀ P.Qbar =
    (sfCommonStageWeilForget D P.l P.different T₀ P.Qbar).op ⋙ B.verdier.duality.dual
  bidual : 𝟭 (sfCommonStageWeilComplex D P.l P.different T₀ P.Qbar) ≅
    functor.rightOp ⋙ functor
  bidual_underlying (K : sfCommonStageWeilComplex D P.l P.different T₀ P.Qbar) :
    HEq ((sfCommonStageWeilForget D P.l P.different T₀ P.Qbar).map (bidual.hom.app K))
      (B.verdier.duality.bidual.hom.app K.carrier)

/-- Evaluation on a Weil pair uses exactly the recorded Verdier evaluation;
only the carrier equality of the lift is transported.
Source: curve-heart proof, Step 7 (blueprint: lem-a1-qbar-curve-duality). -/
def weilEvaluation (B : Dual D P (D.geometricFiber T₀).left)
    (W : WeilDual D P T₀ B) (K : sfCommonStageWeilComplex D P.l P.different T₀ P.Qbar) :
    (CoefQbarTensor D P.l P.different P.Qbar (D.geometricFiber T₀).left).obj
        (K.carrier, (W.functor.obj (op K)).carrier) ⟶ B.verdier.omega :=
  (CoefQbarTensor D P.l P.different P.Qbar (D.geometricFiber T₀).left).map
      (Prod.mkHom (𝟙 K.carrier) ((eqToIso W.underlying).hom.app (op K))) ≫
    B.verdier.evaluation K.carrier

/-- Evaluation fixes the induced Weil structure on the Verdier dual, using
canonical tensor pullback and the prescribed dualizing Tate action.
Source: curve-heart proof, Step 7 (blueprint: lem-a1-qbar-curve-duality). -/
def WeilEvaluation (B : Dual D P (D.geometricFiber T₀).left)
    (W : WeilDual D P T₀ B)
    (θ : (sfCommonStageWeilFrobeniusPullback D P.l P.different T₀ P.Qbar).obj
      B.verdier.omega ≅ B.verdier.omega) : Prop :=
  ∀ K : sfCommonStageWeilComplex D P.l P.different T₀ P.Qbar,
    (sfCommonStageWeilFrobeniusPullback D P.l P.different T₀ P.Qbar).map
        (weilEvaluation D P T₀ B W K) ≫ θ.hom =
      (@canonicalCommonStagePullbackTensor P.l _ P.Qbar _ _ _ _ _
        (D.geometricFrobenius T₀).hom
        (sfWeilPrimeInvertible D P.l P.different T₀)
        (sfWeilPrimeInvertible D P.l P.different T₀)
        K.carrier (W.functor.obj (op K)).carrier).hom ≫
      (CoefQbarTensor D P.l P.different P.Qbar (D.geometricFiber T₀).left).map
        (Prod.mkHom K.str.hom (W.functor.obj (op K)).str.hom) ≫
      weilEvaluation D P T₀ B W K

/-- Canonical pullback of Weil pairs through the normalized geometric-Frobenius
square; this acts on the pairs of def-weil-weil-sheaf-complex.
Source: curve-heart proof, Step 7 (blueprint: lem-a1-qbar-curve-duality). -/
def weilPull {A₀ B₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType A₀.hom] [QuasiCompact A₀.hom]
    [LocallyOfFiniteType B₀.hom] [QuasiCompact B₀.hom] (f₀ : A₀ ⟶ B₀) :
    sfCommonStageWeilComplex D P.l P.different B₀ P.Qbar ⥤
      sfCommonStageWeilComplex D P.l P.different A₀ P.Qbar :=
  Endofunctor.IsoAlgebra.mapOfNatIso (zlFrobeniusSquare D P.l P.different P.Qbar f₀)

/-- The actual comparisons lift to fixed pairs. The closed Weil direct image is
fixed as the right adjoint to canonical closed pullback, with the original unit
and counit; the exceptional lift is its right adjoint in supported localization.
Thus all Weil structures are induced by the original operations.
The existential presentation retains these data and equations without generating
projections for the entire dependent Weil package.
Source: curve-heart proof, Steps 2--3 and Step 7
(blueprint: lem-a1-qbar-curve-duality). -/
def WeilData
    (C₀ U₀ Z₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType C₀.hom] [QuasiCompact C₀.hom] [IsSeparated C₀.hom]
    [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom] [IsSeparated U₀.hom]
    [LocallyOfFiniteType Z₀.hom] [QuasiCompact Z₀.hom] [IsSeparated Z₀.hom]
    (j₀ : U₀ ⟶ C₀) (i₀ : Z₀ ⟶ C₀)
    [fiberOpen : IsOpenImmersion (sfLocalizationFiberMap D j₀)]
    [fiberClosed : IsClosedImmersion (sfLocalizationFiberMap D i₀)]
    (B : Data D P (D.geometricFiber C₀).left (D.geometricFiber U₀).left
      (D.geometricFiber Z₀).left (sfLocalizationFiberMap D j₀) (sfLocalizationFiberMap D i₀)
      (openImmersion := fiberOpen) (closedImmersion := fiberClosed)) : Prop :=
  ∃ dualC : (WeilDual D P C₀ (@Data.dualC D P (D.geometricFiber C₀).left (D.geometricFiber U₀).left
      (D.geometricFiber Z₀).left _ _ _ _ _ _ _ _ _ _ _ _
      (sfLocalizationFiberMap D j₀) (sfLocalizationFiberMap D i₀) fiberOpen fiberClosed B)),
  ∃ dualU : (WeilDual D P U₀ (@Data.dualU D P (D.geometricFiber C₀).left (D.geometricFiber U₀).left
      (D.geometricFiber Z₀).left _ _ _ _ _ _ _ _ _ _ _ _
      (sfLocalizationFiberMap D j₀) (sfLocalizationFiberMap D i₀) fiberOpen fiberClosed B)),
  ∃ dualZ : (WeilDual D P Z₀ (@Data.dualZ D P (D.geometricFiber C₀).left (D.geometricFiber U₀).left
      (D.geometricFiber Z₀).left _ _ _ _ _ _ _ _ _ _ _ _
      (sfLocalizationFiberMap D j₀) (sfLocalizationFiberMap D i₀) fiberOpen fiberClosed B)),
  ∃ _coefficientsC : (FdFrobeniusComparison P.l P.Qbar D P.different
    (@Data.coefficientSystem D P (D.geometricFiber C₀).left (D.geometricFiber U₀).left
      (D.geometricFiber Z₀).left _ _ _ _ _ _ _ _ _ _ _ _
      (sfLocalizationFiberMap D j₀) (sfLocalizationFiberMap D i₀) fiberOpen fiberClosed B) C₀),
  ∃ _coefficientsU : (FdFrobeniusComparison P.l P.Qbar D P.different
    (@Data.coefficientSystem D P (D.geometricFiber C₀).left (D.geometricFiber U₀).left
      (D.geometricFiber Z₀).left _ _ _ _ _ _ _ _ _ _ _ _
      (sfLocalizationFiberMap D j₀) (sfLocalizationFiberMap D i₀) fiberOpen fiberClosed B) U₀),
  ∃ _coefficientsZ : (FdFrobeniusComparison P.l P.Qbar D P.different
    (@Data.coefficientSystem D P (D.geometricFiber C₀).left (D.geometricFiber U₀).left
      (D.geometricFiber Z₀).left _ _ _ _ _ _ _ _ _ _ _ _
      (sfLocalizationFiberMap D j₀) (sfLocalizationFiberMap D i₀) fiberOpen fiberClosed B) Z₀),
  ∃ omegaC : (WeilDualizing D P C₀ (@Data.dualC D P (D.geometricFiber C₀).left
      (D.geometricFiber U₀).left
      (D.geometricFiber Z₀).left _ _ _ _ _ _ _ _ _ _ _ _
      (sfLocalizationFiberMap D j₀) (sfLocalizationFiberMap D i₀) fiberOpen fiberClosed B)),
  ∃ omegaU : (WeilDualizing D P U₀ (@Data.dualU D P (D.geometricFiber C₀).left
      (D.geometricFiber U₀).left
      (D.geometricFiber Z₀).left _ _ _ _ _ _ _ _ _ _ _ _
      (sfLocalizationFiberMap D j₀) (sfLocalizationFiberMap D i₀) fiberOpen fiberClosed B)),
  ∃ omegaZ : (WeilDualizing D P Z₀ (@Data.dualZ D P (D.geometricFiber C₀).left
      (D.geometricFiber U₀).left
      (D.geometricFiber Z₀).left _ _ _ _ _ _ _ _ _ _ _ _
      (sfLocalizationFiberMap D j₀) (sfLocalizationFiberMap D i₀) fiberOpen fiberClosed B)),
  ∃ _orientationC : (WeilOrientation D P C₀ (@Data.dualC D P (D.geometricFiber C₀).left
      (D.geometricFiber U₀).left
      (D.geometricFiber Z₀).left _ _ _ _ _ _ _ _ _ _ _ _
      (sfLocalizationFiberMap D j₀) (sfLocalizationFiberMap D i₀) fiberOpen fiberClosed B) omegaC 1
    ((@Data.orientationC D P (D.geometricFiber C₀).left (D.geometricFiber U₀).left
      (D.geometricFiber Z₀).left _ _ _ _ _ _ _ _ _ _ _ _
      (sfLocalizationFiberMap D j₀) (sfLocalizationFiberMap D i₀) fiberOpen fiberClosed B) _)),
  ∃ _orientationU : (WeilOrientation D P U₀ (@Data.dualU D P (D.geometricFiber C₀).left
      (D.geometricFiber U₀).left
      (D.geometricFiber Z₀).left _ _ _ _ _ _ _ _ _ _ _ _
      (sfLocalizationFiberMap D j₀) (sfLocalizationFiberMap D i₀) fiberOpen fiberClosed B) omegaU 1
    ((@Data.orientationU D P (D.geometricFiber C₀).left (D.geometricFiber U₀).left
      (D.geometricFiber Z₀).left _ _ _ _ _ _ _ _ _ _ _ _
      (sfLocalizationFiberMap D j₀) (sfLocalizationFiberMap D i₀) fiberOpen fiberClosed B) _)),
  ∃ _orientationZ : (WeilOrientation D P Z₀ (@Data.dualZ D P (D.geometricFiber C₀).left
      (D.geometricFiber U₀).left
      (D.geometricFiber Z₀).left _ _ _ _ _ _ _ _ _ _ _ _
      (sfLocalizationFiberMap D j₀) (sfLocalizationFiberMap D i₀) fiberOpen fiberClosed B) omegaZ 0
    ((@Data.orientationZ D P (D.geometricFiber C₀).left (D.geometricFiber U₀).left
      (D.geometricFiber Z₀).left _ _ _ _ _ _ _ _ _ _ _ _
      (sfLocalizationFiberMap D j₀) (sfLocalizationFiberMap D i₀) fiberOpen fiberClosed B) _)),
  ∃ _evaluationC : (WeilEvaluation D P C₀ (@Data.dualC D P (D.geometricFiber C₀).left
      (D.geometricFiber U₀).left
      (D.geometricFiber Z₀).left _ _ _ _ _ _ _ _ _ _ _ _
      (sfLocalizationFiberMap D j₀) (sfLocalizationFiberMap D i₀) fiberOpen fiberClosed B) dualC
    (omegaFrobenius D P C₀ (@Data.dualC D P (D.geometricFiber C₀).left
      (D.geometricFiber U₀).left
      (D.geometricFiber Z₀).left _ _ _ _ _ _ _ _ _ _ _ _
      (sfLocalizationFiberMap D j₀) (sfLocalizationFiberMap D i₀) fiberOpen fiberClosed B) omegaC)),
  ∃ _evaluationU : (WeilEvaluation D P U₀ (@Data.dualU D P (D.geometricFiber C₀).left
      (D.geometricFiber U₀).left
      (D.geometricFiber Z₀).left _ _ _ _ _ _ _ _ _ _ _ _
      (sfLocalizationFiberMap D j₀) (sfLocalizationFiberMap D i₀) fiberOpen fiberClosed B) dualU
    (omegaFrobenius D P U₀ (@Data.dualU D P (D.geometricFiber C₀).left
      (D.geometricFiber U₀).left
      (D.geometricFiber Z₀).left _ _ _ _ _ _ _ _ _ _ _ _
      (sfLocalizationFiberMap D j₀) (sfLocalizationFiberMap D i₀) fiberOpen fiberClosed B) omegaU)),
  ∃ _evaluationZ : (WeilEvaluation D P Z₀ (@Data.dualZ D P (D.geometricFiber C₀).left
      (D.geometricFiber U₀).left
      (D.geometricFiber Z₀).left _ _ _ _ _ _ _ _ _ _ _ _
      (sfLocalizationFiberMap D j₀) (sfLocalizationFiberMap D i₀) fiberOpen fiberClosed B) dualZ
    (omegaFrobenius D P Z₀ (@Data.dualZ D P (D.geometricFiber C₀).left
      (D.geometricFiber U₀).left
      (D.geometricFiber Z₀).left _ _ _ _ _ _ _ _ _ _ _ _
      (sfLocalizationFiberMap D j₀) (sfLocalizationFiberMap D i₀) fiberOpen fiberClosed B) omegaZ)),
  ∃ localization : (SfWeilLocalization (@SfAlgebraicallyClosedLocalization.supported P.l _
      P.Qbar _ _ _ D.k _
      (finiteFieldDatumPrimeUnit D P.l P.different)
      (D.geometricFiber C₀).left (D.geometricFiber Z₀).left (D.geometricFiber U₀).left
      ((D.geometricFiber C₀).left ↘ Spec (.of D.k))
      (sfLocalizationFiberMap D i₀) (sfLocalizationFiberMap D j₀)
      fiberClosed fiberOpen (@Data.localization D P (D.geometricFiber C₀).left (D.geometricFiber
          U₀).left
      (D.geometricFiber Z₀).left _ _ _ _ _ _ _ _ _ _ _ _
      (sfLocalizationFiberMap D j₀) (sfLocalizationFiberMap D i₀) fiberOpen fiberClosed B))
    (sfCommonStageWeilFrobeniusPullback D P.l P.different C₀ P.Qbar)
    (sfCommonStageWeilFrobeniusPullback D P.l P.different Z₀ P.Qbar)
    (sfCommonStageWeilFrobeniusPullback D P.l P.different U₀ P.Qbar)),
  ∃ closedAdjunction : (weilPull D P i₀ ⊣ localization.closedLift),
  ∃ _closedUnit : (∀ (K : sfCommonStageWeilComplex D P.l P.different C₀ P.Qbar),
HEq ((sfCommonStageWeilForget D P.l P.different C₀ P.Qbar).map
      (closedAdjunction.unit.app K))
      ((@SfAlgebraicallyClosedLocalization.supported P.l _ P.Qbar _ _ _ D.k _
      (finiteFieldDatumPrimeUnit D P.l P.different)
      (D.geometricFiber C₀).left (D.geometricFiber Z₀).left (D.geometricFiber U₀).left
      ((D.geometricFiber C₀).left ↘ Spec (.of D.k))
      (sfLocalizationFiberMap D i₀) (sfLocalizationFiberMap D j₀)
      fiberClosed fiberOpen (@Data.localization D P (D.geometricFiber C₀).left (D.geometricFiber
          U₀).left
      (D.geometricFiber Z₀).left _ _ _ _ _ _ _ _ _ _ _ _
      (sfLocalizationFiberMap D j₀) (sfLocalizationFiberMap D i₀) fiberOpen fiberClosed
          B)).closedAdjunction.unit.app K.carrier)),
  ∃ _closedCounit : (∀ (K : sfCommonStageWeilComplex D P.l P.different Z₀ P.Qbar),
HEq ((sfCommonStageWeilForget D P.l P.different Z₀ P.Qbar).map
      (closedAdjunction.counit.app K))
      ((@SfAlgebraicallyClosedLocalization.supported P.l _ P.Qbar _ _ _ D.k _
      (finiteFieldDatumPrimeUnit D P.l P.different)
      (D.geometricFiber C₀).left (D.geometricFiber Z₀).left (D.geometricFiber U₀).left
      ((D.geometricFiber C₀).left ↘ Spec (.of D.k))
      (sfLocalizationFiberMap D i₀) (sfLocalizationFiberMap D j₀)
      fiberClosed fiberOpen (@Data.localization D P (D.geometricFiber C₀).left (D.geometricFiber
          U₀).left
      (D.geometricFiber Z₀).left _ _ _ _ _ _ _ _ _ _ _ _
      (sfLocalizationFiberMap D j₀) (sfLocalizationFiberMap D i₀) fiberOpen fiberClosed
          B)).closedAdjunction.counit.app K.carrier)),
  ∃ openIso : (dualC.functor ⋙ weilPull D P j₀ ≅
    (weilPull D P j₀).op ⋙ dualU.functor),
  ∃ closedIso : (dualC.functor ⋙ weilPull D P i₀ ≅
    localization.exceptionalLift.op ⋙ dualZ.functor),
  ∃ _openUnderlying : (∀ (K : sfCommonStageWeilComplex D P.l P.different C₀ P.Qbar),
HEq ((sfCommonStageWeilForget D P.l P.different U₀ P.Qbar).map
      (openIso.hom.app (op K))) ((Comparisons.openIso (D := D) (P := P)
      (C := (D.geometricFiber C₀).left) (U := (D.geometricFiber U₀).left)
      (Z := (D.geometricFiber Z₀).left)
      (j := sfLocalizationFiberMap D j₀) (i := sfLocalizationFiberMap D i₀)
      (openImmersion := fiberOpen) (closedImmersion := fiberClosed)
      (BC := @Data.dualC D P (D.geometricFiber C₀).left (D.geometricFiber U₀).left
      (D.geometricFiber Z₀).left _ _ _ _ _ _ _ _ _ _ _ _
      (sfLocalizationFiberMap D j₀) (sfLocalizationFiberMap D i₀) fiberOpen fiberClosed B)
      (BU := @Data.dualU D P (D.geometricFiber C₀).left (D.geometricFiber U₀).left
      (D.geometricFiber Z₀).left _ _ _ _ _ _ _ _ _ _ _ _
      (sfLocalizationFiberMap D j₀) (sfLocalizationFiberMap D i₀) fiberOpen fiberClosed B)
      (BZ := @Data.dualZ D P (D.geometricFiber C₀).left (D.geometricFiber U₀).left
      (D.geometricFiber Z₀).left _ _ _ _ _ _ _ _ _ _ _ _
      (sfLocalizationFiberMap D j₀) (sfLocalizationFiberMap D i₀) fiberOpen fiberClosed B)
      (L := @Data.localization D P (D.geometricFiber C₀).left (D.geometricFiber U₀).left
      (D.geometricFiber Z₀).left _ _ _ _ _ _ _ _ _ _ _ _
      (sfLocalizationFiberMap D j₀) (sfLocalizationFiberMap D i₀) fiberOpen fiberClosed B)
      (@Data.comparisons D P (D.geometricFiber C₀).left (D.geometricFiber U₀).left
      (D.geometricFiber Z₀).left _ _ _ _ _ _ _ _ _ _ _ _
      (sfLocalizationFiberMap D j₀) (sfLocalizationFiberMap D i₀) fiberOpen fiberClosed
          B)).hom.app (op K.carrier))),
  ∀ (K : sfCommonStageWeilComplex D P.l P.different C₀ P.Qbar),
HEq ((sfCommonStageWeilForget D P.l P.different Z₀ P.Qbar).map
      (closedIso.hom.app (op K))) ((Comparisons.closedIso (D := D) (P := P)
      (C := (D.geometricFiber C₀).left) (U := (D.geometricFiber U₀).left)
      (Z := (D.geometricFiber Z₀).left)
      (j := sfLocalizationFiberMap D j₀) (i := sfLocalizationFiberMap D i₀)
      (openImmersion := fiberOpen) (closedImmersion := fiberClosed)
      (BC := @Data.dualC D P (D.geometricFiber C₀).left (D.geometricFiber U₀).left
      (D.geometricFiber Z₀).left _ _ _ _ _ _ _ _ _ _ _ _
      (sfLocalizationFiberMap D j₀) (sfLocalizationFiberMap D i₀) fiberOpen fiberClosed B)
      (BU := @Data.dualU D P (D.geometricFiber C₀).left (D.geometricFiber U₀).left
      (D.geometricFiber Z₀).left _ _ _ _ _ _ _ _ _ _ _ _
      (sfLocalizationFiberMap D j₀) (sfLocalizationFiberMap D i₀) fiberOpen fiberClosed B)
      (BZ := @Data.dualZ D P (D.geometricFiber C₀).left (D.geometricFiber U₀).left
      (D.geometricFiber Z₀).left _ _ _ _ _ _ _ _ _ _ _ _
      (sfLocalizationFiberMap D j₀) (sfLocalizationFiberMap D i₀) fiberOpen fiberClosed B)
      (L := @Data.localization D P (D.geometricFiber C₀).left (D.geometricFiber U₀).left
      (D.geometricFiber Z₀).left _ _ _ _ _ _ _ _ _ _ _ _
      (sfLocalizationFiberMap D j₀) (sfLocalizationFiberMap D i₀) fiberOpen fiberClosed B)
      (@Data.comparisons D P (D.geometricFiber C₀).left (D.geometricFiber U₀).left
      (D.geometricFiber Z₀).left _ _ _ _ _ _ _ _ _ _ _ _
      (sfLocalizationFiberMap D j₀) (sfLocalizationFiberMap D i₀) fiberOpen fiberClosed
          B)).hom.app (op K.carrier))

/-- Rational Verdier duality on a smooth geometric finite-field curve.
Source: the blueprint of the Weil conjectures, `thm-a1-curve-perverse-heart.proof.md`,
Steps 2--3 (blueprint: lem-a1-qbar-curve-duality).
Proof (the seven steps of the node):
1. Finite-type schemes over k are noetherian and finite dimensional. The open
and reduced closed complement are finite type and separated. The prime is
invertible. The normalized coefficient equivalence identifies the framework
and PBC categories, their shifts, finite scalar transitions and Weil pairs.
2. Apply coefficient-passage Verdier duality to C, U and Z. Its internal Hom
identification and evaluation give the exact anti-equivalences and biduality;
its exceptional identification fixes omega as Ra^! of the coefficient unit.
3. U is a smooth curve and the reduced boundary is smooth of dimension zero
because k is perfect. Smooth purity in dimensions one, one and zero gives
all three dualizing identifications, including the empty-scheme convention.
4. Dimension-zero purity identifies j* with Rj!. Compose this with the
exceptional-duality formula and dualize using evaluation biduality to obtain
the open natural comparison.
5. Apply the exceptional-duality formula to i, identify its right adjoint
with supported localization, dualize and compose with evaluation biduality.
This gives i* D_C isomorphic to D_Z Ri! as an isomorphism of functors.
6. All factors are the finite-coefficient maps. Their scalar squares compose,
and the canonical line/shift scalar maps give the orientation squares.
7. For a pair descending over k0, the equivariant evaluation, adjunction,
biduality and smooth purity give precisely these comparisons on Weil pairs.
This conditional clause is stated separately in qbarCurveDuality_weil;
exactness always concerns the underlying constructible categories. -/
theorem qbarCurveDuality
    (D : FiniteFieldDatum.{u}) (P : D.CoefficientDatum)
    (C U Z : Scheme.{u})
    [C.Over (Spec (.of D.k))] [U.Over (Spec (.of D.k))] [Z.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (C ↘ Spec (.of D.k))] [QuasiCompact (C ↘ Spec (.of D.k))]
    [IsSeparated (C ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (U ↘ Spec (.of D.k))] [QuasiCompact (U ↘ Spec (.of D.k))]
    [IsSeparated (U ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of D.k))] [QuasiCompact (Z ↘ Spec (.of D.k))]
    [IsSeparated (Z ↘ Spec (.of D.k))]
    [Smooth (C ↘ Spec (.of D.k))] (hCdim : Scheme.IsPureDimension C 1)
    (j : U ⟶ C) (i : Z ⟶ C) [IsOpenImmersion j] [IsClosedImmersion i]
    [j.IsOver (Spec (.of D.k))] [i.IsOver (Spec (.of D.k))]
    (hj : DenseRange j) [IsReduced Z] (hij : Set.range j = (Set.range i)ᶜ) :
    Nonempty (Data D P C U Z j i) := by
  sorry

/-- The conditional Weil clause of rational curve duality, on the actual geometric
base change of a complementary finite-field immersion pair.
Source: curve-heart proof, Steps 2--3, especially its Weil-equivariant localization
(blueprint: lem-a1-qbar-curve-duality).
Proof: use the same finite dualities, evaluation and scalar comparisons as in the
ordinary clause. The geometric-Frobenius square induces canonical pullbacks on Weil
pairs. Transpose the equivariant evaluation through the closed adjunction to give the
induced contragredient dual structure and exceptional structure. The evaluation
biduality and the open and closed comparison formulas then intertwine Frobenius.
Smooth purity gives the shifted Tate structure on the three dualizing objects;
its finite scalar squares descend to the common-stage maps. Finally the normalized
coefficient equivalence commutes with Frobenius, hence identifies the Weil pairs.
No triangulation of the Weil-pair category is asserted. -/
theorem qbarCurveDuality_weil
    (D : FiniteFieldDatum.{u}) (P : D.CoefficientDatum)
    (C₀ U₀ Z₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType C₀.hom] [QuasiCompact C₀.hom] [IsSeparated C₀.hom]
    [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom] [IsSeparated U₀.hom]
    [LocallyOfFiniteType Z₀.hom] [QuasiCompact Z₀.hom] [IsSeparated Z₀.hom]
    (j₀ : U₀ ⟶ C₀) (i₀ : Z₀ ⟶ C₀)
    [IsOpenImmersion j₀.left] [IsClosedImmersion i₀.left]
    [fiberOpen : IsOpenImmersion (sfLocalizationFiberMap D j₀)]
    [fiberClosed : IsClosedImmersion (sfLocalizationFiberMap D i₀)]
    [Smooth ((D.geometricFiber C₀).left ↘ Spec (.of D.k))]
    (hCdim : Scheme.IsPureDimension (D.geometricFiber C₀).left 1)
    (hj : DenseRange (sfLocalizationFiberMap D j₀))
    [IsReduced (D.geometricFiber Z₀).left]
    (hij : Set.range (sfLocalizationFiberMap D j₀) =
      (Set.range (sfLocalizationFiberMap D i₀))ᶜ) :
    ∃ B : Data D P (D.geometricFiber C₀).left (D.geometricFiber U₀).left
      (D.geometricFiber Z₀).left (sfLocalizationFiberMap D j₀) (sfLocalizationFiberMap D i₀)
      (openImmersion := fiberOpen) (closedImmersion := fiberClosed),
      Nonempty (WeilData D P C₀ U₀ Z₀ j₀ i₀
        (fiberOpen := fiberOpen) (fiberClosed := fiberClosed) B) := by
  sorry

end QbarCurve
end WeilConjectures
