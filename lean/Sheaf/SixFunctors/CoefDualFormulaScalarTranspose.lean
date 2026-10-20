/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q69
-/
module

public import Sheaf.SixFunctors.CoefIntegralFiniteExtension
public import Sheaf.Paper.QcqsCompactSupportRealization
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
import Sheaf.Paper.FiniteStageVerdierBiduality
import Sheaf.Paper.PullbackTorAmplitude
import Sheaf.Paper.FiniteTensorConstructibleCohomology
import Sheaf.Paper.FiniteCoefficientFlatModel
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.SixFunctors.Etale.Derived.Adjunctions
import Sheaf.Paper.ProEtaleFiniteCoefficientDirectImage
import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import Sheaf.Paper.FiniteFieldFiber
import Sheaf.Paper.FiniteTorAmplitude
import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
import Sheaf.Paper.SfDerivedDirectImage
import Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage
import Sheaf.Paper.SfIntegralReductionTower
import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Sheaf.Paper.ProEtaleConstructibleOrigin
import Sheaf.Paper.CanonicalOriginCompactSupportComposition
import Sheaf.CategoryTheory.AbsoluteTraceExchange
import Sheaf.Paper.SemilinearDerivedSections
import Sheaf.Paper.CoefDerivedSystemEvaluationCalculus
import WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients
import Sheaf.SixFunctors.IntegralVerdier
import Sheaf.Paper.IntegralOperationsScalarComparisons
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import Sheaf.Paper.FiniteFreeCompletedScalarComparison
import Sheaf.Algebra.Homology.RingedInternalHomSignedCalculus
import Sheaf.Algebra.Homology.RingedInternalHomExactRestriction
import Sheaf.Paper.CoefficientRingedTensorHomModel
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Paper.CoefficientHomRepresentativeEvaluation
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
import Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses
import Sheaf.Paper.DualityPairing
import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Closed
import WeilConjectures.Compactification.NagataCompactification
import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
import WeilConjectures.SixFunctors.Etale.Derived.Dualizing
import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons
public import Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison
public import Sheaf.AlgebraicGeometry.SfOpenExceptionalBaseChange
public import Sheaf.Paper.OrdinaryCompletedIntegralPullback
import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
import Sheaf.Paper.FiniteFreeCoefficientExtension

/-!
# Scalar transpose of the canonical integral exceptional formula

Source: blueprint main-20261015, lem-coef-rational-operations, proof paragraph 8,
Step 15 (blueprint: lem-coef-dual-formula-scalar-transpose).

The trace and evaluation normalizations below specify the formula comparison.
They exclude rescaling an otherwise unspecified exceptional-formula isomorphism.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.CoefDualFormulaScalarTranspose

/-- The specified proper/open support compositor, allowing supplied compactifications.
Source: blueprint Step 2, compact-support composition
(blueprint: lem-coef-dual-formula-scalar-transpose). -/
def finiteSupportComposition (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z)
    (hf : f ≫ g = h) [QuasiCompact f] [QuasiCompact g] [QuasiCompact h]
    [HasCompactification f] [HasCompactification g] [HasCompactification h]
    (c : Compactification f) (d : Compactification g) (e : Compactification h) :
    Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⋙
        Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d ≅
      Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) e := by
  subst h
  exact Functor.isoWhiskerRight (Etale.rightDerivedLowerShriekIso A c) _ ≪≫
    Functor.isoWhiskerLeft _ (Etale.rightDerivedLowerShriekIso A d) ≪≫
    Etale.unboundedEtaleLowerShriekCompIso A f g ≪≫
    (Etale.rightDerivedLowerShriekIso A e).symm

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] (c : Compactification f)

/-- The finite relative trace is the absolute structural counit transposed through
compact-support composition. No exceptional-formula isomorphism is chosen here.
Source: blueprint Step 2, the defining equation for the absolute-trace transpose
(blueprint: lem-coef-dual-formula-scalar-transpose). -/
def finiteEtaleTrace (n : ℕ) :
    (Etale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (finiteDualizingCoeff l E n)) c).obj
      (finiteDualizingEtaleTerm l E D X n) ⟶ finiteDualizingEtaleTerm l E D Y n := by
  letI := c.hasCompactification
  letI := (finiteDualizingCompactification D X).hasCompactification
  letI := (finiteDualizingCompactification D Y).hasCompactification
  exact (finiteDualizingEtaleAdjunction l E D Y n).homEquiv _ _
    ((finiteSupportComposition (finiteDualizingCoeff l E n) f
      (Y ↘ Spec (.of D.k)) (X ↘ Spec (.of D.k))
      (CategoryTheory.comp_over f (Spec (.of D.k))) c (finiteDualizingCompactification D Y)
      (finiteDualizingCompactification D X)).hom.app
        (finiteDualizingEtaleTerm l E D X n) ≫ finiteDualizingEtaleCounit l E D X n)

/-- The finite absolute dualizing object is bounded below on the etale site.
Source: blueprint Step 1, finite Verdier duality
(blueprint: lem-coef-dual-formula-scalar-transpose).
Proof: the coefficient unit is concentrated in degree zero. The bounded-below
exceptional adjoint preserves D+ over the Noetherian finite-dimensional base; apply
its D+ preservation theorem to that unit. -/
theorem finiteEtaleDualizing_plus (W : Scheme.{u})
    [W.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (W ↘ Spec (.of D.k))] [QuasiCompact (W ↘ Spec (.of D.k))]
    [IsSeparated (W ↘ Spec (.of D.k))] (n : ℕ) :
    DerivedCategory.TStructure.t.plus (finiteDualizingEtaleTerm l E D W n) := by
  sorry

/-- The etale-origin support comparison, in intrinsic finite coefficients.
Source: blueprint Steps 1--2, comparison-site realization
(blueprint: lem-coef-dual-formula-scalar-transpose). -/
def finiteSupportOrigin (n : ℕ) :
    (sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (n + 1)) c).obj
        ((finiteDualizingRealization l E X n).obj (finiteDualizingEtaleTerm l E D X n)) ≅
      (finiteDualizingRealization l E Y n).obj
        ((Etale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} (finiteDualizingCoeff l E n)) c).obj
            (finiteDualizingEtaleTerm l E D X n)) :=
  (ProEtale.sfIntrinsicCompactSupportComparison
    (Padic.coefficientExtensionRing l E (n + 1)) c).app
      ((ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} (finiteDualizingCoeff l E n)) X).mapDerivedCategory.obj
          (finiteDualizingEtaleTerm l E D X n)) ≪≫
    (sfIntrinsicDerivedEquivalence Y
      (Padic.coefficientExtensionRing l E (n + 1))).functor.mapIso
        ((ProEtale.compactSupportSiteComparison (finiteDualizingCoeff l E n) c).app
          ⟨finiteDualizingEtaleTerm l E D X n, finiteEtaleDualizing_plus D l E X n⟩)

/-- The canonical finite relative trace after the prescribed site and coefficient transport.
Source: blueprint Step 2, absolute trace
(blueprint: lem-coef-dual-formula-scalar-transpose). -/
def finiteTrace (n : ℕ) :
    (sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (n + 1)) c).obj
      (integralDualizingFiniteTerm l E D X n) ⟶ integralDualizingFiniteTerm l E D Y n :=
  (sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (n + 1)) c).map
      (finiteDualizingOrigin l E D X n).inv ≫
    (finiteSupportOrigin D l E f c n).hom ≫
    (finiteDualizingRealization l E Y n).map (finiteEtaleTrace D l E f c n) ≫
    (finiteDualizingOrigin l E D Y n).hom

/-- Projection normalization for the relative integral dualizing trace.
The finite maps are the structural-counit transposes defined above.
Source: blueprint Steps 2 and 11
(blueprint: lem-coef-dual-formula-scalar-transpose). -/
def TraceNormalized
    (wX : IntegralFiniteExtension.DualizingDatum l X D hl E)
    (wY : IntegralFiniteExtension.DualizingDatum l Y D hl E)
    (t : (sfCompactSupportFiniteIntegralFunctor l D.k
      (PurCompactSupport.coefficientPrimeUnit l D hl) c E).obj wX.omega ⟶ wY.omega) : Prop :=
  ∀ n : ℕ,
    (scalarReductionDerivedExtension l E Y n).map
        ((sfIntegralConstructible l E Y).ι.map t) ≫ (wY.reduction n).hom =
      (sfCompactSupportFiniteReductionIso l D.k
        (PurCompactSupport.coefficientPrimeUnit l D hl) c E wX.omega n).hom ≫
      (sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (n + 1)) c).map
        (wX.reduction n).hom ≫ finiteTrace D l E f c n

/-- The canonical relative trace exists and is fixed by the finite structural traces.
Source: blueprint Steps 2 and 11
(blueprint: lem-coef-dual-formula-scalar-transpose).
Proof: form the simultaneous finite exceptional-adjunction system, including its
coefficient-change counit squares. The absolute support compositor and absolute
counits define its relative trace. Apply the total reduction/limit adjunction to
this system map. The dualizing comparisons identify the result with a map of the
displayed integral objects and give the finite equations. For uniqueness, exceptional
adjunction and the canonical dualizing-composition comparison identify this Hom group
with End(omega_X). Integral Verdier duality identifies that with H^0(X,R_X). The
negative-degree self-Hom of the finite dualizing object vanishes, so the mapping-limit
sequence has no lim^1 term in this degree; the quotient projections separate H^0(X,R_X).
This last argument is specific to the dualizing trace, not a general assertion that
reduction detects arbitrary derived morphisms. -/
theorem trace_existsUnique
    (wX : IntegralFiniteExtension.DualizingDatum l X D hl E)
    (wY : IntegralFiniteExtension.DualizingDatum l Y D hl E) :
    ∃! t : (sfCompactSupportFiniteIntegralFunctor l D.k
        (PurCompactSupport.coefficientPrimeUnit l D hl) c E).obj wX.omega ⟶ wY.omega,
      TraceNormalized D l hl E f c wX wY t := by
  sorry

/-- The relative trace with its unique structural-counit normalization.
Source: blueprint Step 2
(blueprint: lem-coef-dual-formula-scalar-transpose). -/
def trace
    (wX : IntegralFiniteExtension.DualizingDatum l X D hl E)
    (wY : IntegralFiniteExtension.DualizingDatum l Y D hl E) :=
  (trace_existsUnique D l hl E f c wX wY).exists.choose

/-- The two presentations of completed-coefficient direct image agree.
Source: blueprint Step 2, ordinary/completed coefficient identification
(blueprint: lem-coef-dual-formula-scalar-transpose).
Proof: both ring maps have the specified constant-section map after every quotient
projection. The completed-ring limit property identifies the maps. Both pushforwards
are the same sectionwise module pushforward along proEtaleBaseChange f; substitute
the ring-map equality. -/
theorem ordinaryPush_eq :
    ordinaryIntegralModulePush l E f =
      proEtaleRingModuleDirectImage f
        ((PurCompactSupport.completed l E).ring Y)
        ((PurCompactSupport.completed l E).ring X)
        ((PurCompactSupport.completed l E).pull f) := by
  sorry

/-- Canonical comparison of the ordinary module pullback presentations, preserving
adjunction units. Source: blueprint Step 2
(blueprint: lem-coef-dual-formula-scalar-transpose). -/
def ordinaryPullIso :
    proEtaleRingModulePullback f
        ((PurCompactSupport.completed l E).ring Y)
        ((PurCompactSupport.completed l E).ring X)
        ((PurCompactSupport.completed l E).pull f) ≅ ordinaryIntegralModulePull l E f :=
  (proEtaleRingModuleAdjunction f
    ((PurCompactSupport.completed l E).ring Y)
    ((PurCompactSupport.completed l E).ring X)
    ((PurCompactSupport.completed l E).pull f)).leftAdjointUniq
      ((ordinaryIntegralModuleAdjunction l E f).ofNatIsoRight
        (eqToIso (ordinaryPush_eq l E f)))

/-- The unit-normalized module comparison applied termwise to a cochain complex.
Source: blueprint Step 2
(blueprint: lem-coef-dual-formula-scalar-transpose). -/
def ordinaryPullComplexMap (P : CochainComplex (integralTowerModules l E Y) ℤ) :
    ((proEtaleRingModulePullback f
      ((PurCompactSupport.completed l E).ring Y)
      ((PurCompactSupport.completed l E).ring X)
      ((PurCompactSupport.completed l E).pull f)).mapHomologicalComplex (.up ℤ)).obj P ⟶
        (ordinaryIntegralPullComplex l E f).obj P := by
  letI := ordinaryIntegralModulePull_additive l E f
  exact (NatTrans.mapHomologicalComplex (ordinaryPullIso l E f).hom (.up ℤ)).app P

/-- The completion map from the projection-formula pullback presentation is fixed on
K-flat representatives by the actual strict quotient augmentation and zero cone coordinate.
Source: blueprint Steps 2 and 11
(blueprint: lem-coef-dual-formula-scalar-transpose).
Proof: use ordinaryPullIso, exact termwise descent of ringed inverse image, and the
quotients-and-zero completion chain. The resolving-class localization uniquely descends
this natural comparison; its component square on K-flats is the displayed equation. -/
theorem pullCompletion_existsUnique :
    ∃! q : PurCompactSupport.pull (PurCompactSupport.completed l E) f ⟶
        integralDerivedPullback.{u, u} l E f,
      ∀ P : (integralOperationsGoodComplex.{u, u} l E Y).FullSubcategory,
        q.app ((@DerivedCategory.Q (scalarReductionSource.{u, u} l E Y) _ _
          (HasDerivedCategory.standard _)).obj P.obj) ≫
            (integralDerivedPullbackComparison.{u, u} l E f).hom.app P =
          (proEtaleRingDerivedPullbackFactors f
            ((PurCompactSupport.completed l E).ring Y)
            ((PurCompactSupport.completed l E).ring X)
            ((PurCompactSupport.completed l E).pull f)).hom.app P.obj ≫
          (@DerivedCategory.Q (scalarReductionSource.{u, u} l E X) _ _
            (HasDerivedCategory.standard _)).map (ordinaryPullComplexMap l E f P.obj) ≫
          (@DerivedCategory.Q (scalarReductionSource.{u, u} l E X) _ _
            (HasDerivedCategory.standard _)).map (ordinaryIntegralCompletionChain l E f P.obj) := by
  sorry

/-- The canonical ordinary-to-completed pullback map, with the complete chain normalization.
Source: blueprint Steps 2 and 11
(blueprint: lem-coef-dual-formula-scalar-transpose). -/
def pullCompletion :
    PurCompactSupport.pull (PurCompactSupport.completed l E) f ⟶
      integralDerivedPullback.{u, u} l E f :=
  (pullCompletion_existsUnique l E f).exists.choose

/-- The actual integral dual-formula object, using completed pullback and ordinary
internal Hom into the specified dualizing object. Source: blueprint definition of kappa
(blueprint: lem-coef-dual-formula-scalar-transpose). -/
def formulaObject
    (wX : IntegralFiniteExtension.DualizingDatum l X D hl E)
    (wY : IntegralFiniteExtension.DualizingDatum l Y D hl E)
    (M : sfIntegralConstructibleCategory l E Y) : IntegralVerdier.Ambient l E X :=
  (IntegralVerdier.dual l E X wX.omega.obj).obj
    (op ((integralDerivedPullback.{u, u} l E f).obj
      ((IntegralVerdier.dual l E Y wY.omega.obj).obj (op M.obj))))

/-- Evaluation characterization of the canonical integral exceptional-formula component.
Its transpose uses the actual ordinary projection map, completion augmentation, and
structural relative trace. Source: blueprint Steps 2--3
(blueprint: lem-coef-dual-formula-scalar-transpose). -/
def FormulaNormalized
    (wX : IntegralFiniteExtension.DualizingDatum l X D hl E)
    (wY : IntegralFiniteExtension.DualizingDatum l Y D hl E)
    (aX : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l E X))
    (aZ : IntegralHom.TensorPresentation.{u, u} c.Z
      (completedIntegralCommRingSheafUnrestricted l E c.Z))
    (aY : IntegralHom.TensorPresentation.{u, u} Y
      (completedIntegralCommRingSheafUnrestricted l E Y))
    (sX : IntegralVerdier.SignedSymmetry X _ aX)
    (G : sfIntegralConstructibleCategory l E Y ⥤ sfIntegralConstructibleCategory l E X)
    (adj : sfCompactSupportFiniteIntegralFunctor l D.k
      (PurCompactSupport.coefficientPrimeUnit l D hl) c E ⊣ G)
    (M : sfIntegralConstructibleCategory l E Y)
    (k : (G.obj M).obj ≅ formulaObject D l hl E f wX wY M) : Prop :=
  ((PurCompactSupport.projectionMap (PurCompactSupport.completed l E) c
      (IntegralFiniteExtension.tensorModel X aX)
      (IntegralFiniteExtension.tensorModel c.Z aZ)
      (IntegralFiniteExtension.tensorModel Y aY)
      (PurCompactSupport.completedPull_comp l E c.i c.g)).app (G.obj M).obj).app
        ((IntegralVerdier.dual l E Y wY.omega.obj).obj (op M.obj)) ≫
    (PurCompactSupport.image (PurCompactSupport.completed l E) c).map
      (aX.tensor.map (Prod.mkHom (𝟙 (G.obj M).obj)
        ((pullCompletion l E f).app
          ((IntegralVerdier.dual l E Y wY.omega.obj).obj (op M.obj)))) ≫
      (sX.swap (G.obj M).obj ((integralDerivedPullback.{u, u} l E f).obj
        ((IntegralVerdier.dual l E Y wY.omega.obj).obj (op M.obj)))).hom ≫
      aX.tensor.map (Prod.mkHom (𝟙 _) k.hom) ≫
      (aX.adjunction ((integralDerivedPullback.{u, u} l E f).obj
        ((IntegralVerdier.dual l E Y wY.omega.obj).obj (op M.obj)))).counit.app wX.omega.obj) ≫
    (sfQcqsCompactSupportRealization l E D.k
      (PurCompactSupport.coefficientPrimeUnit l D hl) c).hom.app wX.omega ≫
    (sfIntegralConstructible l E Y).ι.map (trace D l hl E f c wX wY) =
  aY.tensor.map (Prod.mkHom
    ((sfQcqsCompactSupportRealization l E D.k
      (PurCompactSupport.coefficientPrimeUnit l D hl) c).hom.app (G.obj M) ≫
      (sfIntegralConstructible l E Y).ι.map (adj.counit.app M)) (𝟙 _)) ≫
    (aY.adjunction M.obj).counit.app wY.omega.obj

/-- The exceptional formula has a unique component with the evaluation normalization.
Source: blueprint Step 3; prop-coef-integral-exceptional-adjoint, formula clause
(blueprint: lem-coef-dual-formula-scalar-transpose).
Proof: at every finite coefficient level, apply the tensor-Hom bijections, ordinary
pullback/direct-image adjunction, and the absolute trace exchange. The inverse Hom
bijection sends h to delta_M inverse composed with the curry of its trace transpose.
By the fixed projection and trace equations this gives exactly FormulaNormalized.
Finite Verdier biduality makes this a bijection. Perform these constructions on
simultaneous coefficient-system resolutions, with the actual quotient units and
counits, and descend the one coherent mapping-system bijection through reduction and
total limit. Constructibility and the common Tor bounds are those of the integral
exceptional-adjoint proposition. The integral adjunction bijection and Yoneda give
existence and uniqueness of the displayed normalized isomorphism. -/
theorem formula_existsUnique
    (wX : IntegralFiniteExtension.DualizingDatum l X D hl E)
    (wY : IntegralFiniteExtension.DualizingDatum l Y D hl E)
    (aX : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l E X))
    (aZ : IntegralHom.TensorPresentation.{u, u} c.Z
      (completedIntegralCommRingSheafUnrestricted l E c.Z))
    (aY : IntegralHom.TensorPresentation.{u, u} Y
      (completedIntegralCommRingSheafUnrestricted l E Y))
    (sX : IntegralVerdier.SignedSymmetry X _ aX)
    (G : sfIntegralConstructibleCategory l E Y ⥤ sfIntegralConstructibleCategory l E X)
    (adj : sfCompactSupportFiniteIntegralFunctor l D.k
      (PurCompactSupport.coefficientPrimeUnit l D hl) c E ⊣ G)
    (M : sfIntegralConstructibleCategory l E Y) :
    ∃! k : (G.obj M).obj ≅ formulaObject D l hl E f wX wY M,
      FormulaNormalized D l hl E f c wX wY aX aZ aY sX G adj M k := by
  sorry

/-- The exceptional-formula component selected by its unique evaluation characterization.
Source: blueprint definition of kappa
(blueprint: lem-coef-dual-formula-scalar-transpose). -/
def formulaIso
    (wX : IntegralFiniteExtension.DualizingDatum l X D hl E)
    (wY : IntegralFiniteExtension.DualizingDatum l Y D hl E)
    (aX : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l E X))
    (aZ : IntegralHom.TensorPresentation.{u, u} c.Z
      (completedIntegralCommRingSheafUnrestricted l E c.Z))
    (aY : IntegralHom.TensorPresentation.{u, u} Y
      (completedIntegralCommRingSheafUnrestricted l E Y))
    (sX : IntegralVerdier.SignedSymmetry X _ aX)
    (G : sfIntegralConstructibleCategory l E Y ⥤ sfIntegralConstructibleCategory l E X)
    (adj : sfCompactSupportFiniteIntegralFunctor l D.k
      (PurCompactSupport.coefficientPrimeUnit l D hl) c E ⊣ G)
    (M : sfIntegralConstructibleCategory l E Y) :=
  (formula_existsUnique D l hl E f c wX wY aX aZ aY sX G adj M).exists.choose

/-- The constructible value of the specified integral Verdier dual. The membership
proof is extracted from the recorded integral Verdier theorem.
Source: blueprint integral Verdier convention
(blueprint: lem-coef-dual-formula-scalar-transpose). -/
def dualValue (W : Scheme.{u}) [W.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (W ↘ Spec (.of D.k))] [QuasiCompact (W ↘ Spec (.of D.k))]
    [IsSeparated (W ↘ Spec (.of D.k))]
    (w : IntegralFiniteExtension.DualizingDatum l W D hl E)
    (K : sfIntegralConstructibleCategory l E W) : sfIntegralConstructibleCategory l E W :=
  ⟨(IntegralVerdier.dual l E W w.omega.obj).obj (op K.obj),
    (Exists.choose (Exists.choose_spec (Exists.choose_spec (Exists.choose_spec
      (Exists.choose_spec (Exists.choose_spec
        (integral_verdier_biduality D l hl E W w.omega w.reduction))))))) K⟩

/-- Completed pullback of the constructible dual, with residue inverses induced from k.
Source: blueprint definition of d_M
(blueprint: lem-coef-dual-formula-scalar-transpose). -/
def pullDualValue (wY : IntegralFiniteExtension.DualizingDatum l Y D hl E)
    (M : sfIntegralConstructibleCategory l E Y) : sfIntegralConstructibleCategory l E X :=
  (@constructibleIntegralPullback l _ E _ _ _ X Y f
    (fun x ↦ (by
      simpa using (finiteFieldDatumPrimeUnit D l hl).map
        ((X ↘ Spec (.of D.k)).residueFieldAlgebraMap x) :
          IsUnit (l : X.residueField x)).invertible)
    (fun y ↦ (by
      simpa using (finiteFieldDatumPrimeUnit D l hl).map
        ((Y ↘ Spec (.of D.k)).residueFieldAlgebraMap y) :
          IsUnit (l : Y.residueField y)).invertible)).obj
      (dualValue D l hl E Y wY M)

variable (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (i : E →ₐ[Padic l] L)

/-- The evaluation-defined beta is invertible on the actual constructible domain,
independently of normalized tensor presentation.
Source: lem-coef-integral-finite-extension, beta clause
(blueprint: lem-coef-dual-formula-scalar-transpose).
Proof: the finite-free scalar Hom comparison preserves evaluation on K-flat models.
Its complete version is obtained by the specified completion maps. The dualizing
comparison is the scalar-extended structural-counit transpose. Finite Verdier duality
makes their composite invertible on every finite level; the coherent reduction/limit
realization and derived completeness give invertibility of the displayed beta.
Changing a normalized tensor presentation preserves its evaluation transpose, so the
conclusion holds for both supplied presentations. -/
theorem beta_isIso (W : Scheme.{u}) [W.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (W ↘ Spec (.of D.k))] [QuasiCompact (W ↘ Spec (.of D.k))]
    [IsSeparated (W ↘ Spec (.of D.k))]
    (wE : IntegralFiniteExtension.DualizingDatum l W D hl E)
    (wL : IntegralFiniteExtension.DualizingDatum l W D hl L)
    (a : IntegralHom.TensorPresentation.{u, u} W
      (completedIntegralCommRingSheafUnrestricted l E W))
    (b : IntegralHom.TensorPresentation.{u, u} W
      (completedIntegralCommRingSheafUnrestricted l L W))
    (K : sfIntegralConstructibleCategory l E W) :
    IsIso (IntegralFiniteExtension.beta l E L i W D hl wE wL a b K.obj K.property.1) := by
  sorry

/-- The specified scalar beta, viewed as an isomorphism using its invertibility theorem.
Source: blueprint beta convention
(blueprint: lem-coef-dual-formula-scalar-transpose). -/
def betaIso (W : Scheme.{u}) [W.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (W ↘ Spec (.of D.k))] [QuasiCompact (W ↘ Spec (.of D.k))]
    [IsSeparated (W ↘ Spec (.of D.k))]
    (wE : IntegralFiniteExtension.DualizingDatum l W D hl E)
    (wL : IntegralFiniteExtension.DualizingDatum l W D hl L)
    (a : IntegralHom.TensorPresentation.{u, u} W
      (completedIntegralCommRingSheafUnrestricted l E W))
    (b : IntegralHom.TensorPresentation.{u, u} W
      (completedIntegralCommRingSheafUnrestricted l L W))
    (K : sfIntegralConstructibleCategory l E W) :=
  @asIso _ _ _ _ (IntegralFiniteExtension.beta l E L i W D hl wE wL a b K.obj K.property.1)
    (beta_isIso D l hl E L i W wE wL a b K)

/-- The finite-free completed compact-support comparison in the ambient realization.
The direction is T_Y F_E to F_L T_X. Both completions and the proper/open scalar mate
are the published canonical maps. Source: blueprint definition of alpha
(blueprint: lem-coef-dual-formula-scalar-transpose). -/
def supportScalar (K : sfIntegralConstructibleCategory l E X) :
    (integralScalarExtension l E L i Y).obj
        ((sfCompactSupportFiniteIntegralFunctor l D.k
          (PurCompactSupport.coefficientPrimeUnit l D hl) c E).obj K).obj ⟶
      (PurCompactSupport.image (PurCompactSupport.completed l L) c).obj
        ((integralScalarExtension l E L i X).obj K.obj) :=
  (IntegralFiniteExtension.completion l E L i Y _
    ((sfCompactSupportFiniteIntegralFunctor l D.k
      (PurCompactSupport.coefficientPrimeUnit l D hl) c E).obj K).property.1).inv ≫
  (pbcDerivedExtend (completedCoefficientMap l E L i Y)).map
    ((sfQcqsCompactSupportRealization l E D.k
      (PurCompactSupport.coefficientPrimeUnit l D hl) c).inv.app K) ≫
  (PurCompactSupport.comparison (PurCompactSupport.completedChange l E L i) c).app K.obj ≫
  (PurCompactSupport.image (PurCompactSupport.completed l L) c).map
    (IntegralFiniteExtension.completion l E L i X K.obj K.property.1).hom

/-- The prescribed finite-free comparison is invertible on constructible complexes.
Source: blueprint alpha convention, finite-free completed scalar comparison
(blueprint: lem-coef-dual-formula-scalar-transpose).
Proof: choose an R-basis of S to compute ordinary scalar extension as a finite sum.
Open extension, proper derived image and the Roos total limit distribute over this
finite sum. The universal tensor and quotient normalizations identify that distributive
map with supportScalar, including its two completion conjugations. Hence it is invertible;
the construction is independent of the basis. -/
theorem supportScalar_isIso (K : sfIntegralConstructibleCategory l E X) :
    IsIso (supportScalar D l hl E f c L i K) := by
  sorry

/-- The canonical finite-free completed support isomorphism, in the ambient realization.
Source: blueprint definition of alpha
(blueprint: lem-coef-dual-formula-scalar-transpose). -/
def supportScalarIso (K : sfIntegralConstructibleCategory l E X) :=
  @asIso _ _ _ _ (supportScalar D l hl E f c L i K)
    (supportScalar_isIso D l hl E f c L i K)

/-- The canonical scalar comparison d_M for the integral dual formula, with precisely
contravariant order: D_X,L(f_L^*(beta_Y inverse) followed by c inverse), then beta_X.
Source: blueprint displayed definition of d_M
(blueprint: lem-coef-dual-formula-scalar-transpose). -/
def dualFormulaScalar
    (wEX : IntegralFiniteExtension.DualizingDatum l X D hl E)
    (wEY : IntegralFiniteExtension.DualizingDatum l Y D hl E)
    (wLX : IntegralFiniteExtension.DualizingDatum l X D hl L)
    (wLY : IntegralFiniteExtension.DualizingDatum l Y D hl L)
    (aEX : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l E X))
    (aEY : IntegralHom.TensorPresentation.{u, u} Y
      (completedIntegralCommRingSheafUnrestricted l E Y))
    (aLX : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l L X))
    (aLY : IntegralHom.TensorPresentation.{u, u} Y
      (completedIntegralCommRingSheafUnrestricted l L Y))
    (M : sfIntegralConstructibleCategory l E Y) :
    (integralScalarExtension l E L i X).obj (formulaObject D l hl E f wEX wEY M) ⟶
      formulaObject D l hl L f wLX wLY
        ((sfConstructibleIntegralScalarExtension D.p l hl E L i Y).obj M) :=
  IntegralFiniteExtension.beta l E L i X D hl wEX wLX aEX aLX
      (pullDualValue D l hl E f wEY M).obj (pullDualValue D l hl E f wEY M).property.1 ≫
    (IntegralVerdier.dual l L X wLX.omega.obj).map
      ((integralDerivedPullback.{u, u} l L f).map (betaIso D l hl E L i Y wEY wLY aEY aLY M).inv ≫
        (scalarPullbackCompleted l E L i f (dualValue D l hl E Y wEY M).obj
          (dualValue D l hl E Y wEY M).property.1
          (pullDualValue D l hl E f wEY M).property.1).inv).op

/-- The comparison b-prime is kappa_L inverse after d_M after T_X(kappa_E).
Every factor is selected by its evaluation or structural-counit normalization.
Source: blueprint displayed definition of b-prime
(blueprint: lem-coef-dual-formula-scalar-transpose). -/
def exceptionalScalar
    (wEX : IntegralFiniteExtension.DualizingDatum l X D hl E)
    (wEY : IntegralFiniteExtension.DualizingDatum l Y D hl E)
    (wLX : IntegralFiniteExtension.DualizingDatum l X D hl L)
    (wLY : IntegralFiniteExtension.DualizingDatum l Y D hl L)
    (aEX : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l E X))
    (aEZ : IntegralHom.TensorPresentation.{u, u} c.Z
      (completedIntegralCommRingSheafUnrestricted l E c.Z))
    (aEY : IntegralHom.TensorPresentation.{u, u} Y
      (completedIntegralCommRingSheafUnrestricted l E Y))
    (aLX : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l L X))
    (aLZ : IntegralHom.TensorPresentation.{u, u} c.Z
      (completedIntegralCommRingSheafUnrestricted l L c.Z))
    (aLY : IntegralHom.TensorPresentation.{u, u} Y
      (completedIntegralCommRingSheafUnrestricted l L Y))
    (sEX : IntegralVerdier.SignedSymmetry X _ aEX)
    (sLX : IntegralVerdier.SignedSymmetry X _ aLX)
    (GE : sfIntegralConstructibleCategory l E Y ⥤ sfIntegralConstructibleCategory l E X)
    (GS : sfIntegralConstructibleCategory l L Y ⥤ sfIntegralConstructibleCategory l L X)
    (adjE : sfCompactSupportFiniteIntegralFunctor l D.k
      (PurCompactSupport.coefficientPrimeUnit l D hl) c E ⊣ GE)
    (adjL : sfCompactSupportFiniteIntegralFunctor l D.k
      (PurCompactSupport.coefficientPrimeUnit l D hl) c L ⊣ GS)
    (M : sfIntegralConstructibleCategory l E Y) :
    (integralScalarExtension l E L i X).obj (GE.obj M).obj ⟶
      (GS.obj ((sfConstructibleIntegralScalarExtension D.p l hl E L i Y).obj M)).obj :=
  (integralScalarExtension l E L i X).map
      (formulaIso D l hl E f c wEX wEY aEX aEZ aEY sEX GE adjE M).hom ≫
    dualFormulaScalar D l hl E f L i wEX wEY wLX wLY aEX aEY aLX aLY M ≫
    (formulaIso D l hl L f c wLX wLY aLX aLZ aLY sLX GS adjL
      ((sfConstructibleIntegralScalarExtension D.p l hl E L i Y).obj M)).inv

/-- The scalar comparison for the canonical integral exceptional formula transposes
under the specified constructible adjunctions to the canonical support comparison.
The equality is written after the faithful ambient inclusion and the canonical
support realization, so that the ordinary proper/open projection normalization remains visible.
Source: blueprint lem-coef-rational-operations, proof paragraph 8, Step 15
(blueprint: lem-coef-dual-formula-scalar-transpose).

Proof plan:
1. At every positive coefficient level use finite Tor closure, finite Verdier biduality,
   and finite exceptional adjunction. Work with B_n = S/pi^n S; its v-adic indexing
   is the cofinal ramified subsequence en, not a replacement coefficient ring.
2. For h:K to D_X f-star D_Y M, evaluate h against f-star D_Y M. Transpose its absolute
   trace through the canonical support compositor and projection formula. Curry and
   compose with delta_M inverse. The resulting Hom bijection is the finite exceptional
   adjunction for the evaluation-normalized formula component.
3. Scalar extension of the absolute structural counit gives its defining trace square.
   The proper/open scalar mate commutes with the support compositor, by mate pasting
   and the same unit normalization. On an R-basis of S these are finite distributivity
   equations, independent of that basis.
4. The evaluation-defined beta and canonical pullback associator give the evaluation
   equation for d_M. Insert it in the trace transpose of step 2. Compatibility of the
   projection map with scalar tensor reassociation and the structural-counit square
   gives y_B = u_Y T_Y(y_A) r. Evaluate, curry and use beta's delta compatibility to get
   Psi_B(d_M T_X(h)) = T_Y(Psi_A(h)) alpha inverse.
5. Put h=kappa_E at G_E M. FormulaNormalized identifies Psi_E(h) with epsilon_E.
   The corresponding normalization over S identifies Psi_L(kappa_L b-prime) with
   epsilon_L F_L(b-prime). This is exactly the finite displayed counit equality.
6. Construct these arrows and identities on simultaneous coefficient-system resolutions,
   including their quotient cocycles. Use finite-adjunction diagram realization and the
   strict-tower Homotopy-limit calculus to descend that single coherent identity through
   reduction/total limit. The finite-free completed comparison identifies its support
   arrow with supportScalarIso. This yields the integral identity below. Equality is
   transported as a system-map identity; it is not inferred from unrelated equalities
   after individual finite evaluations.
-/
theorem coef_dual_formula_scalar_transpose
    (wEX : IntegralFiniteExtension.DualizingDatum l X D hl E)
    (wEY : IntegralFiniteExtension.DualizingDatum l Y D hl E)
    (wLX : IntegralFiniteExtension.DualizingDatum l X D hl L)
    (wLY : IntegralFiniteExtension.DualizingDatum l Y D hl L)
    (aEX : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l E X))
    (aEZ : IntegralHom.TensorPresentation.{u, u} c.Z
      (completedIntegralCommRingSheafUnrestricted l E c.Z))
    (aEY : IntegralHom.TensorPresentation.{u, u} Y
      (completedIntegralCommRingSheafUnrestricted l E Y))
    (aLX : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l L X))
    (aLZ : IntegralHom.TensorPresentation.{u, u} c.Z
      (completedIntegralCommRingSheafUnrestricted l L c.Z))
    (aLY : IntegralHom.TensorPresentation.{u, u} Y
      (completedIntegralCommRingSheafUnrestricted l L Y))
    (sEX : IntegralVerdier.SignedSymmetry X _ aEX)
    (sLX : IntegralVerdier.SignedSymmetry X _ aLX)
    (GE : sfIntegralConstructibleCategory l E Y ⥤ sfIntegralConstructibleCategory l E X)
    (GS : sfIntegralConstructibleCategory l L Y ⥤ sfIntegralConstructibleCategory l L X)
    (adjE : sfCompactSupportFiniteIntegralFunctor l D.k
      (PurCompactSupport.coefficientPrimeUnit l D hl) c E ⊣ GE)
    (adjL : sfCompactSupportFiniteIntegralFunctor l D.k
      (PurCompactSupport.coefficientPrimeUnit l D hl) c L ⊣ GS)
    (M : sfIntegralConstructibleCategory l E Y) :
    (PurCompactSupport.image (PurCompactSupport.completed l L) c).map
        (exceptionalScalar D l hl E f c L i wEX wEY wLX wLY
          aEX aEZ aEY aLX aLZ aLY sEX sLX GE GS adjE adjL M) ≫
      (sfQcqsCompactSupportRealization l L D.k
        (PurCompactSupport.coefficientPrimeUnit l D hl) c).hom.app
          (GS.obj ((sfConstructibleIntegralScalarExtension D.p l hl E L i Y).obj M)) ≫
      (sfIntegralConstructible l L Y).ι.map
        (adjL.counit.app ((sfConstructibleIntegralScalarExtension D.p l hl E L i Y).obj M)) =
    (supportScalarIso D l hl E f c L i (GE.obj M)).inv ≫
      (integralScalarExtension l E L i Y).map
        ((sfIntegralConstructible l E Y).ι.map (adjE.counit.app M)) := by
  sorry

end WeilConjectures.CoefDualFormulaScalarTranspose



