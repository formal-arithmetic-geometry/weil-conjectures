/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Diagonal.PurityDiagonalDualizingObject
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalObjects
public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothCoefficientArrows
public import WeilConjectures.AlgebraicGeometry.Scalar.ScalarExtensionFunctor
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateSheaf
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import WeilConjectures.Algebra.Homology.KFlatResolution
public import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.Additive
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
public import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
public import Mathlib.CategoryTheory.Types.Basic
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
public import Mathlib.LinearAlgebra.TensorProduct.Vanishing
public import Mathlib.RingTheory.TensorProduct.DirectLimitFG
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Functor.EpiMono
public import Mathlib.CategoryTheory.Limits.Types.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
public import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
public import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Sites.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
public import WeilConjectures.Algebra.Homology.Site.SiteDerivedTensorDescent
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackBase
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLinePullback
public import WeilConjectures.EtaleCohomology.TateTwist.RootsOfUnityPullback
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTensorFamily
public import WeilConjectures.CategoryTheory.NormalizedSignedTensorPowers
public import WeilConjectures.CategoryTheory.Monoidal.IntTensorFamily
public import WeilConjectures.CategoryTheory.IntTensorFamilyIso
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLocalLine
public import WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf
public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.LocallyTrivialInverse
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.MonoidalComp
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackRest
public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import WeilConjectures.AlgebraicGeometry.Vector.VectorBundlePurity
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Adjunction
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalChart
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalRealization
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenCover
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalConservativity

/-! # Canonical data for finite general-ring smooth purity

Unchanged constructions extracted from `FiniteGeneralRing` so its proof steps can
be stated independently without an import cycle.
Source: general-ring smooth purity (blueprint: def-sp-general-ring-canonical-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale

/-- Scalar extension of the comparison-origin coefficient unit, using the published
site/scalar mate and the multiplication-normalized ordinary scalar unit.
Source: general-ring purity, clause (1) (blueprint: det-sp-finite-general-ring). -/
def finiteGeneralRingScalarUnitIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (phi : A →+* B) (T : Scheme.{u}) :
    (Etale.FiniteSmoothPurity.proScalar phi T).obj
        ((Etale.FiniteSmoothPurity.comparison A T).obj (Etale.ordinaryFiniteUnit A T)) ≅
      (Etale.FiniteSmoothPurity.comparison B T).obj (Etale.ordinaryFiniteUnit B T) :=
  (pbcComparisonReduction T phi).app (Etale.ordinaryFiniteUnit A T) ≪≫
    (Etale.FiniteSmoothPurity.comparison B T).mapIso
      ((Etale.scalarExtension phi T).mapIso
          (Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} A) T) ≪≫
        Etale.ExceptionalCoefficients.unitIso phi T ≪≫
        (Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} B) T).symm)

/-- Actual intrinsic derived scalar extension, in fixed-coefficient coordinates.
This is scalarExtensionFunctor conjugated by the published realization equivalences.
Source: general-ring purity, (-)_A (blueprint: det-sp-finite-general-ring). -/
def finiteGeneralRingScalar {A B : Type u} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (phi : A →+* B) (T : Scheme.{u}) :
    Etale.FiniteSmoothPurity.proCategory (ULift.{u + 1, u} A) T ⥤
      Etale.FiniteSmoothPurity.proCategory (ULift.{u + 1, u} B) T :=
  (sfIntrinsicDerivedEquivalence T A).functor ⋙ scalarExtensionFunctor phi T ⋙
    (sfIntrinsicDerivedEquivalence T B).inverse

/-- The scalar-presentation comparison is the inverse realization of the published
section-normalized scalar mate, followed by the realization unit.
Source: general-ring purity, coefficient comparison (blueprint: det-sp-finite-general-ring). -/
def finiteGeneralRingScalarIso {A B : Type u} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (phi : A →+* B) (T : Scheme.{u})
    (K : Etale.FiniteSmoothPurity.proCategory (ULift.{u + 1, u} A) T) :
    (finiteGeneralRingScalar phi T).obj K ≅
      (Etale.FiniteSmoothPurity.proScalar
        (RingHom.ulift.{u + 1, u + 1, u, u} phi) T).obj K :=
  (sfIntrinsicDerivedEquivalence T B).inverse.mapIso
      ((reductionRealizationScalarIso phi T).app K) ≪≫
    (sfIntrinsicDerivedEquivalence T B).unitIso.symm.app _

/-- The comparison-origin unit. This is the actual constant A_T in degree zero.
Source: general-ring purity, omega=f^!A_Y (blueprint: det-sp-finite-general-ring). -/
def finiteGeneralRingUnit (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :=
  (Etale.FiniteSmoothPurity.comparison A T).obj (Etale.ordinaryFiniteUnit A T)

/-- The map from nu* of the ordinary dualizing complex to f^! of the comparison unit.
Its formula uses the comparison-adjunction unit, so it is never an arbitrary iso.
Source: finite exceptional inverse image (blueprint: det-sp-finite-general-ring). -/
def finiteGeneralRingDualizingUnitMap (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] :
    (Etale.FiniteSmoothPurity.comparison A X).obj
        (Etale.dualizingComplex A f) ⟶
      (Etale.FiniteSmoothPurity.exceptional A f).obj (finiteGeneralRingUnit A Y) :=
  (Etale.FiniteSmoothPurity.comparison A X).map
    ((Etale.rightDerivedUpperShriek A f).map
      ((derivedComparisonAdjunction (ModuleCat.{u + 1} A) Y).unit.app
        (Etale.ordinaryFiniteUnit A Y)))

/-- The actual exceptional scalar comparison evaluated at the unit, followed by the
canonical scalar unit identification. Its middle factor is the published transpose
of scalar extension of the compact-support counit after the inverse support comparison.
Source: det-sp-reduction-exceptional and clause (1)
(blueprint: det-sp-finite-general-ring). -/
def finiteGeneralRingReduction (P : WeilConjectures.PurityFiniteSetting.{u})
    {A : Type u} [CommRing A] [Finite A] (phi : P.Ring →+* A)
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] :
    (finiteGeneralRingScalar phi X).obj (P.diagonalDualizing f) ⟶
      (Etale.FiniteSmoothPurity.exceptional (ULift.{u + 1, u} A) f).obj
        (finiteGeneralRingUnit (ULift.{u + 1, u} A) Y) :=
  letI : (Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} P.Coefficient)
      (HasCompactification.compactification f)).IsLeftAdjoint :=
    inferInstanceAs (Etale.rightDerivedLowerShriek
      (ModuleCat.{u + 1} P.Coefficient) f).IsLeftAdjoint
  (finiteGeneralRingScalarIso phi X (P.diagonalDualizing f)).hom ≫
    (Etale.FiniteSmoothPurity.proScalar (RingHom.ulift.{u + 1, u + 1, u, u} phi) X).map
      ((Etale.FiniteSmoothPurity.comparison P.Coefficient X).map
        (((Adjunction.ofIsLeftAdjoint (Etale.rightDerivedLowerShriekOfCompactification
            (ModuleCat.{u + 1} P.Coefficient)
            (HasCompactification.compactification f))).rightAdjointUniq
          (Etale.rightDerivedUpperShriekAdjunction P.Coefficient f)).hom.app
            ((Etale.FiniteSmoothPurity.origin P.Coefficient Y).obj
              (finiteGeneralRingUnit P.Coefficient Y)))) ≫
    Etale.FiniteSmoothPurity.proCoefficientMap
      (RingHom.ulift.{u + 1, u + 1, u, u} phi) f
      (finiteGeneralRingUnit P.Coefficient Y) ≫
    (Etale.FiniteSmoothPurity.exceptional (ULift.{u + 1, u} A) f).map
      (finiteGeneralRingScalarUnitIso
        (RingHom.ulift.{u + 1, u + 1, u, u} phi) Y).hom

/-- Tensor a normalized Kummer sheaf comparison in the published ordered shifted model.
The empty power is the identity on the coefficient unit. No orientation is chosen.
Source: general-ring purity, exponent independence
(blueprint: det-sp-finite-general-ring). -/
def finiteGeneralRingLevelPower (A : Type (u + 1)) [CommRing A]
    (M N : ℕ) (hM : (M : A) = 0) (hN : (N : A) = 0) (T : Scheme.{u})
    (e : Scheme.finiteEtaleTateLine T M A hM ≅ Scheme.finiteEtaleTateLine T N A hN) :
    (d : ℕ) → Etale.FiniteSmoothPurity.line A M hM T d ≅
      Etale.FiniteSmoothPurity.line A N hN T d
  | 0 => Iso.refl _
  | d + 1 =>
    ((Etale.derivedTensor (ModuleCat.{u + 1} A) T).mapIso
      (finiteGeneralRingLevelPower A M N hM hN T e d)).app _ ≪≫
    ((Etale.derivedTensor (ModuleCat.{u + 1} A) T).obj
      (Etale.FiniteSmoothPurity.line A N hN T d)).mapIso
        ((shiftFunctor _ (2 : ℤ)).mapIso ((DerivedCategory.singleFunctor _ 0).mapIso e))

/-- A Kummer level comparison in the ordinary sheaf presentation, fixed by the power
map into G_m and its action on every scalar/root generator. This is precisely the
root normalization of etaleFiniteTwistPullback, specialized to degree one.
Source: general-ring purity, proof (3) (blueprint: det-sp-finite-general-ring). -/
def FiniteGeneralRingKummerComparison (A : Type (u + 1)) [CommRing A]
    (M N : ℕ) (hM : (M : A) = 0) (hN : (N : A) = 0) (T : Scheme.{u})
    (q : T.rootsOfUnitySheaf M ⟶ T.rootsOfUnitySheaf N)
    (e : Scheme.finiteEtaleTateLine T M A hM ≅ Scheme.finiteEtaleTateLine T N A hN) :
    Prop :=
  q ≫ kernel.ι (N • 𝟙 T.gmSheaf) = (M / N) • kernel.ι (M • 𝟙 T.gmSheaf) ∧
    ∀ (W : T.Etaleᵒᵖ) (a : A) (z : (T.rootsOfUnitySheaf M).obj.obj W),
      e.hom.hom.app W (Scheme.finiteEtaleTateOneGenerator A M T hM W a z) =
        Scheme.finiteEtaleTateOneGenerator A N T hN W a (q.hom.app W z)

/-- Scalar extension of the recorded Q_ell diagonal orientation, followed by the
actual site/scalar comparison and the generator-normalized Tate comparison.
Source: clause (1) (blueprint: det-sp-finite-general-ring). -/
def finiteGeneralRingOrientationExtension (P : WeilConjectures.PurityFiniteSetting.{u})
    {A : Type u} [CommRing A] [Finite A] (phi : P.Ring →+* A)
    (hA : (P.diagonalExponent : ULift.{u + 1, u} A) = 0)
    {X Y : Scheme.{u}} (d : ℕ) (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [SmoothOfRelativeDimension d f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    [HasCompactification f]
    (t : Etale.FiniteSmoothPurity.CoefficientLineComparison
      (RingHom.ulift.{u + 1, u + 1, u, u} phi) P.diagonalExponent P.diagonalExponent
      P.diagonalExponent_annihilates hA X) :
    (finiteGeneralRingScalar phi X).obj (P.diagonalDualizing f) ≅
      (Etale.FiniteSmoothPurity.comparison (ULift.{u + 1, u} A) X).obj
        (Etale.FiniteSmoothPurity.line (ULift.{u + 1, u} A) P.diagonalExponent hA X d) :=
  (finiteGeneralRingScalar phi X).mapIso (P.diagonalDualizingObject d f aY) ≪≫
    finiteGeneralRingScalarIso phi X (P.diagonalTwist X d) ≪≫
    (pbcComparisonReduction X (RingHom.ulift.{u + 1, u + 1, u, u} phi)).app
      (P.diagonalTwistEtale X d) ≪≫
    (Etale.FiniteSmoothPurity.comparison (ULift.{u + 1, u} A) X).mapIso (t.tensorPower d)

/-- Invertibility and naturality of the specified projection-formula/counit purity map.
The coefficient ring is abstract so concrete coefficient structures are elaborated once.
Source: general-ring purity, clause (3) (blueprint: det-sp-finite-general-ring). -/
def FiniteGeneralRingTensorFormula (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (L : Etale.DerivedCategoryModule A X)
    (alpha : Etale.dualizingComplex A f ≅ L) : Prop :=
  (∀ K : Etale.FiniteSmoothPurity.proCategory A Y,
    Etale.FiniteSmoothPurity.IsCtf A Y K →
      Etale.FiniteSmoothPurity.IsCtf A X ((Etale.FiniteSmoothPurity.exceptional A f).obj K) ∧
      IsIso (Etale.FiniteSmoothPurity.proGamma A f L alpha K)) ∧
  (∀ (K K' : Etale.FiniteSmoothPurity.proCategory A Y),
    Etale.FiniteSmoothPurity.IsCtf A Y K →
    Etale.FiniteSmoothPurity.IsCtf A Y K' → ∀ a : K ⟶ K',
      (Etale.FiniteSmoothPurity.proSource A f L).map a ≫
          Etale.FiniteSmoothPurity.proGamma A f L alpha K' =
        Etale.FiniteSmoothPurity.proGamma A f L alpha K ≫
          (Etale.FiniteSmoothPurity.exceptional A f).map a)

end AlgebraicGeometry.ProEtale
