/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedCoefficientChangePresentations
import WeilConjectures.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Cones
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import WeilConjectures.CategoryTheory.ModulePullbackPushforwardAdjunctionSupplement
import WeilConjectures.CategoryTheory.PreDerivedAdjointFunctorsGeneral
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.CategoryTheory.RingedToposDerivedPushforwardComposition
import WeilConjectures.CategoryTheory.RingedToposMorphismSupplement
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsSupplement
import WeilConjectures.Mathlib.Algebra.Homology.GrothendieckAbelian
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import WeilConjectures.CategoryTheory.RingedToposRingData
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.GeometricModuleTransport
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.GeometricRingTransport
import Mathlib.CategoryTheory.Sites.Limits
import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
import WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
import WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import Mathlib.CategoryTheory.Types.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIsoSupplement
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed

/-!
# Naturality of normalized coefficient changes

Source: Stacks, Tags 03D7, 07A6 and 0D6E.
(blueprint: lem-pur-ringed-coefficient-change-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v r w
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.RingedCoefficientCounit

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  [UnivLE.{max u v, r}] [EssentiallySmall.{r} C] [EssentiallySmall.{r} D]
  {JX : GrothendieckTopology C} {JY : GrothendieckTopology D}
  [JX.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [JY.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [JX.HasSheafCompose (forget AddCommGrpCat.{r})]
  [JY.HasSheafCompose (forget AddCommGrpCat.{r})]
  [HasSheafify JX AddCommGrpCat.{r}] [JX.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasSheafify JY AddCommGrpCat.{r}] [JY.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasWeakSheafify JX CommRingCat.{r}] [HasWeakSheafify JY CommRingCat.{r}]
  (A : CommRingCat.{r}) (RX RI : Sheaf JX CommRingCat.{r})
  (RY : Sheaf JY CommRingCat.{r})
  (inverse : Sheaf JY (Type r) ⥤ Sheaf JX (Type r))
  (direct : Sheaf JX (Type r) ⥤ Sheaf JY (Type r)) (geom : inverse ⊣ direct)
  [leftExact : PreservesFiniteLimits inverse]
  (IA : SheafOfModules.AlgebraicInverseImage inverse
    (constantRing JY A) (constantRing JX A))
  (IR : SheafOfModules.AlgebraicInverseImage inverse RY RI) (c : RI ⟶ RX)

include leftExact in
/-- Compatible coefficient maps admit normalized derived comparisons. Assuming the individual
counit compatibilities, every normalized comparison satisfies the two coefficient
naturality squares.

Source: Stacks Project, sites-cohomology.tex, Tags 07A6 and 0D6E;
sites-modules.tex, Tag 03D7. The coefficient normalization is an agent consequence.
(blueprint: lem-pur-ringed-coefficient-change-normalization).

Proof:
1. Restricting successively along bX and aX has the same underlying module as restricting along
aX prime; the equality aX followed by bX = aX prime identifies the actions. The identity on
underlying sheaves gives the ordinary restriction-composition isomorphism, and similarly on Y.
Exactness of restriction gives the termwise localized functors vX and vY. Localize those
ordinary isomorphisms and compose with xFactors and yFactors to obtain rhoX and rhoY with
exactly the equations in CoefficientRestrictionChangeNormalized. The remaining five
normalization clauses are the given compatibility hypotheses.
2. Commutation of the structural ring maps makes the two ordinary pushR functors after
restriction have the same scalar action, as seen by transposing against the specified geometric
adjunction. Thus the identity underlying direct-image map lifts to ordinaryBeta; it is
invertible by the same construction in reverse. Apply normalized right-derived composition to
its two factorizations to construct beta. Its equation on I and a K-injective resolution j of
the restricted I is exactly CoefficientDirectChangeNormalized.
3. Both constant-coefficient left derived functors derive the same IA.modules. Their canonical
universal comparison gives alpha, with alpha followed by the primed counit equal to the unprimed
counit. The two ordinary pushA functors are right adjoints to IA.modules, with the same
geometric Hom formula. Right-adjoint uniqueness gives ordinaryGamma with the prescribed
underlying identity. Its right-derived comparison gives gamma; evaluating on K-injectives gives
the constant normalization. Take sigma to be the adjoint mate of beta after the primed derived
unit. Naturality of adjunction supplies a natural transformation, and its defining formula is
CoefficientChangeNormalized. Together these construct CoefficientChange.
4. For any normalized CoefficientChange, compare the two composites in the kappa naturality
square on a K-injective I. Resolve its restricted module complex once more by a K-injective T.
The normalization equations for beta, rhoX, rhoY, gamma and kappa identify both composites with
the same localized ordinary direct-image map to the final resolution. This ordinary equality
holds because all three underlying comparisons are identities and the coefficient actions
commute by the hypotheses. Common K-injective refinements and naturality of the comparison maps
remove the chosen resolutions. Every derived object has a K-injective representative, so this
proves the kappa square for all objects.
5. Use the assumed CounitCompatibility equations for p and p prime: tau is the adjoint mate of
kappa, and tau prime is the mate of kappa prime. The normalized constant comparisons alpha and
gamma preserve the canonical derived adjunction by the representative Hom formula. The preceding
kappa square, after taking adjoint mates, becomes the displayed tau square: sigma is the mate of
beta by its normalization, while rhoX and rhoY are the restriction-composition identifications.
The triangle identities cancel the inserted units and counits. Taking mates is a bijection on
natural transformations, so this is equality of the specified derived maps and requires no
faithfulness of restriction. This establishes both clauses of IsNatural for every normalized
comparison. -/
theorem coefficientChange_exists
    (aX : constantRing JX A ⟶ RX) (aY : constantRing JY A ⟶ RY)
    (aI : constantRing JX A ⟶ RI)
    (o : OrdinaryPresentation direct geom IA IR c aX aY aI)
    [IA.modules.Additive]
    [HasDerivedCategory.{w} (modules RX)] [HasDerivedCategory.{w} (modules RY)]
    [HasDerivedCategory.{w} (modules (constantRing JX A))]
    [HasDerivedCategory.{w} (modules (constantRing JY A))]
    (p : DerivedPresentation o) (hp : CounitCompatibility p)
    (RX' RI' : Sheaf JX CommRingCat.{r}) (RY' : Sheaf JY CommRingCat.{r})
    (IR' : SheafOfModules.AlgebraicInverseImage inverse RY' RI') (c' : RI' ⟶ RX')
    (aX' : constantRing JX A ⟶ RX') (aY' : constantRing JY A ⟶ RY')
    (aI' : constantRing JX A ⟶ RI')
    (o' : OrdinaryPresentation direct geom IA IR' c' aX' aY' aI')
    [HasDerivedCategory.{w} (modules RX')] [HasDerivedCategory.{w} (modules RY')]
    (p' : DerivedPresentation o') (hp' : CounitCompatibility p')
    (bX : RX ⟶ RX') (bY : RY ⟶ RY') (bI : RI ⟶ RI')
    (haX : aX ≫ bX = aX') (haY : aY ≫ bY = aY') (haI' : aI ≫ bI = aI')
    (hc' : c ≫ bX = bI ≫ c')
    (hIR : IR.ringUnderlying.hom ≫ (sheafCompose JX (forget CommRingCat.{r})).map bI =
      inverse.map ((sheafCompose JY (forget CommRingCat.{r})).map bY) ≫ IR'.ringUnderlying.hom) :
    Nonempty (CoefficientChange p p' bX bY bI) ∧
      ∀ m : CoefficientChange p p' bX bY bI, m.IsNatural := by sorry

end CategoryTheory.RingedCoefficientCounit
