/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.DiagonalEtaleComparison.DiagonalDncEtaleFactors
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.DiagonalEtaleComparison.DiagonalEtaleNormalTransport
import all WeilConjectures.SmoothPurity.PurityFiniteSetting.OrientationRefinement.DiagonalOrientationCompatibility
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteTwistTransportUniqueness
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Arrows
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
import WeilConjectures.AlgebraicGeometry.Relative.RelativeKummerExchangeGeneratorsSupplement
import WeilConjectures.AlgebraicGeometry.Etale.EtaleSinglePullbackComparisonsSupplement
import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.AlgebraicGeometry.Scheme
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateSheaf
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
import WeilConjectures.AlgebraicGeometry.Sites.Kummer
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Sites.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
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
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.Algebra.Homology.Site.SiteDerivedTensorDescent
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackBase
import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLinePullback
import WeilConjectures.EtaleCohomology.TateTwist.RootsOfUnityPullback
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTensorFamily
import WeilConjectures.CategoryTheory.NormalizedSignedTensorPowers
import WeilConjectures.CategoryTheory.Monoidal.IntTensorFamily
import WeilConjectures.CategoryTheory.IntTensorFamilyIso
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLocalLine
import WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.LocallyTrivialInverse
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.MonoidalComp
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit
import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackRest
import Mathlib.CategoryTheory.Abelian.Refinements
import Mathlib.Algebra.Homology.ShortComplex.Exact
import WeilConjectures.AlgebraicGeometry.ProperProjectionFormula
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
import WeilConjectures.CategoryTheory.Monoidal.EtaleDerivedTensorSymmetrySupplement
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Topology.Defs.Filter
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.SixFunctors.Etale.Derived.Tensor
import WeilConjectures.AlgebraicGeometry.ExactUnboundedExchange
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
import WeilConjectures.SixFunctors.BaseChange.Square
import WeilConjectures.SixFunctors.Etale.Derived.Shift
import WeilConjectures.SixFunctors.Etale.Derived.ReductionConservative
import Mathlib.CategoryTheory.Adjunction.Whiskering
import WeilConjectures.AlgebraicGeometry.Ordered.OrderedTateCoefficientComposition
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Dnc.ComparisonPullbackDerivedCoherence

/-! # The normal-integration square of an etale correspondence -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

attribute [local irreducible] OrientationRefinement.vectorBetaInverse Dnc.sectionBaseChange
  Etale.vectorIntegrationBaseCoefficientPullback VectorBundleZeroSection.scheme
  VectorBundleZeroSection.π VectorBundleZeroSection.over VectorBundleZeroSection.antiEquivalence
  Etale.rightDerivedLowerShriek Etale.rightDerivedUpperShriek
  Etale.rightDerivedUpperShriekAdjunction

private theorem tate_comp (P : PurityFiniteSetting.{u})
    {T S R : Scheme.{u}} (a : T ⟶ S) (b : S ⟶ R)
    (aR : R ⟶ Spec (.of P.field.k)) (aS : S ⟶ Spec (.of P.field.k)) (d : ℕ) :
    (OrientationRefinement.pull P a).mapIso (OrientationRefinement.tate P b aR d) ≪≫
        OrientationRefinement.tate P a aS d =
      (ProEtale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) a b).symm.app
          (P.diagonalTwist R d) ≪≫ OrientationRefinement.tate P (a ≫ b) aR d := by
  let tw := purityTwistTransport P.Coefficient P.diagonalExponent
    (pow_pos P.coefficients.prime.out.pos P.level) P.diagonalExponent_annihilates
  let cb := Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient
    P.diagonalExponent P.diagonalExponent_annihilates tw b (P.diagonalExponent_isUnit aR) d
  have hn := congrArg Iso.hom (Dnc.pullComparison_naturality P a cb)
  have hc := Dnc.pullComparison_comp P a b (P.diagonalTwistEtale R d)
  have ht := Etale.orderedTateCoefficientComposition P.Coefficient P.diagonalExponent
    P.diagonalExponent_annihilates tw a b (a ≫ b) rfl
    (P.diagonalExponent_isUnit aR) (P.diagonalExponent_isUnit aS) d
  apply Iso.ext
  apply (cancel_epi ((ProEtale.leftDerivedUpperStarComp
    (ModuleCat.{u + 1} P.Coefficient) a b).hom.app (P.diagonalTwist R d))).mp
  simp only [OrientationRefinement.tate, Functor.mapIso_trans, Iso.trans_hom,
    Functor.mapIso_hom, Iso.app_hom, Iso.symm_hom, Category.assoc,
    Iso.hom_inv_id_app_assoc]
  simp only [Iso.trans_hom, Functor.mapIso_hom] at hn
  erw [reassoc_of% hn]
  erw [← reassoc_of% hc]
  simp only [← Functor.map_comp]
  exact congrArg (fun z ↦ (Dnc.pullComparison P (a ≫ b)
    (P.diagonalTwistEtale R d)).hom ≫
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) T).mapDerivedCategory.map z) ht

private theorem tate_congr (P : PurityFiniteSetting.{u})
    {T S : Scheme.{u}} {a b : T ⟶ S} (h : a = b)
    (aS : S ⟶ Spec (.of P.field.k)) (d : ℕ) :
    (ProEtale.leftDerivedUpperStarCongr (ModuleCat.{u + 1} P.Coefficient) h).app
        (P.diagonalTwist S d) ≪≫ OrientationRefinement.tate P b aS d =
      OrientationRefinement.tate P a aS d := by
  subst b
  apply Iso.ext
  simp only [ProEtale.leftDerivedUpperStarCongr_rfl, Iso.trans_hom, Iso.app_hom,
    Iso.refl_hom, NatTrans.id_app, Category.id_comp]

private theorem tate_restrictionAlong (P : PurityFiniteSetting.{u})
    {U X : Scheme.{u}} (j : U ⟶ X) (W : X.Opens) (O : U.Opens)
    (k : O.toScheme ⟶ W.toScheme) (hk : k ≫ W.ι = O.ι ≫ j)
    (aX : X ⟶ Spec (.of P.field.k)) (aU : U ⟶ Spec (.of P.field.k)) (d : ℕ) :
    (OrientationRefinement.pull P k).mapIso
        (OrientationRefinement.tate P W.ι aX d) ≪≫
        OrientationRefinement.tate P k (W.ι ≫ aX) d =
      (OrientationCounit.restrictionAlong P j W O k hk).app (P.diagonalTwistEtale X d) ≪≫
        (OrientationRefinement.pull P O.ι).mapIso
          ((ProEtale.comparisonUpperStar
            (ModuleCat.{u + 1} P.Coefficient) U).mapDerivedCategory.mapIso
            (Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
              P.diagonalExponent_annihilates
              (purityTwistTransport P.Coefficient P.diagonalExponent
                (pow_pos P.coefficients.prime.out.pos P.level) P.diagonalExponent_annihilates)
              j (P.diagonalExponent_isUnit aX) d)) ≪≫
        OrientationRefinement.tate P O.ι aU d := by
  have hc := tate_comp P k W.ι aX (W.ι ≫ aX) d
  have hc' := tate_comp P O.ι j aX aU d
  have he := tate_congr P hk aX d
  erw [hc]
  have hcomp : (OrientationCounit.comparisonPull P j).app (P.diagonalTwistEtale X d) =
      Dnc.pullComparison P j (P.diagonalTwistEtale X d) := by
    unfold OrientationCounit.comparisonPull
    rfl
  unfold OrientationCounit.restrictionAlong
  erw [NatIso.trans_app]
  simp only [Iso.trans_assoc]
  change _ =
    ((ProEtale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) k W.ι).symm ≪≫
      ProEtale.leftDerivedUpperStarCongr (ModuleCat.{u + 1} P.Coefficient) hk ≪≫
      ProEtale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) O.ι j).app
        (P.diagonalTwist X d) ≪≫
      (OrientationRefinement.pull P O.ι).mapIso
        ((OrientationCounit.comparisonPull P j).app (P.diagonalTwistEtale X d)) ≪≫ _
  erw [hcomp]
  simp only [NatIso.trans_app, Iso.trans_assoc]
  erw [← Iso.trans_assoc ((OrientationRefinement.pull P O.ι).mapIso
    (Dnc.pullComparison P j (P.diagonalTwistEtale X d)))]
  rw [← Functor.mapIso_trans]
  change _ = _ ≪≫ _ ≪≫ _ ≪≫
    ((OrientationRefinement.pull P O.ι).mapIso (OrientationRefinement.tate P j aX d) ≪≫ _)
  erw [hc']
  apply Iso.ext
  simpa only [Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Category.assoc,
    Iso.hom_inv_id_app_assoc] using congrArg Iso.hom
      (congrArg (fun z ↦ (ProEtale.leftDerivedUpperStarComp
        (ModuleCat.{u + 1} P.Coefficient) k W.ι).symm.app (P.diagonalTwist X d) ≪≫ z)
        he.symm)

private theorem compared_beta (P : PurityFiniteSetting.{u}) {X U : Scheme.{u}}
    (j : U ⟶ X) (aX : X ⟶ Spec (.of P.field.k)) (d : ℕ)
    {M : Etale.DerivedCategoryModule P.Coefficient X}
    {M' : Etale.DerivedCategoryModule P.Coefficient U}
    (β : M ≅ P.diagonalTwistEtale X d) (β' : M' ≅ P.diagonalTwistEtale U d)
    (s : (Etale.ordinaryFinitePullback P.Coefficient j).obj M ≅ M')
    (hβ : (Etale.ordinaryFinitePullback P.Coefficient j).mapIso β ≪≫
        Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
          P.diagonalExponent_annihilates
          (purityTwistTransport P.Coefficient P.diagonalExponent
            (pow_pos P.coefficients.prime.out.pos P.level) P.diagonalExponent_annihilates)
          j (P.diagonalExponent_isUnit aX) d = s ≪≫ β') :
    (OrientationRefinement.pull P j).mapIso
        ((ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.mapIso β) ≪≫
        OrientationRefinement.tate P j aX d =
      Dnc.pullComparison P j M ≪≫
        (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) U).mapDerivedCategory.mapIso s ≪≫
        (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) U).mapDerivedCategory.mapIso β' := by
  dsimp only [Etale.ordinaryFinitePullback] at hβ
  dsimp only [OrientationRefinement.tate]
  erw [← Iso.trans_assoc, Dnc.pullComparison_naturality P j β]
  simp only [Iso.trans_assoc, ← Functor.mapIso_trans, hβ]

private theorem factor_square {C : Type*} [Category* C]
    {A B N K L M : C} (m : A ≅ B) (tj : A ≅ K) (tv : B ≅ K)
    (z : N ≅ K) (nj : N ≅ L) (nv : N ≅ M) (hc : m ≪≫ tv = tj) :
    m ≪≫ (tv ≪≫ z.symm ≪≫ nv) =
      (tj ≪≫ z.symm ≪≫ nj) ≪≫ (nj.symm ≪≫ nv) := by
  simp only [Iso.trans_assoc, Iso.self_symm_id_assoc]
  rw [← Iso.trans_assoc m tv, hc]

/-- Compatibility of only the Tate and integration factors with the actual normal map.
Source: diagonal-dualizing proof Step 2 and its final base-change paragraph;
orientation-charts proof Step 4.

Proof: identify the actual normal cones using the zero fibre of the coefficientwise
Rees maps on the two self-products. Their degree-one maps are the relative
differentials of jO and vO, and are isomorphisms since these maps are etale.
Use C.normalized and E.normalized to replace beta on any vector-bundle model by
zero-section restriction of inverse integration-transposed purity. Vector integration
base change gives the square on local frames; linear trace invariance removes the
frame choices. Compose the two single-arrow squares through the normal cone of the
common source. The Tate pullback compositors and site comparison identify their
outer composite with m. The root-inclusion and pure-tensor normalizations make
any supplied t equal to the canonical Tate transport used by the integration theorem.
No deformation isomorphism, alpha or rho is used here.
The argument includes rank zero, where the ordered tensor has no factors, and
empty opens, where the required morphism is unique.
(blueprint: lem-pur-diagonal-etale-beta-square). -/
theorem diagonalDncEtaleNaturality_beta (P : PurityFiniteSetting.{u})
    {X Z Y : Scheme.{u}} (d : ℕ) (f : X ⟶ Y) (g : Z ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [SmoothOfRelativeDimension d f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [SmoothOfRelativeDimension d g]
    [IsNoetherian X] [IsNoetherian Z] [IsNoetherian Y]
    [HasCompactification f] [HasCompactification g]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (V : Y.affineOpens)
    (C : OrientationRefinement.Chart P f aY d V)
    (E : OrientationRefinement.Chart P g aY d V)
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates)
    (U : Scheme.{u}) [IsNoetherian U]
    (j : U ⟶ X) [Etale j] [IsSeparated j] [LocallyOfFiniteType j] [QuasiCompact j]
    (v : U ⟶ Z) [Etale v] [IsSeparated v] [LocallyOfFiniteType v] [QuasiCompact v]
    (w : v ≫ g = j ≫ f)
    [HasCompactification (j ≫ f)] [HasCompactification (v ≫ g)]
    (O : U.Opens) (jO : O.toScheme ⟶ (f ⁻¹ᵁ V.1).toScheme)
    (vO : O.toScheme ⟶ (g ⁻¹ᵁ V.1).toScheme)
    (hj : jO ≫ (f ⁻¹ᵁ V.1).ι = O.ι ≫ j)
    (hv : vO ≫ (g ⁻¹ᵁ V.1).ι = O.ι ≫ v) :
    let νU := (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) U).mapDerivedCategory
    let T := OrientationRefinement.pull P O.ι
    let cj := OrientationCounit.restrictionAlong P j (f ⁻¹ᵁ V.1) O jO hj
    let cv := OrientationCounit.restrictionAlong P v (g ⁻¹ᵁ V.1) O vO hv
    let a :=
      (Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates t j (P.diagonalExponent_isUnit (f ≫ aY)) d).hom ≫
      (Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates t v (P.diagonalExponent_isUnit (g ≫ aY)) d).inv
    let m := (cj.app (P.diagonalTwistEtale X d)).hom ≫
      T.map (νU.map a) ≫
      (cv.app (P.diagonalTwistEtale Z d)).inv
    let n := DiagonalEtaleComparison.normalTransport P d f g aY V C.geometry E.geometry U j v w
      O jO vO hj hv
    m ≫ (OrientationRefinement.pull P vO).map
        (DiagonalEtaleComparison.twistToNormal P d g aY V E).hom =
      (OrientationRefinement.pull P jO).map
        (DiagonalEtaleComparison.twistToNormal P d f aY V C).hom ≫ n.hom := by
  let tw := purityTwistTransport P.Coefficient P.diagonalExponent
    (pow_pos P.coefficients.prime.out.pos P.level) P.diagonalExponent_annihilates
  have ht : t = tw := Etale.ordinaryFiniteTwistTransport_unique _ _ _ t tw
  subst t
  let := C.geometry.separated
  let := C.geometry.finiteType
  let := C.geometry.quasiCompact
  let := C.geometry.smoothDimension
  let := C.geometry.baseFiniteType
  let := C.geometry.baseQuasiCompact
  let := C.geometry.sourceSeparated
  let := C.geometry.sourceFiniteType
  let := C.geometry.sourceQuasiCompact
  let := E.geometry.separated
  let := E.geometry.finiteType
  let := E.geometry.quasiCompact
  let := E.geometry.smoothDimension
  let := E.geometry.baseFiniteType
  let := E.geometry.baseQuasiCompact
  let := E.geometry.sourceSeparated
  let := E.geometry.sourceFiniteType
  let := E.geometry.sourceQuasiCompact
  have : Etale (jO ≫ (f ⁻¹ᵁ V.1).ι) := by rw [hj]; infer_instance
  have : Etale jO := Etale.of_comp jO (f ⁻¹ᵁ V.1).ι
  have : Etale (vO ≫ (g ⁻¹ᵁ V.1).ι) := by rw [hv]; infer_instance
  have : Etale vO := Etale.of_comp vO (g ⁻¹ᵁ V.1).ι
  have : IsSeparated (jO ≫ (f ⁻¹ᵁ V.1).ι) := by rw [hj]; infer_instance
  have : IsSeparated jO := IsSeparated.of_comp jO (f ⁻¹ᵁ V.1).ι
  have : IsSeparated (vO ≫ (g ⁻¹ᵁ V.1).ι) := by rw [hv]; infer_instance
  have : IsSeparated vO := IsSeparated.of_comp vO (g ⁻¹ᵁ V.1).ι
  have : QuasiCompact jO := inferInstance
  have : QuasiCompact vO := inferInstance
  have : SmoothOfRelativeDimension 0 jO :=
    (Etale.iff_smoothOfRelativeDimension_zero jO).mp inferInstance
  let h := jO ≫ (f ∣_ V.1)
  have hd : SmoothOfRelativeDimension (0 + d) h :=
    inferInstanceAs (SmoothOfRelativeDimension (0 + d) (jO ≫ (f ∣_ V.1)))
  have : SmoothOfRelativeDimension d h :=
    Eq.mp (congrArg (fun n ↦ SmoothOfRelativeDimension n h) (Nat.zero_add d)) hd
  have he : vO ≫ (g ∣_ V.1) = h := by
    apply (cancel_mono V.1.ι).mp
    dsimp only [h]
    rw [Category.assoc, Category.assoc, morphismRestrict_ι, morphismRestrict_ι,
      ← Category.assoc, hv, ← Category.assoc, hj]
    simp only [Category.assoc, w]
  let B := (f ⁻¹ᵁ V.1).toScheme
  let D := (g ⁻¹ᵁ V.1).toScheme
  let aB := (f ∣_ V.1) ≫ V.1.ι ≫ aY
  let aD := (g ∣_ V.1) ≫ V.1.ι ≫ aY
  let aO := h ≫ V.1.ι ≫ aY
  let pB := pullback.fst (f ∣_ V.1) (f ∣_ V.1)
  let pD := pullback.fst (g ∣_ V.1) (g ∣_ V.1)
  let pO := pullback.fst h h
  let sB := pullback.diagonal (f ∣_ V.1)
  let sD := pullback.diagonal (g ∣_ V.1)
  let sO := pullback.diagonal h
  let qB := Scheme.Hom.normalConeProj pB sB
  let qD := Scheme.Hom.normalConeProj pD sD
  let qO := Scheme.Hom.normalConeProj pO sO
  let := P.noetherian aB
  let := P.noetherian aD
  let := P.noetherian aO
  let := Dnc.normalCompactifiable P d pB aB sB (pullback.diagonal_fst _)
  let := Dnc.normalCompactifiable P d pD aD sD (pullback.diagonal_fst _)
  let := Dnc.normalCompactifiable P d pO aO sO (pullback.diagonal_fst _)
  let : SmoothOfRelativeDimension d qB :=
    (Scheme.Hom.normalConeData d (pullback.diagonal_fst _)).smoothOfRelativeDimension_proj
  let : SmoothOfRelativeDimension d qD :=
    (Scheme.Hom.normalConeData d (pullback.diagonal_fst _)).smoothOfRelativeDimension_proj
  let : SmoothOfRelativeDimension d qO :=
    (Scheme.Hom.normalConeData d (pullback.diagonal_fst _)).smoothOfRelativeDimension_proj
  let := SmoothOfRelativeDimension.smooth d qB
  let := SmoothOfRelativeDimension.smooth d qD
  let := SmoothOfRelativeDimension.smooth d qO
  let := Dnc.normalQuasiCompact d pB sB (pullback.diagonal_fst _)
  let := Dnc.normalQuasiCompact d pD sD (pullback.diagonal_fst _)
  let := Dnc.normalQuasiCompact d pO sO (pullback.diagonal_fst _)
  let := Dnc.invertibleExponent P (qB ≫ aB)
  let := Dnc.invertibleExponent P (qD ≫ aD)
  let := Dnc.invertibleExponent P (qO ≫ aO)
  let := P.noetherian (qB ≫ aB)
  let := P.noetherian (qD ≫ aD)
  let := P.noetherian (qO ≫ aO)
  obtain ⟨FB, hFB, eB, heB, hzB⟩ := C.vectorModel
  obtain ⟨FD, hFD, eD, heD, hzD⟩ := E.vectorModel
  let := hFB
  let := hFD
  obtain ⟨hFO, _, rO, eO, _, _, heO, hzO⟩ := SectionReesBaseChange.normal_bundle d
    pO sO (pullback.diagonal_fst _)
  let := hFO
  let FO := ConormalGradedAlgebra.piece sO 1
  let e : VectorBundleZeroSection.scheme O.toScheme d FO ≅ sO.ker.normalCone :=
    (rO ≪≫ eO).symm
  have heπ : e.hom ≫ qO = VectorBundleZeroSection.π O.toScheme d FO :=
    (Iso.inv_comp_eq _).2 heO.symm
  have hez : VectorBundleZeroSection.zero O.toScheme d FO ≫ e.hom =
      sO.normalConeZeroSection := ((Iso.eq_comp_inv _).2 hzO).symm
  let := (Etale.vectorIntegration_geometry O.toScheme d FO).1
  let := (Etale.vectorIntegration_geometry O.toScheme d FO).2.1
  let := Dnc.compactifiable P (VectorBundleZeroSection.π O.toScheme d FO) aO
  let := OrientationRefinement.vector_beta_isIso P O.toScheme aO d FO
  let c := (Etale.leftDerivedUpperStarId (ModuleCat.{u + 1} P.Coefficient)
      O.toScheme).symm.app (Etale.sectionInvariant P.Coefficient qO sO.normalConeZeroSection) ≪≫
    Dnc.sectionBaseChange P.Coefficient d qO
      (b := 𝟙 O.toScheme) (f' := VectorBundleZeroSection.π O.toScheme d FO) (a := e.hom)
      (IsPullback.of_horiz_isIso ⟨heπ.trans (Category.comp_id _).symm⟩)
      sO.normalConeZeroSection (VectorBundleZeroSection.zero O.toScheme d FO)
      (hez.trans (Category.id_comp _).symm)
  let βO : Etale.sectionInvariant P.Coefficient qO sO.normalConeZeroSection ≅
      P.diagonalTwistEtale O.toScheme d :=
    c ≪≫ (asIso (OrientationRefinement.vectorBetaInverse P O.toScheme aO d FO)).symm
  have hnO : βO.inv ≫ c.hom =
      OrientationRefinement.vectorBetaInverse P O.toScheme aO d FO := by
    simp only [βO, Iso.trans_inv, Iso.symm_inv, asIso_hom, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
  have hb := OrientationRefinement.model_beta_compat P aB aO d qB qO
    sB.normalConeZeroSection sO.normalConeZeroSection jO
    (DiagonalEtaleComparison.normalMap d (f ∣_ V.1) h jO rfl)
    (DiagonalEtaleComparison.normalGeometry d (f ∣_ V.1) h jO rfl).1
    (DiagonalEtaleComparison.normalGeometry d (f ∣_ V.1) h jO rfl).2
    FB FO eB e heB heπ hzB hez C.betaEtale βO
    (C.normalized FB eB heB hzB) hnO
  have hd := OrientationRefinement.model_beta_compat P aD aO d qD qO
    sD.normalConeZeroSection sO.normalConeZeroSection vO
    (DiagonalEtaleComparison.normalMap d (g ∣_ V.1) h vO he)
    (DiagonalEtaleComparison.normalGeometry d (g ∣_ V.1) h vO he).1
    (DiagonalEtaleComparison.normalGeometry d (g ∣_ V.1) h vO he).2
    FD FO eD e heD heπ hzD hez E.betaEtale βO
    (E.normalized FD eD heD hzD) hnO
  let νO := (ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} P.Coefficient) O.toScheme).mapDerivedCategory
  let z := Dnc.normalComparison P d pO aO sO (pullback.diagonal_fst h) ≪≫ νO.mapIso βO
  let nj := DiagonalEtaleComparison.normal P d (f ∣_ V.1) h (V.1.ι ≫ aY) jO rfl
  let nv := DiagonalEtaleComparison.normal P d (g ∣_ V.1) h (V.1.ι ≫ aY) vO he
  have hbj : (OrientationRefinement.pull P jO).mapIso
        (OrientationRefinement.beta P f aY d V C.geometry C.betaEtale) ≪≫
        OrientationRefinement.tate P jO aB d = nj.symm ≪≫ z := by
    have hh := compared_beta P jO aB d C.betaEtale βO _ hb
    dsimp only [OrientationRefinement.beta]
    simp only [Functor.mapIso_trans, Iso.trans_assoc]
    erw [hh]
    dsimp only [nj, DiagonalEtaleComparison.normal, z]
    simp only [OrientationRefinement.normalEtale, νO, pO, aO, sO, qO, qB, pB, sB,
      Iso.trans_symm, Functor.mapIso_symm, Iso.symm_symm_eq, Iso.trans_assoc,
      Iso.symm_self_id_assoc]
  have hdv : (OrientationRefinement.pull P vO).mapIso
        (OrientationRefinement.beta P g aY d V E.geometry E.betaEtale) ≪≫
        OrientationRefinement.tate P vO aD d = nv.symm ≪≫ z := by
    have hh := compared_beta P vO aD d E.betaEtale βO _ hd
    dsimp only [OrientationRefinement.beta]
    simp only [Functor.mapIso_trans, Iso.trans_assoc]
    erw [hh]
    dsimp only [nv, DiagonalEtaleComparison.normal, z]
    simp only [OrientationRefinement.normalEtale, νO, pO, aO, sO, qO, qD, pD, sD,
      Iso.trans_symm, Functor.mapIso_symm, Iso.symm_symm_eq, Iso.trans_assoc,
      Iso.symm_self_id_assoc]
  have hbj' := congrArg
    (fun e ↦ OrientationRefinement.tate P jO aB d ≪≫ e) (congrArg Iso.symm hbj)
  have hdv' := congrArg
    (fun e ↦ OrientationRefinement.tate P vO aD d ≪≫ e) (congrArg Iso.symm hdv)
  simp only [Iso.trans_symm, Iso.symm_symm_eq, Iso.self_symm_id_assoc,
    ← Functor.mapIso_symm] at hbj' hdv'
  let cj := OrientationCounit.restrictionAlong P j (f ⁻¹ᵁ V.1) O jO hj
  let cv := OrientationCounit.restrictionAlong P v (g ⁻¹ᵁ V.1) O vO hv
  let τj := Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
    P.diagonalExponent_annihilates tw j (P.diagonalExponent_isUnit (f ≫ aY)) d
  let τv := Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
    P.diagonalExponent_annihilates tw v (P.diagonalExponent_isUnit (g ≫ aY)) d
  let νU := (ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} P.Coefficient) U).mapDerivedCategory
  let T := OrientationRefinement.pull P O.ι
  let m := cj.app (P.diagonalTwistEtale X d) ≪≫ T.mapIso (νU.mapIso (τj ≪≫ τv.symm)) ≪≫
    (cv.app (P.diagonalTwistEtale Z d)).symm
  let tj := (OrientationRefinement.pull P jO).mapIso
    (OrientationRefinement.tate P (f ⁻¹ᵁ V.1).ι (f ≫ aY) d) ≪≫
    OrientationRefinement.tate P jO aB d
  let tv := (OrientationRefinement.pull P vO).mapIso
    (OrientationRefinement.tate P (g ⁻¹ᵁ V.1).ι (g ≫ aY) d) ≪≫
    OrientationRefinement.tate P vO aD d
  have hc : m ≪≫ tv = tj := by
    have hjt := tate_restrictionAlong P j (f ⁻¹ᵁ V.1) O jO hj (f ≫ aY) (j ≫ f ≫ aY) d
    have hvt := tate_restrictionAlong P v (g ⁻¹ᵁ V.1) O vO hv (g ≫ aY) (j ≫ f ≫ aY) d
    dsimp only [tj, tv]
    erw [hjt, hvt]
    simp only [m, cj, cv, τj, τv, νU, T, tw, Functor.mapIso_trans,
      Functor.mapIso_symm, Iso.trans_assoc, Iso.symm_self_id_assoc]
  have hfactors : (OrientationRefinement.pull P jO).mapIso
        (DiagonalEtaleComparison.twistToNormal P d f aY V C) = tj ≪≫ z.symm ≪≫ nj := by
    simp only [DiagonalEtaleComparison.twistToNormal, Functor.mapIso_trans]
    rw [hbj']
    simp only [tj, Iso.trans_assoc]
  have gfactors : (OrientationRefinement.pull P vO).mapIso
        (DiagonalEtaleComparison.twistToNormal P d g aY V E) = tv ≪≫ z.symm ≪≫ nv := by
    simp only [DiagonalEtaleComparison.twistToNormal, Functor.mapIso_trans]
    rw [hdv']
    simp only [tv, Iso.trans_assoc]
  have hi : m ≪≫ (OrientationRefinement.pull P vO).mapIso
        (DiagonalEtaleComparison.twistToNormal P d g aY V E) =
      (OrientationRefinement.pull P jO).mapIso
        (DiagonalEtaleComparison.twistToNormal P d f aY V C) ≪≫ (nj.symm ≪≫ nv) := by
    exact (congrArg (fun e ↦ m ≪≫ e) gfactors).trans
      ((factor_square m tj tv z nj nv hc).trans
        (congrArg (fun e ↦ e ≪≫ (nj.symm ≪≫ nv)) hfactors.symm))
  simpa only [m, τj, τv, cj, cv, νU, T, nj, nv, h,
    DiagonalEtaleComparison.normalTransport, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, Functor.map_comp, Category.assoc] using congrArg Iso.hom hi

end WeilConjectures.PurityFiniteSetting
