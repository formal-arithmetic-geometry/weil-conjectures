/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.Constant.ConstantAdicQuotientScalarComparison
public import Submission.WeilConjectures.ConstructibleSheaf.Defs
public import Mathlib.AlgebraicGeometry.Noetherian
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RestrictScalars
import all Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
import all Submission.WeilConjectures.AlgebraicGeometry.Pbc.PbcFinitePullbackConstructibility
import all Submission.WeilConjectures.AlgebraicGeometry.Constant.ConstantAdicQuotientScalarComparison
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleCoefficientSheaf
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
import Submission.WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Submission.WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf
import Submission.WeilConjectures.CategoryTheory.Sites.ConstantForget
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageComparison
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.CategoryTheory.Sites.Equivalence
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Submission.WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Ring
import Submission.WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageUnderlying
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleModelRingPresentation
import Submission.WeilConjectures.CategoryTheory.SheafPullbackUnitPresentation
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Submission.WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import Submission.WeilConjectures.CategoryTheory.ModuleInverseImageAdjunction
import Submission.WeilConjectures.CategoryTheory.ModuleInverseImageAction
import Submission.WeilConjectures.CategoryTheory.ModuleInverseImageActionOfPresentations
import Submission.WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageScalarGraph
import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf
import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Constructible
import Submission.WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleFiniteLocalConstancyReflection
import Submission.WeilConjectures.ConstructibleSheaf.Defs
import Submission.WeilConjectures.SixFunctors.ProEtale.Comparison.Defs
import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleLisseOrigin
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
import Submission.WeilConjectures.AlgebraicGeometry.EtaleSheaves
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleFixedModuleLocalConstancy
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleLocallyConstantSheaf
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import Mathlib.Algebra.Category.ModuleCat.AB
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleGeometricStalk
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Submission.WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitFunctor
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import Submission.WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantModuleValues
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleLisseFiniteModels
import Submission.WeilConjectures.ConstructibleSheaf.Pullback
import Submission.WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleLisseFiniteModelsFromLisse
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModelStalks
import Submission.WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Point.Over
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModelLocalConstancy
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CoverLifting
import Submission.WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafEquivalence
import Mathlib.CategoryTheory.Functor.TypeValuedFlat
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleOriginFromFiniteModels
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleComparisonLocalization
import Submission.WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import Submission.WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStar
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleEtaleFiniteModels
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleModelTypePartition
import Submission.WeilConjectures.AlgebraicGeometry.FpqcOpenSubschemeDescent
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleUniformModelEtaleCover
import Mathlib.CategoryTheory.Sites.SheafHom
import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleLocallyClassicalEtaleCover
import Mathlib.CategoryTheory.Sites.CoversTop.Basic
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleLocallyClassicalContinuity
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleComparisonSections
import Submission.WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
import Submission.WeilConjectures.CategoryTheory.LanContinuityFromRepresentables
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Adjunction.Limits
import Submission.WeilConjectures.AlgebraicGeometry.ComparisonPullbackCoherence
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparison
import Submission.WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
import Mathlib.AlgebraicGeometry.Pullbacks
import Submission.WeilConjectures.SixFunctors.BaseChange.Square
import Submission.WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Sites.Precoverage.Generates
import Mathlib.CategoryTheory.Sites.Finite
import Mathlib.CategoryTheory.Sites.LocalProperties
import Mathlib.CategoryTheory.Limits.Connected
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.CategoryTheory.Filtered.Connected
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.Basic.Finite.Prod
import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.LocallySurjective
import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
import Mathlib.CategoryTheory.Sites.Sheafification
import Submission.WeilConjectures.CategoryTheory.SiteConstantModuleFunctor
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.Algebra.Module.FinitePresentation
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantSheafStalk
import Mathlib.CategoryTheory.Abelian.RightDerived
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Submission.WeilConjectures.SixFunctors.ProEtale.Comparison.FullyFaithful
import Submission.WeilConjectures.AlgebraicGeometry.EtaleRestrictScalarsFunctorComparisons

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Core data for a single finite quotient étale origin

Source: Stacks Project, Tags 09AL and 09B1.
(blueprint: lem-weil-pbc-lisse-finite-quotient-etale-origin).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] HasDerivedCategory.ofIsGrothendieckAbelian

namespace FiniteQuotientOriginProof

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem inverseImage_additive {X Y : Scheme.{u}} (g : Y ⟶ X)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    (proEtaleModuleInverseImage g R).Additive :=
  (proEtaleModuleInverseImageAdjunction g R).left_adjoint_additive

private theorem inverseImage_limits {X Y : Scheme.{u}} (g : Y ⟶ X)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    PreservesFiniteLimits (proEtaleModuleInverseImage g R) :=
  proEtaleModuleInverseImage_preservesFiniteLimits g R

private theorem inverseImage_colimits {X Y : Scheme.{u}} (g : Y ⟶ X)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    PreservesFiniteColimits (proEtaleModuleInverseImage g R) := by
  have : PreservesColimitsOfSize.{0, 0} (proEtaleModuleInverseImage g R) :=
    (proEtaleModuleInverseImageAdjunction g R).leftAdjoint_preservesColimits
  infer_instance

attribute [local instance] inverseImage_additive inverseImage_limits inverseImage_colimits

private theorem scalar_additive (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B] :
    (scalarRestriction X B).Additive where
  map_add := by intros; ext U x; rfl

private theorem relative_additive {X Y : Scheme.{u}} (g : Y ⟶ X)
    (B : Type (u + 1)) [CommRing B] : (relativeRestriction g B).Additive where
  map_add := by intros; ext U x; rfl

private theorem scalar_equivalence (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B] :
    (scalarRestriction X B).IsEquivalence := scalarRestriction_equivalence X B

private theorem relative_equivalence {X Y : Scheme.{u}} (g : Y ⟶ X)
    (B : Type (u + 1)) [CommRing B] : (relativeRestriction g B).IsEquivalence := by
  let E := proEtaleScalarEquivalence Y ((adicLisseForget Y).mapIso (constantCoefficients g B))
  change (E.inverse ⋙ scalarRestriction Y B).IsEquivalence
  have := scalar_equivalence Y B
  infer_instance

attribute [local instance] scalar_additive relative_additive scalar_equivalence relative_equivalence

end FiniteQuotientOriginProof

/-- The fixed-coefficient encoding of modules over the constant ring sheaf.
Its underlying module-valued sheaf is restriction along the constant-section map.
Source: Stacks Project, Tags 093I and 03CY.
(blueprint: lem-weil-pbc-lisse-finite-quotient-etale-origin-core). -/
def finiteQuotientOriginEncoding (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B] :
    pbcModules X (adicLisseConstantRing X B) ⥤
      Sheaf (ProEt.topology X) (ModuleCat.{u + 1} B) where
  obj M := by
    let P := (PresheafOfModules.restrictScalars (adicLisseConstantUnit X B)).obj M.val
    let F : X.ProEtᵒᵖ ⥤ ModuleCat.{u + 1} B :=
      { obj := P.obj
        map f := P.map f
        map_id U := by ext x; exact ConcreteCategory.congr_hom (P.presheaf.map_id U) x
        map_comp f g := by ext x; exact ConcreteCategory.congr_hom (P.presheaf.map_comp f g) x }
    exact ⟨F, Presheaf.isSheaf_of_isSheaf_comp (ProEt.topology X) F
      (forget₂ (ModuleCat.{u + 1} B) AddCommGrpCat.{u + 1}) M.isSheaf⟩
  map φ := ⟨{
    app U := ((PresheafOfModules.restrictScalars (adicLisseConstantUnit X B)).map φ.val).app U
    naturality _ _ f := by
      ext x
      exact ConcreteCategory.congr_hom (φ.val.naturality f) x }⟩
  map_id M := by ext U x; rfl
  map_comp φ ψ := by ext U x; rfl

instance finiteQuotientOriginEncoding_additive (X : Scheme.{u})
    (B : Type (u + 1)) [CommRing B] : (finiteQuotientOriginEncoding X B).Additive where
  map_add := by intros; ext U x; rfl

instance finiteQuotientOriginEncoding_equivalence (X : Scheme.{u})
    (B : Type (u + 1)) [CommRing B] : (finiteQuotientOriginEncoding X B).IsEquivalence :=
  FiniteQuotientOriginProof.scalar_equivalence X B

/-- The actual fixed-coefficient realization of the pullback of a quotient complex.
Source: Stacks Project, Tags 09AL and 09B1.
(blueprint: lem-weil-pbc-lisse-finite-quotient-etale-origin-core). -/
def finiteQuotientOriginPullback {X Y : Scheme.{u}} (g : Y ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :=
  pbcDerivedRestrict (pbcLevelConstantComparison X d n).hom ⋙
    (finiteQuotientOriginEncoding X (A ⧸ d.ideal ^ (n + 1))).mapDerivedCategory ⋙
      (ProEtale.upperStar (ModuleCat.{u + 1} (A ⧸ d.ideal ^ (n + 1))) g).mapDerivedCategory

/-- The descended level, its actual comparison with the pullback of `K`, and local
finiteness data, before conditional transport. The comparison uses the fixed
`A/I^(n+1)` coefficient encoding after restriction from the completion quotient.

Source: Stacks Project, proetale.tex, Tags 09AL and 09B1
(blueprint: lem-weil-pbc-lisse-finite-quotient-etale-origin-core).
-/
structure LisseFiniteQuotientEtaleOriginCore
    (X Y : Scheme.{u}) (g : Y ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ)
    (K : DerivedCategory (pbcModules X ((pbcAdicRings X d).obj (op n))))
    (V : Y.Etale) where
  level : DerivedCategory (Sheaf V.left.smallEtaleTopology
    (ModuleCat.{u + 1} (AdicCompletion d.ideal A ⧸
      (d.ideal.map (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 1))))
  lisse : ∀ q : ℤ, IsFiniteLocallyConstantSheaf
    ((DerivedCategory.homologyFunctor _ q).obj level)
  vanishing : ∀ q : ℤ,
    IsZero ((DerivedCategory.homologyFunctor _ q).obj K) →
    IsZero ((DerivedCategory.homologyFunctor _ q).obj level)
  refinementLisse : ∀ (W : Y.ProEt) (_w : W ⟶ (toProEt Y).obj V) (q : ℤ),
    IsRelativelyFiniteLisseModule (W.hom ≫ g) (A ⧸ d.ideal ^ (n + 1))
      ((pbcRestrict ((adicTowerInverseImage (W.hom ≫ g)).map
        (pbcLevelConstantComparison X d n).hom)).obj
          ((DerivedCategory.homologyFunctor _ q).obj
            ((adicTowerPullback (W.hom ≫ g)
              ((pbcAdicRings X d).obj (op n))).obj K)))
  comparison : Nonempty
    ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (A ⧸ d.ideal ^ (n + 1)))
        V.left).mapDerivedCategory.obj
      ((Sheaf.restrictScalars V.left.smallEtaleTopology
        (constantAdicQuotientMap d.ideal n)).mapDerivedCategory.obj level) ≅
      (finiteQuotientOriginPullback (V.hom ≫ g) d n).obj K)

attribute [local instance] FiniteQuotientOriginProof.scalar_additive
  FiniteQuotientOriginProof.relative_additive FiniteQuotientOriginProof.scalar_equivalence
  FiniteQuotientOriginProof.relative_equivalence

end AlgebraicGeometry.Scheme
