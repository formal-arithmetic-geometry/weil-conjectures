/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Rational.RationalRealizationPullbackComparison
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcActualRingedExchange
import all WeilConjectures.AlgebraicGeometry.Rational.RationalRealizationPullbackComparison
import all WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedOrdinaryComparisons
import all WeilConjectures.AlgebraicGeometry.ProEtaleDerivedPullbackComposition
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsCanonicalAdjunctionSupplement
import all WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingInverseImage
import all WeilConjectures.AlgebraicGeometry.WeilSheaf.ProfiniteCoefficientInverseImageSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.CategoryTheory.Adjunction.Mates
import all WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import all WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all Mathlib.Algebra.Homology.HomologicalComplex
import all Mathlib.Algebra.Homology.Additive
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import all WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import all Mathlib.CategoryTheory.Types.Basic
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import all Mathlib.LinearAlgebra.TensorProduct.Vanishing
import all Mathlib.RingTheory.TensorProduct.DirectLimitFG
import all Mathlib.LinearAlgebra.TensorProduct.Finiteness
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import all WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import all Mathlib.CategoryTheory.Sites.Sheaf
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all Mathlib.CategoryTheory.Sites.Limits
import all Mathlib.CategoryTheory.Adjunction.Limits
import all Mathlib.CategoryTheory.Limits.Types.Pullbacks
import all Mathlib.CategoryTheory.Functor.EpiMono
import all Mathlib.CategoryTheory.Limits.Types.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import all Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import all WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.CategoryTheory.Sites.PreservesSheafification
import all Mathlib.CategoryTheory.Limits.Preserves.Limits
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.RingTheory.Flat.CategoryTheory
import all Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import all Mathlib.Algebra.Homology.Embedding.CochainComplex
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import all WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Preadditive
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage
import all Mathlib.CategoryTheory.Sites.Pullback
import all WeilConjectures.CategoryTheory.SiteCoveringAxioms
import all Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import all Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import all Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import all Mathlib.CategoryTheory.Adjunction.Additive
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import all WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
import all WeilConjectures.CategoryTheory.Site.SitePullbackAbelianUnderlyingSupplement
import all WeilConjectures.AlgebraicGeometry.ProEtaleAlgebraicInverseImage
import all WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import all WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import all Mathlib.AlgebraicGeometry.Sites.Proetale
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import all WeilConjectures.CategoryTheory.Site.SiteInverseImageTensor
import all WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all Mathlib.CategoryTheory.Monoidal.Ring
import all WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import all WeilConjectures.AlgebraicGeometry.ProEtaleTensorComparison.ProEtaleInverseImageTensorComparisonSupplement
import all WeilConjectures.AlgebraicGeometry.ProEtaleTensorCompositionUnit
import all WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
import all Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-! # Ordinary rational coefficient identity and the normalized module and derived identity.

Source: Bhatt--Scholze, Remark 6.8.15, p. 62; Stacks Tags 03CB, 0D6D, 07A4, 099N.
(blueprint: lem-per-rational-ordinary-pullback-identity).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

attribute [local irreducible] Functor.sheafPullbackConstruction.sheafPullback
  proEtaleRingInverseImageComp LocallyRingedSpace.comp PresheafedSpace.comp

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

variable {X Y Z : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
  [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
  [Fact (∃ n : ℕ, topologicalKrullDim Y ≤ n)]
  [Fact (∃ n : ℕ, topologicalKrullDim Z ≤ n)]
  [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
  [Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y))]
  [Fact (∀ z : Z, IsUnit (l : Z.presheaf.stalk z))]


private theorem ordinaryIdentityCoefficient (sX : RationalModuleRealization l E X)
    (a : RationalRealizationPullbackComparison l E (𝟙 X) sX sX) :
    a.rationalCoefficient = (proEtaleRingInverseImageId X).hom.app
      (rationalCoefficientSheaf l X E) := by
  let := coefficientExtensionNormedField l E
  let adj := proEtaleSheafAdjunction (𝟙 X) CommRingCat.{u + 1}
  let e := Functor.sheafPushforwardContinuousId'
    (MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X) CommRingCat.{u + 1}
      (ProEt.topology X)
  have he : adj.homEquiv _ _ ((proEtaleRingInverseImageId X).hom.app
      (rationalCoefficientSheaf l X E)) = e.inv.app (rationalCoefficientSheaf l X E) := by
    exact (unit_conjugateEquiv_symm Adjunction.id adj e.inv
      (rationalCoefficientSheaf l X E)).symm
  apply (adj.homEquiv _ _).injective
  refine Eq.trans ?_ he.symm
  apply Sheaf.hom_ext
  ext U s
  apply ContinuousMap.ext
  intro x
  exact a.rational_normalization U.unop s x

private def ordinaryIdentityRight
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    pbcRestrict ((proEtaleRingInverseImageId X).hom.app R) ⋙
      proEtaleRingModuleDirectImage (𝟙 X) R
        ((proEtaleSheafInverseImage (𝟙 X) CommRingCat.{u + 1}).obj R) (Iso.refl _) ≅
      𝟭 (pbcModules X R) := by
  let c := (proEtaleRingInverseImageId X).app R
  let d := (modulePushId_generic X R c rfl).exists.choose
  let F := proEtaleBaseChange (𝟙 X)
  let B := (adicLisseForget X).obj R
  let A := (adicLisseForget X).obj
    ((proEtaleSheafInverseImage (𝟙 X) CommRingCat.{u + 1}).obj R)
  let φ := (adicLisseForget X).map
    (proEtaleRingDirectImageMap (𝟙 X) R
      ((proEtaleSheafInverseImage (𝟙 X) CommRingCat.{u + 1}).obj R) (Iso.refl _))
  let ψ := (adicLisseForget X).map c.hom
  have hh : φ ≫ (proEtaleSheafDirectImage (𝟙 X) RingCat.{u + 1}).map ψ =
      (adicLisseForget X).map (proEtaleRingDirectImageMap (𝟙 X) R R c) := by
    dsimp only [φ, ψ, proEtaleRingDirectImageMap, Iso.refl_hom]
    erw [(proEtaleSheafDirectImage (𝟙 X) CommRingCat.{u + 1}).map_id, Category.comp_id]
    rfl
  exact SheafOfModules.pushforwardCongr (F := F) (J := ProEt.topology X)
    (K := ProEt.topology X) (R := B) (S := B)
    (φ := φ ≫ (proEtaleSheafDirectImage (𝟙 X) RingCat.{u + 1}).map ψ) hh ≪≫ d


omit [IsNoetherian X] [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)] in
private theorem ordinaryIdentityRight_hom
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (N : pbcModules X R) (V : X.ProEt)
    (m : ((pbcRestrict ((proEtaleRingInverseImageId X).hom.app R) ⋙
      proEtaleRingModuleDirectImage (𝟙 X) R
        ((proEtaleSheafInverseImage (𝟙 X) CommRingCat.{u + 1}).obj R) (Iso.refl _)).obj
          N).val.obj (op V)) :
    ((ordinaryIdentityRight R).hom.app N).val.app (op V) m =
      N.val.map ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X).inv.app V).op m := by
  exact (modulePushId_generic X R ((proEtaleRingInverseImageId X).app R) rfl).exists.choose_spec
    N V m

omit [IsNoetherian X] [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)] in
private theorem ordinaryIdentityRight_inv
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (N : pbcModules X R) (V : X.ProEt) (m : N.val.obj (op V)) :
    ((ordinaryIdentityRight R).inv.app N).val.app (op V) m =
      N.val.map ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X).hom.app V).op m := by
  let e := ordinaryIdentityRight R
  let δ := (MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X).app V
  have hi := congrArg (fun z ↦ z.val.app (op V) m) (e.inv_hom_id_app N)
  have hs := ordinaryIdentityRight_hom R N V ((e.inv.app N).val.app (op V) m)
  have h := congrArg (fun z ↦ N.val.map δ.hom.op z) (hs.symm.trans hi)
  exact (inverse_restriction N δ ((e.inv.app N).val.app (op V) m)).symm.trans h


set_option maxHeartbeats 800000 in
-- Nested chart conversions arise in the explicit tensor-section normalization.
/-- Ordinary rational coefficient identity and the normalized module and derived identity.
Source: Stacks Tags 03EL, 0D6D and 07A4; BS Remark 6.8.15.

Proof: coefficient restriction normalization identifies the identity coefficient map
with the inverse-image identity on continuous functions. The ordinary identity
comparison multiplies the coefficient into the module and restricts along the
specified pullbackId chart isomorphism; its inverse inserts one. Balancing and
local generation prove both inverse identities and the displayed section formula.
Derive this isomorphism on flat-term K-flat representatives, then use the fixed
computation counits to obtain the displayed equation on arbitrary complexes.
The identity counit is precisely the chain map of scalar multiplication.
(blueprint: lem-per-rational-ordinary-pullback-identity). -/
theorem rationalOrdinaryPullbackIdentity (sX : RationalModuleRealization l E X)
    (a : RationalRealizationPullbackComparison l E (𝟙 X) sX sX) :
    let unitSection {S T : Scheme.{u}} (g : S ⟶ T)
        (c : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
          (rationalCoefficientSheaf l T E) ⟶ rationalCoefficientSheaf l S E)
        (M : pbcModules T (rationalCoefficientSheaf l T E))
        (V : T.ProEt) (m : M.val.obj (op V)) :
        ((rationalPullModule l E g c).obj M).val.obj
          (op ((proEtaleBaseChange g).obj V)) :=
      pbcTensorSection c
        ((proEtaleRingModulePullback g (rationalCoefficientSheaf l T E)
          ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
            (rationalCoefficientSheaf l T E)) (Iso.refl _)).obj M)
        (op ((proEtaleBaseChange g).obj V)) 1
        (proEtaleRingModuleUnitSection g (rationalCoefficientSheaf l T E)
          ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
            (rationalCoefficientSheaf l T E)) (Iso.refl _) M V m)
    let scalarMul (T : Scheme.{u})
        (M : pbcModules T (rationalCoefficientSheaf l T E)) (V : T.ProEtᵒᵖ)
        (e : (rationalCoefficientSheaf l T E).obj.obj V) (m : M.val.obj V) : M.val.obj V :=
      e • m
    (a.rationalCoefficient =
    (proEtaleRingInverseImageId X).hom.app
      (rationalCoefficientSheaf l X E)) ∧
    ∃ (moduleId : rationalPullModule l E (𝟙 X) a.rationalCoefficient ≅ 𝟭 _),
    (∀ (M : pbcModules X (rationalCoefficientSheaf l X E)) (V : X.ProEt)
      (m : M.val.obj (op V))
      (e : (rationalCoefficientSheaf l X E).obj.obj (op ((proEtaleBaseChange (𝟙 X)).obj V))),
    (moduleId.hom.app M).val.app (op ((proEtaleBaseChange (𝟙 X)).obj V))
        (scalarMul X
          ((rationalPullModule l E (𝟙 X) a.rationalCoefficient).obj M)
          (op ((proEtaleBaseChange (𝟙 X)).obj V)) e
          (unitSection (𝟙 X) a.rationalCoefficient M V m)) =
      scalarMul X M (op ((proEtaleBaseChange (𝟙 X)).obj V)) e
        (M.val.map ((MorphismProperty.Over.pullbackId _ _ X).hom.app V).op m)) ∧
    ∃ (ambientId : rationalPullDerived l E (𝟙 X) a.rationalCoefficient ≅ 𝟭 _),
    (∀ P : CochainComplex (pbcModules X (rationalCoefficientSheaf l X E)) ℤ,
    ambientId.hom.app (DerivedCategory.Q.obj P) =
      rationalPullComplexCounit l E (𝟙 X) a.rationalCoefficient P ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex moduleId (.up ℤ) ≪≫
            Functor.mapHomologicalComplexIdIso _ (.up ℤ)).hom.app P)) := by
  classical
  dsimp only
  have hc := ordinaryIdentityCoefficient l E sX a
  refine ⟨hc, ?_⟩
  rw [hc]
  let R := rationalCoefficientSheaf l X E
  let S := (proEtaleSheafInverseImage (𝟙 X) CommRingCat.{u + 1}).obj R
  let c := (proEtaleRingInverseImageId X).hom.app R
  let F := proEtaleRingModulePullback (𝟙 X) R S (Iso.refl _)
  let adj := (proEtaleRingModuleAdjunction (𝟙 X) R S (Iso.refl _)).comp
    (pbcScalarAdjunction c)
  let e := ordinaryIdentityRight R
  let moduleId : rationalPullModule l E (𝟙 X) c ≅ 𝟭 _ := adj.leftAdjointIdIso e
  refine ⟨moduleId, ?_, ?_⟩
  · intro M V m b
    have h := congrArg (fun q ↦ q.val.app (op V) m)
      (unit_conjugateEquiv_symm Adjunction.id adj e.inv M).symm
    change (moduleId.hom.app M).val.app (op ((proEtaleBaseChange (𝟙 X)).obj V))
        (((pbcScalarAdjunction c).unit.app _).val.app
          (op ((proEtaleBaseChange (𝟙 X)).obj V))
          (((proEtaleRingModuleAdjunction (𝟙 X) R S (Iso.refl _)).unit.app M).val.app
            (op V) m)) = (e.inv.app M).val.app (op V) m at h
    rw [canonicalAdjunction_normalized (𝟙 X) R S (Iso.refl _)] at h
    rw [show ((pbcScalarAdjunction c).unit.app _).val.app
        (op ((proEtaleBaseChange (𝟙 X)).obj V)) _ = _ from
      (pbcScalarAdjunction_exists c).exists.choose_spec _ _ _] at h
    rw [ordinaryIdentityRight_inv R M V m] at h
    exact (((moduleId.hom.app M).val.app _).hom.map_smul b _).trans (congrArg (b • ·) h)
  · have hExact := rationalPullExtendExact c
    let := hExact.1
    let := hExact.2
    let ε : DerivedCategory.Q ⋙ rationalPullDerived l E (𝟙 X) c ≅
        (rationalPullModule l E (𝟙 X) c).mapHomologicalComplex (.up ℤ) ⋙
          DerivedCategory.Q :=
      isoWhiskerRight (proEtaleRingDerivedPullbackFactors (𝟙 X) R S (Iso.refl _))
          (pbcDerivedExtend c) ≪≫
        isoWhiskerLeft (F.mapHomologicalComplex (.up ℤ)) (rationalPullScalarFactors c)
    let ec := NatIso.mapHomologicalComplex moduleId (.up ℤ) ≪≫
      Functor.mapHomologicalComplexIdIso _ (.up ℤ)
    obtain ⟨d, hd⟩ := rationalPullDescendIso (rationalPullDerived l E (𝟙 X) c) (𝟭 _)
      _ _ ε (Functor.rightUnitor DerivedCategory.Q)
      (isoWhiskerRight ec DerivedCategory.Q ≪≫ Functor.leftUnitor DerivedCategory.Q)
    refine ⟨d, fun P ↦ ?_⟩
    have hε : ε.hom.app P = rationalPullComplexCounit l E (𝟙 X) c P := by rfl
    change d.hom.app (DerivedCategory.Q.obj P) =
      ε.hom.app P ≫ DerivedCategory.Q.map (ec.hom.app P)
    have h := hd P
    change d.hom.app (DerivedCategory.Q.obj P) ≫ 𝟙 _ =
      ε.hom.app P ≫ DerivedCategory.Q.map (ec.hom.app P) ≫ 𝟙 _ at h
    simpa only [Category.comp_id] using h

end AlgebraicGeometry.Scheme
