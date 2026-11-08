/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Submission.WeilConjectures.AlgebraicGeometry.GlobalDerivedHom
public import Submission.WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Adjunction.Basic
import Submission.WeilConjectures.AlgebraicGeometry.DerivedCategory
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Submission.WeilConjectures.CategoryTheory.DerivedModuleDirectSums
import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Submission.WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Additive
import Submission.WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Submission.WeilConjectures.AlgebraicGeometry.QcqsCohomologyDirectSum
import Submission.WeilConjectures.Topology.OpenModuleCohomology
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Submission.WeilConjectures.AlgebraicGeometry.HigherDirectImagePresheaf
import Submission.WeilConjectures.AlgebraicGeometry.OpenRestrictionModuleCohomology
import Submission.WeilConjectures.AlgebraicGeometry.HigherDirectImageResolutionNaturality
import Mathlib.Topology.Sheaves.SheafCondition.Sites
import Mathlib.AlgebraicGeometry.AffineScheme
import Submission.WeilConjectures.AlgebraicGeometry.PQFCohomology
import Submission.WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Submission.WeilConjectures.CategoryTheory.Filtration
import Submission.WeilConjectures.CategoryTheory.CanonicalFiltration
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
import Submission.WeilConjectures.CategoryTheory.DerivedCoupleFunctoriality
import Submission.WeilConjectures.CategoryTheory.TruncationCouple
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import Submission.WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Submission.WeilConjectures.CategoryTheory.ExactCoupleConvergence
import Submission.WeilConjectures.CategoryTheory.RightDerivedFunctorTruncationIso
import Submission.WeilConjectures.CategoryTheory.TruncationTriangle
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
import Submission.WeilConjectures.CategoryTheory.PBCFiltration
import Submission.WeilConjectures.AlgebraicGeometry.Cohomology.QuasicoherentExtension
import Submission.WeilConjectures.AlgebraicGeometry.Ample
import Submission.WeilConjectures.CategoryTheory.ImageFiltration
import Submission.WeilConjectures.CategoryTheory.HalfPlaneConvergence
import Mathlib.Data.Int.Interval
import Submission.WeilConjectures.Mathlib.CategoryTheory.Subobject.Limits
import Submission.WeilConjectures.CategoryTheory.HalfPlaneDiagonalColimits
import Submission.WeilConjectures.CategoryTheory.HalfPlaneWeakConvergence
import Submission.WeilConjectures.CategoryTheory.DerivedCoupleExact
import Submission.WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import Submission.WeilConjectures.AlgebraicGeometry.OrdinaryHigherImageQuasiCoherent
import Submission.WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Submission.WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.AlgebraicGeometry.Restrict
import Submission.WeilConjectures.Algebra.Homology.KInjectiveRestrictOpen
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful
import Submission.WeilConjectures.AlgebraicGeometry.LocalUniformHigherDirectImageBound
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Submission.WeilConjectures.AlgebraicGeometry.LerayDegenerateSections
import Submission.WeilConjectures.AlgebraicGeometry.OpenModuleCohomologyComparison
import Submission.WeilConjectures.AlgebraicGeometry.ModuleCohomologySourceComparison
import Submission.WeilConjectures.Topology.RingedSpaceModuleCohomology
import Submission.WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections
import Submission.WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Cech
import Submission.WeilConjectures.AlgebraicGeometry.HigherDirectImageOpenRestriction
import Submission.WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import Submission.WeilConjectures.Topology.OpenModuleDerivedSections
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Submission.WeilConjectures.AlgebraicGeometry.UnboundedDerivedFunctorCohomologicalBound
import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Submission.WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Submission.WeilConjectures.CategoryTheory.CompactlyGenerated
import Mathlib.CategoryTheory.Triangulated.Subcategory
import Mathlib.Topology.QuasiSeparated
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Mathlib.CategoryTheory.ObjectProperty.Retract
import Submission.WeilConjectures.AlgebraicGeometry.PerfectAffineClassesSmall
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.CategoryTheory.Skeletal
import Mathlib.Logic.Small.Basic
import Submission.WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Submission.WeilConjectures.AlgebraicGeometry.InjectiveRestrictionSurjective
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Mathlib.CategoryTheory.Abelian.CommSq
import Mathlib.Algebra.Homology.HomologicalComplexBiprod
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import Submission.WeilConjectures.AlgebraicGeometry.QuasiCompactOpenInduction
import Mathlib.CategoryTheory.Limits.FullSubcategory
import Submission.WeilConjectures.CategoryTheory.CompactObject
import Mathlib.Algebra.Homology.Localization
import Submission.WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
import Mathlib.Algebra.Homology.HomotopyCategory
import Mathlib.Algebra.Homology.Single
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
import Mathlib.Algebra.DirectSum.Basic
import Submission.WeilConjectures.AlgebraicGeometry.AffineQCohDerivedEquivalence
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import Mathlib.Algebra.Category.ModuleCat.AB
import Submission.WeilConjectures.Algebra.Homology.KFlatResolution
import Submission.WeilConjectures.Algebra.Homology.KFlat
import Submission.WeilConjectures.Algebra.Homology.KFlatPullback
import Submission.WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Submission.WeilConjectures.Algebra.Homology.DerivedChangeOfRings
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Submission.WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import Mathlib.CategoryTheory.Adjunction.Additive
import Submission.WeilConjectures.AlgebraicGeometry.InverseImageTensorPullbackComparison
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
import Submission.WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import Submission.WeilConjectures.AlgebraicGeometry.RingedSpaceTensorPullbackUnderived
import Submission.WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Submission.WeilConjectures.Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Submission.WeilConjectures.AlgebraicGeometry.DerivedPullback
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Submission.WeilConjectures.AlgebraicGeometry.AffineQCohDerivedEquivalenceCore
import Submission.WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
import Submission.WeilConjectures.AlgebraicGeometry.Modules.PullbackTilde
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Submission.WeilConjectures.Algebra.Homology.KFlatStalkCriterion
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.CategoryTheory.Whiskering
import Submission.WeilConjectures.Algebra.Homology.ModuleStalkFunctor
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Submission.WeilConjectures.Mathlib.Algebra.Homology.Bifunctor
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import Submission.WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
import Submission.WeilConjectures.AlgebraicGeometry.Modules.AffineTildeTensor
import Submission.WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorProduct
import Submission.WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorComparisonDescent
import Submission.WeilConjectures.AlgebraicGeometry.TensorPullback
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Submission.WeilConjectures.AlgebraicGeometry.Modules.PullbackMonoidal
import Submission.WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import Submission.WeilConjectures.AlgebraicGeometry.AffineDerivedTildeHomologyComparison
import Mathlib.CategoryTheory.Preadditive.LeftExact
import Submission.WeilConjectures.Algebra.Homology.KFlatModuleBaseChange
import Mathlib.Algebra.Homology.Additive
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Submission.WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk
import Submission.WeilConjectures.FromJoel.CategoryTheory.Monoidal.Functor
import Submission.WeilConjectures.AlgebraicGeometry.Modules.RestrictionTensorComparison
import Submission.WeilConjectures.AlgebraicGeometry.DerivedPullbackMonoidalModel
import Submission.WeilConjectures.Algebra.Homology.DerivedInternalHom
import Mathlib.CategoryTheory.Yoneda
import Submission.WeilConjectures.Algebra.Homology.HomComplex
import Submission.WeilConjectures.Algebra.Homology.HomComplexProjections
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHomOver
import Submission.WeilConjectures.Algebra.Homology.InternalHomOverNaturality
import Mathlib.CategoryTheory.MorphismProperty.Retract
import Submission.WeilConjectures.RingTheory.FiniteProjectivePrimeLocalFree
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FiniteFreeInternalHomExact
import Submission.WeilConjectures.Algebra.Homology.BoundedExactTermHomQuasiIso
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHomFree
import Submission.WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentCokernel
import Mathlib.Algebra.Homology.BifunctorShift
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import Submission.WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalFree
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Submission.WeilConjectures.FromJoel.Algebra.Homology.BicomplexColumns
import Mathlib.CategoryTheory.Localization.Monoidal.Functor
import Submission.WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Adjunction.Limits
import Submission.WeilConjectures.Algebra.Homology.OpenRestrictionAdjunctionExact
import Submission.WeilConjectures.Algebra.Homology.ModuleExtensionByZeroUnitIsIso
import Mathlib.CategoryTheory.Monad.Adjunction
import Submission.WeilConjectures.Algebra.Homology.OpenExtensionCounitStalk
import Submission.WeilConjectures.Algebra.Homology.StalkTensorComplex
import Submission.WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Submission.WeilConjectures.AlgebraicGeometry.CanonicalPullbackTensorComparison
import Mathlib.CategoryTheory.Linear.LinearFunctor
import Submission.WeilConjectures.AlgebraicGeometry.InternalHomOverEquiv
import Mathlib.Algebra.Category.ModuleCat.Presheaf.PushforwardZeroMonoidal
import Mathlib.CategoryTheory.Adjunction.Restrict
import Submission.WeilConjectures.AlgebraicGeometry.OpenModuleContractionTransport
import Submission.WeilConjectures.AlgebraicGeometry.CanonicalDerivedTensorHomModel
import Submission.WeilConjectures.CategoryTheory.Monoidal.Closed.Preadditive
import Submission.WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Submission.WeilConjectures.Topology.SheafIsomorphismLocalOpenCover
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import Submission.WeilConjectures.Algebra.Homology.BoundedAboveFlatRingedSpaceKFlat
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Submission.WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence
import Submission.WeilConjectures.Algebra.Homology.ModuleExtensionByZeroStalkOutside
import Mathlib.Topology.Sheaves.Module
import Submission.WeilConjectures.Algebra.Homology.ModuleRestrictionStalkComponents
import Mathlib.Geometry.RingedSpace.Stalks
import Mathlib.CategoryTheory.Localization.LocallySmall
import Submission.WeilConjectures.CategoryTheory.WeakTriangulatedGenerator
import Mathlib.CategoryTheory.Triangulated.Orthogonal
import Mathlib.CategoryTheory.Triangulated.Functor
import Mathlib.CategoryTheory.EssentiallySmall
import Submission.WeilConjectures.CategoryTheory.BrownCohomologicalRepresentability
import Submission.WeilConjectures.CategoryTheory.TriangulatedEquivalenceTransfer
import Submission.WeilConjectures.CategoryTheory.CompactGenerationEquivalence
import Mathlib.CategoryTheory.Adjunction.PartialAdjoint
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import Submission.WeilConjectures.AlgebraicGeometry.SchemeDerivedBaseChangeMap
public import Submission.WeilConjectures.AlgebraicGeometry.CanonicalDerivedTensorHom
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.CategoryTheory.Localization.Adjunction
import Submission.WeilConjectures.AlgebraicGeometry.KFlatBifunctorIsoDescent
import Mathlib.CategoryTheory.Localization.Prod
import Mathlib.CategoryTheory.Localization.Equivalence
import Submission.WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineMorphism
import Submission.WeilConjectures.AlgebraicGeometry.DerivedAdjoint
import Mathlib.CategoryTheory.Adjunction.Mates
import Submission.WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import Mathlib.CategoryTheory.Retract
import Mathlib.CategoryTheory.Triangulated.Yoneda
import Mathlib.CategoryTheory.Triangulated.Adjunction
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Abelian.Exact
import Submission.WeilConjectures.Algebra.Homology.LargeFilteredFreeResolution
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Submission.WeilConjectures.AlgebraicGeometry.CanonicalPullbackTensorMonoidalRealization
import Mathlib.CategoryTheory.Monoidal.Category

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
Canonical adjunction and tensor data are pinned by their characterising equations.
 # Canonical global Hom adjunction
Source: Stacks Project, duality.tex, Tag 0B6I (lemma-iso-global-hom).
(blueprint: lem-pc-global-hom-adjunction).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w wA vC vD vE vB uC uD uE uB
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  Opposite TopologicalSpace
noncomputable section
namespace AlgebraicGeometry
section InternalHomMate
variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  [MonoidalCategory C] [MonoidalCategory D]
variable (H : Cᵒᵖ × C ⥤ C) (J : Dᵒᵖ × D ⥤ D)
  (F : D ⥤ C) (R : C ⥤ D) (p : F ⊣ R)
  (t : tensor D ⋙ F ≅ F.prod F ⋙ tensor C)
  (ex : ∀ A L M : C, (A ⟶ H.obj (op L, M)) ≃ (A ⊗ L ⟶ M))
  (ey : ∀ A L M : D, (A ⟶ J.obj (op L, M)) ≃ (A ⊗ L ⟶ M))
  (hx : ∀ (A A' L L' M M' : C) (a : A' ⟶ A) (b : L' ⟶ L) (d : M ⟶ M')
    (g : A ⟶ H.obj (op L, M)),
    ex A' L' M' (a ≫ g ≫ H.map (b.op, d)) = (a ⊗ₘ b) ≫ ex A L M g ≫ d)
  (hy : ∀ (A A' L L' M M' : D) (a : A' ⟶ A) (b : L' ⟶ L) (d : M ⟶ M')
    (g : A ⟶ J.obj (op L, M)),
    ey A' L' M' (a ≫ g ≫ J.map (b.op, d)) = (a ⊗ₘ b) ≫ ey A L M g ≫ d)
end InternalHomMate

section TensorHomAdjunction
variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C]
  (H : Cᵒᵖ × C ⥤ C)
  (e : ∀ A L M : C, (A ⟶ H.obj (op L, M)) ≃ (A ⊗ L ⟶ M))
  (h : ∀ (A A' L L' M M' : C) (a : A' ⟶ A) (b : L' ⟶ L) (d : M ⟶ M')
    (g : A ⟶ H.obj (op L, M)),
    e A' L' M' (a ≫ g ≫ H.map (b.op, d)) = (a ⊗ₘ b) ≫ e A L M g ≫ d)
end TensorHomAdjunction


section LerayNaturality
variable {C : Type uC} {D : Type uD} {E : Type uE} {B : Type uB}
  [Category.{vC} C] [Category.{vD} D] [Category.{vE} E] [Category.{vB} B]
  (R : C ⥤ D) (G : D ⥤ E) (GX : C ⥤ B) (S : B ⥤ E)
  (e : R ⋙ G ≅ GX ⋙ S)

end LerayNaturality


/-- Exact restriction along the map on global functions.
Source: Stacks, Tag 0B6I (blueprint: lem-pc-global-hom-adjunction). -/
def schemeGlobalScalarRestriction
    [∀ (R : Type u) [Ring R], HasDerivedCategory.{w} (ModuleCat.{u} R)]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (ModuleCat.restrictScalars.{u}
    (R := (moduleRings Y.toRingedSpace).obj.obj (op ⊤))
    (S := (moduleRings X.toRingedSpace).obj.obj (op ⊤)) f.appTop.hom).mapDerivedCategory

variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
variable [∀ (R : Type u) [Ring R], HasDerivedCategory.{w} (ModuleCat.{u} R)]


set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The same pinned derived adjunction as the canonical base-change map.
Source: Stacks, Tags 079W and 0B6I (blueprint: lem-pc-global-hom-adjunction). -/
def schemeHomPullbackAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y) :
    derivedPullback f ⊣ schemeDerivedDirectImage f :=
  Classical.choose (exists_schemeDerivedAdjunction f
    (hAdd := (Classical.choose exists_derivedPullbackComposition) f)
    ((Classical.choose (Classical.choose_spec exists_derivedPullbackComposition)) f)
    ((Classical.choose (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition))) f))

omit [∀ (R : Type u) [Ring R], HasDerivedCategory.{w} (ModuleCat.{u} R)] in
/-- The canonical pullback tensor comparison with independent localization universes.
Proof: take the canonical comparison normalized to SingleComplexBaseChange.counit.
On K-flat representatives, tensor, pullback, localization tensor maps and the shared
left-derived counits are invertible. The canonical coordinate equation thus makes
its components invertible. K-flat resolutions and naturality transport invertibility
to arbitrary objects. Package these components as a natural isomorphism.
Source: Stacks Tags 079U and 0B6I
(blueprint: lem-sc-mixed-hom-tensor-pullback-iso). -/
theorem exists_mixedHomTensorPullbackIso {T S : Scheme.{u}} (h : T ⟶ S) :
    ∃ t : tensor (schemeDerivedCategory S) ⋙ derivedPullback h ≅
      (derivedPullback h).prod (derivedPullback h) ⋙ tensor (schemeDerivedCategory T),
      IsCanonicalPullbackTensorComparison h (fun K L ↦ t.hom.app (K, L)) := by
  obtain ⟨τ, hτ⟩ := exists_canonicalPullbackTensorComparison h
  let c : tensor (schemeDerivedCategory S) ⋙ derivedPullback h ⟶
      (derivedPullback h).prod (derivedPullback h) ⋙ tensor (schemeDerivedCategory T) :=
    { app := fun Z ↦ τ Z.1 Z.2
      naturality := fun Z Z' a ↦ hτ.2 Z.1 Z'.1 Z.2 Z'.2 a.1 a.2 }
  obtain ⟨m, hm⟩ := canonicalPullbackTensor_monoidal_realization h τ hτ
  have (Z : schemeDerivedCategory S × schemeDerivedCategory S) : IsIso (c.app Z) := by
    change IsIso (τ Z.1 Z.2)
    rw [← hm Z.1 Z.2]
    infer_instance
  exact ⟨NatIso.ofComponents (fun Z ↦ asIso (c.app Z))
    (fun a ↦ c.naturality a), hτ⟩

omit [∀ (R : Type u) [Ring R], HasDerivedCategory.{w} (ModuleCat.{u} R)] in
/-- The pullback tensorator normalized to the shared derived counit.
Source: Stacks Tag 079U. -/
def mixedHomTensorPullbackIso {T S : Scheme.{u}} (h : T ⟶ S) :
    tensor (schemeDerivedCategory S) ⋙ derivedPullback h ≅
      (derivedPullback h).prod (derivedPullback h) ⋙ tensor (schemeDerivedCategory T) :=
  Classical.choose (exists_mixedHomTensorPullbackIso h)

attribute [local irreducible] schemeHomPullbackAdjunction mixedHomTensorPullbackIso


end AlgebraicGeometry
