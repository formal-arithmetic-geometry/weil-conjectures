/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ModuleRingedComparison.ResolvingOplaxConstraints.SectionResolvingOplaxConstraintData
import WeilConjectures.Algebra.Homology.KFlatTotalTensorModel.KFlatTotalTensorModelSupplement
import WeilConjectures.AlgebraicGeometry.SectionModuleAlgebraicInverseImage
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.CategoryTheory.Monoidal.Mod.Tensor
import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
import WeilConjectures.CategoryTheory.RingObjects.Ab
import WeilConjectures.CategoryTheory.Sites.MonObj
import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Types.Basic
import WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal
import WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import Mathlib.Algebra.Category.Grp.FilteredColimits
import all WeilConjectures.Algebra.Homology.AlgebraicInverseImageKFlat
import all WeilConjectures.Algebra.Homology.RingedSiteKFlatStalkCriterion
import all WeilConjectures.CategoryTheory.Sites.RingedSitePoint
import all WeilConjectures.CategoryTheory.Sites.GeometricMorphism
import all Mathlib.CategoryTheory.Adjunction.Mates
import all Mathlib.CategoryTheory.Adjunction.Limits
import all Mathlib.CategoryTheory.Limits.Preserves.Finite
import all WeilConjectures.CategoryTheory.Grothendieck.GrothendieckTopos
import all WeilConjectures.CategoryTheory.SiteCoveringAxioms
import all Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import all Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Basic
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Functor.ReflectsIso.Jointly
import all WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.Algebra.Homology.HomologicalComplex
import all Mathlib.Algebra.Homology.Additive
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
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
import all WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import all WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.CategoryTheory.Limits.Preserves.Limits
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
import all WeilConjectures.Algebra.Homology.RingedSitePointUniversalTensor
import all Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
import all Mathlib.Algebra.Module.FinitePresentation
import all WeilConjectures.Algebra.Homology.RingedSitePointTensor
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.CategoryTheory.AdjunctionRingOperations
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import all Mathlib.CategoryTheory.Adjunction.Basic
import all WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all WeilConjectures.CategoryTheory.RingedToposRingData
import all WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.CategoryTheory.GeometricModuleTransport
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all Mathlib.Algebra.Homology.Bifunctor
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import all Mathlib.CategoryTheory.PUnit
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainModuleAdjunction
import all WeilConjectures.SecSmoothPurity.CochainTensoratorExistence
import all WeilConjectures.Mathlib.Algebra.Homology.Bifunctor
import all WeilConjectures.Algebra.Homology.RingedSitePointExact
import all Mathlib.CategoryTheory.Abelian.Exact
import all Mathlib.CategoryTheory.Sites.EpiMono
import all Mathlib.Algebra.Category.ModuleCat.Abelian
import all Mathlib.CategoryTheory.Sites.LocallySurjective
import all WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import all WeilConjectures.Algebra.Homology.RingedSitePointFinitePresentationRetract
import all Mathlib.CategoryTheory.Retract
import all WeilConjectures.CategoryTheory.Sites.InverseImageFreeModule
import all WeilConjectures.CategoryTheory.Sites.FreeModuleSheafConstruction
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.CategoryTheory.Sites.LeftExact
import all WeilConjectures.CategoryTheory.Sites.FreeModuleUniversalProperty
import all Mathlib.LinearAlgebra.FreeModule.Basic
import all WeilConjectures.CategoryTheory.Sites.GeometricFreeModuleHomEquivalence
import all WeilConjectures.CategoryTheory.Sites.NormalizedFreeModuleComparison
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import all Mathlib.Algebra.Category.ModuleCat.Kernels
import all Mathlib.LinearAlgebra.Finsupp.Pi
import all WeilConjectures.Algebra.Homology.RingedSitePointKFlatResolution
import all WeilConjectures.Algebra.Homology.RingedSitePointFlat
import all Mathlib.RingTheory.Flat.Basic
import all WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
import all Mathlib.Algebra.Category.ModuleCat.AB
import all WeilConjectures.Algebra.Homology.RingedSitePointAcyclic
import all WeilConjectures.Algebra.Homology.UniversalAcyclicModuleKFlat
import all Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all WeilConjectures.Algebra.ModuleDirectedColimitFinitePresentation
import all Mathlib.Algebra.Module.ULift
import all Mathlib.CategoryTheory.Category.Preorder
import all Mathlib.CategoryTheory.Limits.HasLimits
import all Mathlib.LinearAlgebra.Finsupp.LinearCombination
import all Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
import all WeilConjectures.FromJoel.Algebra.Homology.Embedding.CochainComplexTrunc
import all Mathlib.CategoryTheory.Monoidal.Closed.Braided
import all WeilConjectures.Algebra.Homology.PullbackTensorResolving.PullbackTensorResolvingComputation
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import Mathlib.CategoryTheory.Monoidal.Ring
import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch

/-! # Resolving closure for nested section tensors

Source: Stacks Project, sites-cohomology.tex, Tags 07A4 and 0G7E;
the resolving-closure part of `lem-pd-section-resolving-oplax-model-edges`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.ModuleRingedComparison
namespace ResolvingOplaxConstraints

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ T)]

private theorem resolving_tensor (T : Scheme.{u})
    (P Q : CochainComplex (modules Λ T) ℤ)
    (hP : KFlatSectionComparison.sectionResolving Λ T P)
    (hQ : KFlatSectionComparison.sectionResolving Λ T Q) :
    KFlatSectionComparison.sectionResolving Λ T (P ⊗ Q) := by
  have h := SheafOfModules.KFlatTotalTensorModel.kFlat_total_tensor_model
    (ring Λ T) P Q hP.1 hQ.1 hP.2 hQ.2
  exact ⟨h.1, h.2.1⟩

omit [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ T)] in
private theorem resolving_iso (T : Scheme.{u})
    {P Q : CochainComplex (modules Λ T) ℤ} (e : P ≅ Q)
    (hP : KFlatSectionComparison.sectionResolving Λ T P) :
    KFlatSectionComparison.sectionResolving Λ T Q := by
  refine ⟨?_, ?_⟩
  · intro A hA n
    exact (hP.1 A hA n).of_iso
      (((curriedTensor (modules Λ T)).map₂CochainComplex.obj A).mapIso e)
  · intro n
    exact (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso (ring Λ T) (P.X n) ≪≫
        (curriedTensor (modules Λ T)).flip.mapIso
          ((HomologicalComplex.eval _ _ n).mapIso e) ≪≫
        (SheafOfModules.siteSheafTensorRightIso (ring Λ T) (Q.X n)).symm) (hP.2 n)

private theorem resolving_pullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : CochainComplex (modules Λ Y) ℤ)
    (hP : KFlatSectionComparison.sectionResolving Λ Y P) :
    KFlatSectionComparison.sectionResolving Λ X ((totalSectionPull Λ f).obj P) := by
  classical
  let L := Scheme.proEtaleSheafInverseImage f (Type (u + 1))
  let V := Scheme.proEtaleSheafDirectImage f (Type (u + 1))
  let adj : L ⊣ V := Scheme.proEtaleSheafAdjunction f (Type (u + 1))
  have : PreservesFiniteLimits L := by
    have : PreservesFiniteLimits
        ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).op.lan :
          (Y.ProEtᵒᵖ ⥤ Type (u + 1)) ⥤ X.ProEtᵒᵖ ⥤ Type (u + 1)) := by
      let : AB5OfSize.{u, u + 1} (Type (u + 1)) :=
        AB5OfSize_shrink.{u, u + 1, u + 1, u + 1} (Type (u + 1))
      apply preservesFiniteLimits_op_lan_of_flat
    unfold L Scheme.proEtaleSheafInverseImage
      Functor.sheafPullbackConstruction.sheafPullback
    infer_instance
  let geom : GeometricMorphism
      (Sheaf (Scheme.ProEt.topology X) (Type (u + 1)))
      (Sheaf (Scheme.ProEt.topology Y) (Type (u + 1))) :=
    { inverse := L, direct := V, adj := adj, leftExact := inferInstance }
  obtain ⟨I, ⟨θ⟩⟩ := exists_sectionModuleAlgebraicInverseImage f
    (condensedRingObj Λ Y) (condensedRingObj Λ X) (inv (condensedPullbackHom Λ f))
  let c : CondensedRing.upperStar Λ f ≅
      Mod.mapModComap (inv (condensedPullbackHom Λ f)) :=
    Functor.isoWhiskerLeft _ (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ f))
  let e : I.modules ≅ pullback Λ f :=
    θ.symm ≪≫ Functor.isoWhiskerLeft (equivalence Λ Y).inverse
      (Functor.isoWhiskerRight c.symm (equivalence Λ X).functor ≪≫ pullComparison Λ f) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (equivalence Λ Y).counitIso (pullback Λ f) ≪≫
    Functor.leftUnitor _
  have : (equivalence Λ Y).functor.Additive := sectionFunctorAdditive Λ Y
  have : (equivalence Λ X).functor.Additive := sectionFunctorAdditive Λ X
  have : I.modules.Additive := Functor.additive_of_iso θ
  have : (pullback Λ f).Additive := Functor.additive_of_iso e
  let I₀ := SheafOfModules.unliftInverseImage geom I
  have : I₀.modules.Additive := ‹I.modules.Additive›
  have hk := SheafOfModules.PullbackTensorResolving.isKFlat_inverseImage
    L V adj I₀ P hP.1 hP.2
  have hf (n : ℤ) := SheafOfModules.isFlat_algebraicInverseImageOfUniverses.{u + 1, u,
    u + 1, u, u + 1, u + 1}
    L V adj I (P.X n) (hP.2 n)
  exact resolving_iso Λ X ((NatIso.mapHomologicalComplex e (.up ℤ)).app P) ⟨hk, hf⟩

/--
The four nested tensor totals of resolving section complexes, together with all
their pullbacks, are resolving.  This is the closure step in the explicit
representative calculation: apply the K-flat total-tensor model theorem to the
two binary pairs and then to the two outer pairs, and apply preservation of
K-flatness and flat terms by ringed-topos pullback.
Source: Stacks Project, sites-cohomology.tex, Tags 07A4 and 0G7E.
(blueprint: lem-pd-section-resolving-oplax-closure).
-/
theorem section_resolving_oplax_closure {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P Q H : CochainComplex (modules Λ Y) ℤ)
    (hP : KFlatSectionComparison.sectionResolving Λ Y P)
    (hQ : KFlatSectionComparison.sectionResolving Λ Y Q)
    (hH : KFlatSectionComparison.sectionResolving Λ Y H) :
    ResolvingClosure Λ f P Q H := by
  have hPQ := resolving_tensor Λ Y P Q hP hQ
  have hQH := resolving_tensor Λ Y Q H hQ hH
  have hPQH := resolving_tensor Λ Y (P ⊗ Q) H hPQ hH
  have hPQH' := resolving_tensor Λ Y P (Q ⊗ H) hP hQH
  constructor
  · intro A hA
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hA
    rcases hA with rfl | rfl | rfl | rfl
    · exact hPQ
    · exact hQH
    · exact hPQH
    · exact hPQH'
  · intro A hA
    apply resolving_pullback Λ f A
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hA
    rcases hA with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hP
    · exact hQ
    · exact hH
    · exact hPQ
    · exact hQH
    · exact hPQH
    · exact hPQH'

end ResolvingOplaxConstraints
end AlgebraicGeometry.ProEtale.ModuleRingedComparison
