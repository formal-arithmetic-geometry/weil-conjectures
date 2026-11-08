/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Additive
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleAffineAcyclicHypercover
import Submission.WeilConjectures.CategoryTheory.SimplicialMatchingObject
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleAffineAcyclicHypercoverGeometry
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleQcqsFiniteFamilyGeometry
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleQcqsSiteLimits
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleQcqsSubsite
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Sites.Finite
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Comma.Over.Basic
import Submission.WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation
import Mathlib.AlgebraicGeometry.Limits
import Submission.WeilConjectures.AlgebraicGeometry.FiniteCoproductLfpQcqs
import Submission.WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductSections
import Submission.WeilConjectures.CategoryTheory.SiteFiniteBasisHypercoverExistence
import Mathlib.CategoryTheory.Sites.Precoverage
import Mathlib.CategoryTheory.Limits.FormalCoproducts.Basic
import Submission.WeilConjectures.CategoryTheory.ProperFaceMatchingObject
import Submission.WeilConjectures.CategoryTheory.SiteFiniteBasisHypercoverStep
import Submission.WeilConjectures.AlgebraicGeometry.SiteHypercoverFiniteExtension
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import Submission.WeilConjectures.AlgebraicGeometry.SiteHypercoverFiniteExtensionBase
import Mathlib.AlgebraicTopology.SimplicialObject.Basic
import Mathlib.Basic.Finite.Sigma
import Submission.WeilConjectures.AlgebraicGeometry.SiteHypercoverFiniteExtensionConstruction
import Submission.WeilConjectures.AlgebraicGeometry.SiteHypercoverAttachmentComposition
import Submission.WeilConjectures.AlgebraicGeometry.SiteHypercoverAttachmentOperators
import Submission.WeilConjectures.AlgebraicGeometry.SiteHypercoverFiniteExtensionSplit
import Mathlib.Basic.Finite.Sum
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
import Mathlib.CategoryTheory.Limits.IsConnected
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.CategoryTheory.Sites.PreservesLimits
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleQcAffineContractibleCover
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleAffineAcyclicHypercoverWeak
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.BoundedBelowSectionModel
import Mathlib.Algebra.Homology.CochainComplexPlus
import Submission.WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
import Mathlib.Algebra.Homology.Embedding.Extend
import Submission.WeilConjectures.CategoryTheory.DoubleComplexTotal
import Submission.WeilConjectures.CategoryTheory.CanonicalFiltration
import Mathlib.CategoryTheory.Preadditive.FunctorCategory
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWeaklyContractibleEvaluationExact
import Submission.WeilConjectures.Algebra.Homology.BoundedBelowTotalComparison
import Mathlib.Algebra.Homology.TotalComplex
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.TotalComplexSymmetry
import Submission.WeilConjectures.FromJoel.Algebra.Homology.BicomplexColumns
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.SectionsConservative
import Submission.WeilConjectures.Algebra.Homology.BoundedBelowAugmentation
import Submission.WeilConjectures.CategoryTheory.RingedHypercoverInjectiveAugmentation
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.CategoryTheory.Sites.Subcanonical
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Algebra.Exact.Basic
import Mathlib.Algebra.Category.Ring.Limits
import Submission.WeilConjectures.CategoryTheory.RingedHypercoverInjectiveAugmentationRing
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Submission.WeilConjectures.CategoryTheory.RingedHypercoverFiniteCones
import Mathlib.CategoryTheory.Sites.Grothendieck
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.SingleHomology
import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleHypercoverLocalLifting
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleRepresentableEpiLocalLifting
import Submission.WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.Algebra.Homology.HomotopyCofiber
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleHypercoverComputesBoundedComplex
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleAbelianHypercoverQuasiIso
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleAbelianHypercoverTotal
import Mathlib.Algebra.Category.Grp.AB
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleAbelianEvaluationColimits
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.Algebra.Category.Grp.EpiMono
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Submission.WeilConjectures.Algebra.Homology.ComplexExtensionColimits
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleAbelianHypercoverRowComparison
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleAbelianHypercoverAugmentation
import Submission.WeilConjectures.AlgebraicGeometry.CondensedHypercoverInjectiveRow
import Submission.WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
import Submission.WeilConjectures.CategoryTheory.RingObjects.Ab
import Submission.WeilConjectures.CategoryTheory.Sites.MonObj
import Submission.WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Submission.WeilConjectures.AlgebraicGeometry.CondensedQcqsPushforwardLocalComparison
import Submission.WeilConjectures.AlgebraicGeometry.CondensedHypercoverComparison
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Sites.Sheafification
import Submission.WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Ring
import Mathlib.CategoryTheory.Adjunction.Limits
import Submission.WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjectiveResolution
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Submission.WeilConjectures.AlgebraicGeometry.CondensedQcqsPushforwardContinuity
import Submission.WeilConjectures.Mathlib.CategoryTheory.Preadditive.LiftToFinset
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.HomologyCoproducts
import Submission.WeilConjectures.CategoryTheory.GrothendieckDerivedCoproducts
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Submission.WeilConjectures.CategoryTheory.DerivedModuleDirectSums

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Coproduct continuity with a common lower cohomology bound

Source: Hemo--Richarz--Scholbach, Lemma 5.3(1), and the finite-partial-sum construction.
(blueprint: lem-sfb-adic-proper-bounded-below-coproducts)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace CategoryTheory.Limits

open CoproductsFromFiniteFiltered

-- The finite-partial-sum argument needs preservation only for this one diagram.
private theorem preservesCoproduct_of_finitePartialSums
    {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
    [HasFiniteCoproducts C] {I : Type*} (f : I → C) [HasCoproduct f]
    [HasColimitsOfShape (Finset (Discrete I)) C]
    (F : C ⥤ D) [F.Additive]
    [PreservesColimit (liftToFinsetObj (Discrete.functor f)) F] :
    PreservesColimit (Discrete.functor f) F := by
  refine preservesColimit_of_preserves_colimit_cocone (coproductIsCoproduct f) ?_
  have hc := isColimitOfPreserves F (isColimitFiniteSubproductsCocone f)
  -- the finite subcoproducts are preserved by the additive functor `F`
  have hS (S : Finset (Discrete I)) : IsColimit (Cofan.mk
      (F.obj (∐ fun x : S ↦ f x.1.as)) fun a ↦ F.map (Sigma.ι (fun x : S ↦ f x.1.as) a)) :=
    (isColimitMapCoconeCofanMkEquiv F _ _).1 (isColimitOfPreserves F (coproductIsCoproduct _))
  let ι (s : Cofan fun a ↦ F.obj (f a)) (S : Finset (Discrete I)) :
      F.obj (∐ fun x : S ↦ f x.1.as) ⟶ s.pt :=
    (hS S).desc (Cofan.mk s.pt fun a ↦ s.inj a.1.as)
  have hι (s : Cofan fun a ↦ F.obj (f a)) (S : Finset (Discrete I)) (a : S) :
      F.map (Sigma.ι (fun x : S ↦ f x.1.as) a) ≫ ι s S = s.inj a.1.as :=
    (hS S).fac (Cofan.mk s.pt fun a ↦ s.inj a.1.as) ⟨a⟩
  let t (s : Cofan fun a ↦ F.obj (f a)) :
      Cocone (liftToFinsetObj (Discrete.functor f) ⋙ F) :=
    { pt := s.pt
      ι :=
        { app := ι s
          naturality := fun S T h ↦ by
            refine Cofan.IsColimit.hom_ext (hS S) _ _ fun a ↦ ?_
            dsimp
            rw [Category.comp_id, hι, ← F.map_comp_assoc, liftToFinsetObj_map]
            erw [colimit.ι_desc]
            exact hι s T ⟨a.1, h.down.down a.2⟩ } }
  have hfac (s : Cofan fun a ↦ F.obj (f a)) (a : I) :
      F.map (Sigma.ι f a) = F.map (Sigma.ι (fun x : ({⟨a⟩} : Finset (Discrete I)) ↦ f x.1.as)
        ⟨⟨a⟩, by simp⟩) ≫ F.map ((finiteSubcoproductsCocone f).ι.app {⟨a⟩}) := by
    rw [← F.map_comp, finiteSubcoproductsCocone_ι_app]
    erw [colimit.ι_desc]
    rfl
  refine (isColimitMapCoconeCofanMkEquiv F f (Sigma.ι f)).2
    (Cofan.IsColimit.mk _ (fun s ↦ hc.desc (t s)) (fun s a ↦ ?_) (fun s m hm ↦ ?_))
  · dsimp
    rw [hfac s a, Category.assoc]
    erw [hc.fac (t s) {⟨a⟩}]
    exact hι s _ _
  · refine hc.hom_ext fun S ↦ ?_
    erw [hc.fac (t s) S]
    refine Cofan.IsColimit.hom_ext (hS S) _ _ fun a ↦ ?_
    dsimp
    rw [hι, ← F.map_comp_assoc, finiteSubcoproductsCocone_ι_app]
    erw [colimit.ι_desc]
    exact hm a.1.as

private theorem isStrictlyGE_finitePartialSums
    {C : Type*} [Category* C] [Abelian C]
    {I : Type*} (E : I → CochainComplex C ℤ) (N : ℤ)
    (hE : ∀ i, (E i).IsStrictlyGE N) (s : Finset (Discrete I)) :
    ((liftToFinsetObj (Discrete.functor E)).obj s).IsStrictlyGE N := by
  have : ∀ i, (E i).IsStrictlyGE N := hE
  rw [CochainComplex.isStrictlyGE_iff]
  intro n hn
  exact (isColimitOfPreserves (HomologicalComplex.eval C (.up ℤ) n)
    (coproductIsCoproduct (fun x : s ↦ E x.1.as))).isZero_pt
      (Functor.isZero _ fun x ↦ (E x.as.1.as).isZero_of_isStrictlyGE N n hn)

private theorem hasColimitsOfShape_cochainComplex
    {C J : Type*} [Category* C] [Category* J] [HasZeroMorphisms C]
    [HasColimitsOfShape J C] : HasColimitsOfShape J (CochainComplex C ℤ) := by
  refine ⟨fun E ↦ ?_⟩
  have (n : ℤ) : HasColimit (E ⋙ HomologicalComplex.eval C (.up ℤ) n) :=
    HasColimitsOfShape.has_colimit _
  exact ⟨⟨⟨_, HomologicalComplex.isColimitCoconeOfHasColimitEval E⟩⟩⟩

private theorem preservesCoproduct_of_boundedBelow_continuity
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions D]
    {I : Type*} [HasColimitsOfShape (Discrete I) C]
    [HasColimitsOfShape (Discrete I) D] [HasExactColimitsOfShape (Discrete I) D]
    [HasColimitsOfShape (Finset (Discrete I)) C]
    (F : DerivedCategory C ⥤ DerivedCategory D) [F.Additive]
    (N : ℤ) (K : I → DerivedCategory C) (hN : ∀ i, (K i).IsGE N)
    (hcont : ∀ E : Finset (Discrete I) ⥤ CochainComplex C ℤ,
      (∀ s, (E.obj s).IsStrictlyGE N) → ∀ q : ℤ,
      PreservesColimit E (DerivedCategory.Q ⋙ F ⋙ DerivedCategory.homologyFunctor D q)) :
    PreservesColimit (Discrete.functor K) F := by
  classical
  have : HasColimitsOfShape (Discrete I) (CochainComplex C ℤ) :=
    hasColimitsOfShape_cochainComplex
  have : HasColimitsOfShape (Finset (Discrete I)) (CochainComplex C ℤ) :=
    hasColimitsOfShape_cochainComplex
  have : HasColimitsOfShape (Discrete I) (DerivedCategory C) :=
    DerivedCategory.hasColimitsOfShape_discrete I
  have : HasColimitsOfShape (Discrete I) (DerivedCategory D) :=
    DerivedCategory.hasColimitsOfShape_discrete I
  have representatives (i : I) : ∃ E : CochainComplex C ℤ,
      E.IsStrictlyGE N ∧ Nonempty (DerivedCategory.Q.obj E ≅ K i) := by
    have : (K i).IsGE N := hN i
    obtain ⟨E, hE, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isGE (K i) N
    exact ⟨E, hE, ⟨e.symm⟩⟩
  choose E hE he using representatives
  let S := CoproductsFromFiniteFiltered.liftToFinsetObj (Discrete.functor E)
  have hS (s : Finset (Discrete I)) : (S.obj s).IsStrictlyGE N :=
    isStrictlyGE_finitePartialSums E N hE s
  have hT (q : ℤ) : PreservesColimit (Discrete.functor E)
      (DerivedCategory.Q ⋙ F ⋙ DerivedCategory.homologyFunctor D q) := by
    have : PreservesColimit S
        (DerivedCategory.Q ⋙ F ⋙ DerivedCategory.homologyFunctor D q) := hcont S hS q
    exact preservesCoproduct_of_finitePartialSums E _
  let T := DerivedCategory.Q ⋙ F
  have hcomp : IsIso (sigmaComparison T E) := by
    apply (DerivedCategory.isIso_sigmaComparison_iff T E).2
    intro q
    have : PreservesColimit (Discrete.functor E)
        (T ⋙ DerivedCategory.homologyFunctor D q) := hT q
    infer_instance
  have : PreservesColimit (Discrete.functor E) T :=
    PreservesCoproduct.of_iso_comparison T E
  have : PreservesColimit (Discrete.functor (fun i ↦ DerivedCategory.Q.obj (E i))) F := by
    refine preservesColimit_of_preserves_colimit_cocone
      (DerivedCategory.isColimitCofanMkQObj (coproductIsCoproduct E)) ?_
    exact (isColimitMapCoconeCofanMkEquiv F _ _).2
      ((isColimitMapCoconeCofanMkEquiv T _ _).1
        (isColimitOfPreserves T (coproductIsCoproduct E)))
  exact preservesColimit_of_iso_diagram F
    (Discrete.natIso (fun i ↦ (he i.as).some) :
      Discrete.functor (fun i ↦ DerivedCategory.Q.obj (E i)) ≅ Discrete.functor K)

end CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
  {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]

private theorem continuity_preserves_strictlyGE
    {J : Type (u + 1)} [SmallCategory J] [IsFiltered J]
    (E : J ⥤ CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) ℤ)
    (N q : ℤ) (hE : ∀ j, (E.obj j).IsStrictlyGE N) :
    PreservesColimit E (DerivedCategory.Q ⋙ R((f)_*⟦Λ⟧) ⋙
      DerivedCategory.homologyFunctor _ q) := by
  let C := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)
  have : HasColimitsOfShape J C := inferInstance
  have : HasColimitsOfShape J (CochainComplex C ℤ) := inferInstance
  have : HasColimitsOfShape J
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj Λ Y)) := inferInstance
  let T := DerivedCategory.Q ⋙ R((f)_*⟦Λ⟧) ⋙ DerivedCategory.homologyFunctor _ q
  have : HasColimit (E ⋙ (ComplexShape.embeddingUpIntGE N).truncGEFunctor C) :=
    HasColimitsOfShape.has_colimit _
  have : HasColimit (E ⋙ T) := HasColimitsOfShape.has_colimit _
  have : ∀ j, (E.obj j).IsStrictlyGE N := hE
  let π := Functor.whiskerLeft E ((ComplexShape.embeddingUpIntGE N).πTruncGENatTrans C)
  have hi (j : J) : IsIso (π.app j) := by
    change IsIso (CochainComplex.πTruncGE (E.obj j) N)
    infer_instance
  have : IsIso π := NatIso.isIso_of_isIso_app π
  have hc : IsColimit (condensedContinuityCocone E N) :=
    (IsColimit.precomposeHomEquiv (asIso π) _).symm
      (colimit.isColimit (E ⋙ (ComplexShape.embeddingUpIntGE N).truncGEFunctor C))
  have hcomparison := condensed_qcqs_pushforward_continuity Λ f E N
    (fun j n hn ↦ CochainComplex.isZero_of_isGE (E.obj j) N n hn) q
  have hT : IsColimit (T.mapCocone (condensedContinuityCocone E N)) :=
    IsColimit.ofPointIso (colimit.isColimit (E ⋙ T)) (i := hcomparison)
  exact preservesColimit_of_preserves_colimit_cocone hc hT

/-- Ordinary qcqs derived pushforward preserves coproducts of complexes with a common
lower cohomology bound, for arbitrary condensed commutative coefficients.

Source: Hemo--Richarz--Scholbach, Lemma 5.3(1).
(blueprint: lem-sfb-adic-proper-bounded-below-coproducts)

Proof: choose representatives zero below N. Their coproduct is the filtered colimit
of finite partial sums, all still zero below N. Qcqs continuity preserves that
filtered colimit after pushforward and each homology functor. Additivity preserves
the finite partial sums, so the full coproduct comparison is invertible on homology.
Homology detects isomorphisms. Transport along the chosen representatives; this
includes the empty family, whose coproduct and all finite partial sums are zero.
-/
theorem condensed_boundedBelow_preservesCoproduct
    (I : Type (u + 1)) (N : ℤ)
    (K : I → DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (hN : ∀ i, (K i).IsGE N) :
    PreservesColimit (Discrete.functor K) R((f)_*⟦Λ⟧) := by
  classical
  let C := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)
  let D := Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)
  have : HasColimitsOfSize.{u + 1, u + 1} C := IsGrothendieckAbelian.hasColimits C
  have : HasColimitsOfSize.{u + 1, u + 1} D := IsGrothendieckAbelian.hasColimits D
  have : HasCoproducts.{u + 1} D := fun J ↦
    HasColimitsOfSize.has_colimits_of_shape (Discrete J)
  have : HasColimitsOfShape (Discrete I) C :=
    HasColimitsOfSize.has_colimits_of_shape _
  have : HasColimitsOfShape (Discrete I) D :=
    HasColimitsOfSize.has_colimits_of_shape _
  have : HasColimitsOfShape (Finset (Discrete I)) C :=
    HasColimitsOfSize.has_colimits_of_shape _
  have : HasExactColimitsOfShape (Discrete I) D := inferInstance
  exact preservesCoproduct_of_boundedBelow_continuity R((f)_*⟦Λ⟧) N K hN
    (fun E hE q ↦ continuity_preserves_strictlyGE Λ f E N q hE)

end AlgebraicGeometry.ProEtale.CondensedRing
