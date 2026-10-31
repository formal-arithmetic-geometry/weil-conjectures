/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicDerivedOpenAdjunction
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantDerivedDirectImage
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ModuleDerivedCategory
public import Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.AlgebraicGeometry.ProEtaleImmersionLimitPreservation
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Ring
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.CategoryTheory.Sites.Limits
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedInverseImageLeftAdjoint
import WeilConjectures.AlgebraicGeometry.IndEtaleBasisWeaklyContractibleCover
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.CategoryTheory.Sites.LowerShriekCoveringGenerators
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import WeilConjectures.CategoryTheory.Sites.LowerShriekCorepresentability
import Mathlib.CategoryTheory.Adjunction.PartialAdjoint
import Mathlib.CategoryTheory.Sites.Sheaf
import WeilConjectures.CategoryTheory.Sites.CoveringRepresentableCoequalizer
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Sites.RegularEpi
import Mathlib.CategoryTheory.Limits.Shapes.KernelPair
import WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedInverseImageEvaluation
import WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedSiteFunctorProperties
import WeilConjectures.CategoryTheory.InverseMateEquivalence
import WeilConjectures.AlgebraicGeometry.ProEtale.Replete
import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImageLimitsZariskiLocal
import Mathlib.CategoryTheory.Functor.ReflectsIso.Limits
import WeilConjectures.Mathlib.CategoryTheory.Sites.Sheaf
import WeilConjectures.Mathlib.CategoryTheory.NatIso
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageComparison
import Mathlib.Algebra.Category.Ring.FilteredColimits
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageUnderlying
import WeilConjectures.AlgebraicGeometry.ProEtaleModelRingPresentation
import WeilConjectures.CategoryTheory.SheafPullbackUnitPresentation
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import WeilConjectures.CategoryTheory.ModuleInverseImageAdjunction
import WeilConjectures.CategoryTheory.ModuleInverseImageAction
import WeilConjectures.CategoryTheory.ModuleInverseImageActionOfPresentations
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageScalarGraph
import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresAbelian
import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenInjectiveProperAcyclic
import WeilConjectures.AlgebraicGeometry.ProEtale.Proper.ProEtaleProperOpenSheafComparison
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.FullyFaithful
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusHomology

import WeilConjectures.AlgebraicGeometry.ProEtaleProductsExact
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import WeilConjectures.AlgebraicGeometry.ProEtaleSectionsLimitsColimits
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.AlgebraicGeometry.AffineScheme
import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Mathlib.CategoryTheory.Sites.LocallyBijective
import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Coseparator
import WeilConjectures.AlgebraicGeometry.ProEtale.SectionsConservative
import WeilConjectures.AlgebraicGeometry.WContractibleAffineCover
import WeilConjectures.RingTheory.ProEtale.WContractible
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import WeilConjectures.RingTheory.ProperBaseChange.IndPrincipalZariski
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleLeftComplete
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import WeilConjectures.AlgebraicGeometry.ProEtaleOpenClosedSequence
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import Mathlib.Algebra.Homology.ExactSequence
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.ClosedImmersion
import WeilConjectures.Mathlib.CategoryTheory.Functor.ReflectsIso.Exact

/-!
# Proper direct image preserves open support on the full pro-etale derived category

Source: Weil blueprint, `sec-smooth-purity/sk-prop-sf-existence`, clause (b),
compactification independence (blueprint: lem-sp-proper-open-derived-support).
Stacks Project, Tag 09AG, supplies only the degree-zero specialization vanishing used
in the proof, rather than the full derived support assertion stated here.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section

set_option autoImplicit false

section

-- Keep the ordinary localization and coefficient sizes fixed while elaborating the proof.
attribute [-instance] HasDerivedCategory.ofIsGrothendieckAbelian
  WeilConjectures.integralOperationsCommHasDerivedCategory
  WeilConjectures.integralOperationsAbSheafify
  WeilConjectures.integralOperationsAbLocallyBijective
  WeilConjectures.integralCoefficientAbLocallyBijective
  WeilConjectures.integralCoefficientAbSheafify

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

private noncomputable local instance (priority := 3000) fixed_sheafify (X : Scheme.{u}) :
    HasSheafify (ProEt.topology X) AddCommGrpCat.{u + 1} :=
  WeilConjectures.integralCoefficientAbSheafify.{u, u} X

private noncomputable local instance (priority := 3000) fixed_locallyBijective (X : Scheme.{u}) :
    (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  WeilConjectures.integralCoefficientAbLocallyBijective.{u, u} X

private noncomputable local instance fixed_derived (X : Scheme.{u}) (A : Type u) [CommRing A] :
    HasDerivedCategory.{u + 2} (proEtaleRingModules X (proEtaleConstantRing X A)) :=
  HasDerivedCategory.standard _

private theorem fixed_groth (X : Scheme.{u}) (A : Type u) [CommRing A] :
    IsGrothendieckAbelian.{u + 1}
      (proEtaleRingModules X (proEtaleConstantRing X A)) :=
  (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u + 1, u, 0}
    (ProEt.topology X) (proEtaleConstantRing X A)).1

private local instance fixed_kInjective (X : Scheme.{u}) (A : Type u) [CommRing A] :
    Abelian.HasKInjectiveResolutions (proEtaleRingModules X (proEtaleConstantRing X A)) :=
  proEtaleRingModules_hasKInjectiveResolutions X (proEtaleConstantRing X A)

private theorem derived_support_of_complex
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) (G : D ⥤ C) [F.Additive] [G.Additive]
    [CategoryTheory.Limits.PreservesFiniteLimits F]
    [CategoryTheory.Limits.PreservesFiniteColimits F]
    [CategoryTheory.Limits.PreservesFiniteLimits G]
    [CategoryTheory.Limits.PreservesFiniteColimits G]
    (adj : F ⊣ G) [F.Full] [F.Faithful]
    (adjD : F.mapDerivedCategory ⊣ G.mapDerivedCategory)
    (L : CochainComplex D ℤ)
    (hL : ∀ n : ℤ, IsIso (adj.counit.app (L.X n))) :
    IsIso (adjD.counit.app (DerivedCategory.Q.obj L)) := by
  have : IsIso adj.unit := inferInstance
  have ff := adjD.fullyFaithfulLOfCompIsoId
    ((Functor.mapDerivedCategoryCompIso F G).symm ≪≫
      Functor.mapDerivedCategoryNatIso (asIso adj.unit).symm ≪≫
        Functor.mapDerivedCategoryIdIso C)
  have := ff.full
  have := ff.faithful
  let C := G.mapHomologicalComplex (ComplexShape.up ℤ)
  let φ : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (C.obj L) ⟶ L :=
    { f n := adj.counit.app (L.X n)
      comm' _ _ _ := (adj.counit.naturality _).symm }
  have : ∀ n : ℤ, IsIso (φ.f n) := hL
  have : IsIso φ := HomologicalComplex.Hom.isIso_of_components φ
  apply adjD.isIso_counit_app_of_iso
  exact ((F.mapDerivedCategoryFactors.app (C.obj L)) ≪≫
    DerivedCategory.Q.mapIso (asIso φ)).symm

private noncomputable def acyclic_complex_computation
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [EnoughInjectives C] [Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] [CategoryTheory.Limits.PreservesFiniteLimits F]
    (L : CochainComplex.Plus C) (hL : ∀ n, F.rightAcyclic (L.obj.X n)) :
    F.rightDerivedFunctor.obj (DerivedCategory.Q.obj L.obj) ≅
      DerivedCategory.Q.obj ((F.mapHomologicalComplex _).obj L.obj) := by
  have := F.isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic L hL
  exact (F.rightDerivedFunctorPlusCompatibility.app (DerivedCategory.Plus.Q.obj L)).symm ≪≫
    DerivedCategory.Plus.ι.mapIso
      (asIso (F.rightDerivedFunctorPlusUnit.app
        ((HomotopyCategory.Plus.quotient C).obj L))).symm

private theorem bounded_support
    {C D E B : Type*} [Category* C] [Category* D] [Category* E] [Category* B]
    [Abelian C] [Abelian D] [Abelian E] [Abelian B]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [HasDerivedCategory B] [EnoughInjectives C] [EnoughInjectives D]
    [Abelian.HasKInjectiveResolutions D]
    (J : C ⥤ D) (P : D ⥤ E) (F : B ⥤ E) (G : E ⥤ B)
    [J.Additive] [P.Additive] [F.Additive] [G.Additive]
    [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    [PreservesFiniteLimits P]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (adj : F ⊣ G) [F.Full] [F.Faithful]
    (adjD : F.mapDerivedCategory ⊣ G.mapDerivedCategory)
    (hs : ∀ M, IsIso (adj.counit.app (P.obj (J.obj M))))
    (ha : ∀ (M : C) [Injective M], P.rightAcyclic (J.obj M))
    (K : DerivedCategory C) (n : ℤ) [K.IsGE n] :
    IsIso (adjD.counit.app (P.rightDerivedFunctor.obj (J.mapDerivedCategory.obj K))) := by
  let K' : DerivedCategory.Plus C := ⟨K, ⟨n, inferInstance⟩⟩
  have : K'.IsGE n := (K'.isGE_ι_obj_iff n).1 (show K.IsGE n from inferInstance)
  obtain ⟨L, hL, ⟨e⟩⟩ := DerivedCategory.Plus.exists_injective_nonempty_iso K' n
  let L' := (InjectiveObject.ι C).mapCochainComplexPlus.obj L
  let L'' := J.mapCochainComplexPlus.obj L'
  have hac (q : ℤ) : P.rightAcyclic (L''.obj.X q) := by
    have : Injective (L'.obj.X q) := inferInstanceAs (Injective (L.obj.X q).obj)
    exact ha (L'.obj.X q)
  let d : P.rightDerivedFunctor.obj (J.mapDerivedCategory.obj K) ≅
      DerivedCategory.Q.obj ((P.mapHomologicalComplex _).obj L''.obj) :=
    P.rightDerivedFunctor.mapIso
      (J.mapDerivedCategory.mapIso (DerivedCategory.Plus.ι.mapIso e).symm ≪≫
        J.mapDerivedCategoryFactors.app L'.obj) ≪≫
      acyclic_complex_computation P L'' hac
  have hh : IsIso (adjD.counit.app
      (DerivedCategory.Q.obj ((P.mapHomologicalComplex _).obj L''.obj))) := by
    apply derived_support_of_complex F G adj adjD
    intro q
    exact hs (L'.obj.X q)
  exact (NatTrans.isIso_app_iff_of_iso adjD.counit d).2 hh

private theorem kernel_preserves_products
    {C D : Type*} [Category* C] [Category* D] [Abelian D]
    (I : Type*) [HasProductsOfShape I C]
    (F G H : C ⥤ D) (a : F ⟶ G) (b : G ⟶ H)
    (hab : ∀ M, a.app M ≫ b.app M = 0)
    (hk : ∀ M, IsLimit (KernelFork.ofι (a.app M) (hab M)))
    [PreservesLimitsOfShape (Discrete I) G]
    [PreservesLimitsOfShape (Discrete I) H] :
    PreservesLimitsOfShape (Discrete I) F := by
  classical
  have h (K : I → C) : PreservesLimit (Discrete.functor K) F := by
    let P := ∏ᶜ K
    let cg := Fan.mk (G.obj P) (fun n ↦ G.map (Pi.π K n))
    let ch := Fan.mk (H.obj P) (fun n ↦ H.map (Pi.π K n))
    let hg : IsLimit cg := isLimitOfHasProductOfPreservesLimit G K
    let hh : IsLimit ch := isLimitOfHasProductOfPreservesLimit H K
    let lift (s : Fan (fun n ↦ F.obj (K n))) : s.pt ⟶ G.obj P :=
      Fan.IsLimit.lift hg (fun n ↦ s.proj n ≫ a.app (K n))
    have hz (s : Fan (fun n ↦ F.obj (K n))) : lift s ≫ b.app P = 0 := by
      apply Fan.IsLimit.hom_ext hh
      intro n
      dsimp [ch]
      change (lift s ≫ b.app P) ≫ H.map (Pi.π K n) = 0 ≫ H.map (Pi.π K n)
      rw [Category.assoc, ← b.naturality, ← Category.assoc]
      change (lift s ≫ cg.proj n) ≫ b.app (K n) = _
      rw [Fan.IsLimit.fac]
      simp [hab, Category.assoc]
    let l (s : Fan (fun n ↦ F.obj (K n))) : s.pt ⟶ F.obj P :=
      (hk P).lift (KernelFork.ofι (lift s) (hz s))
    apply preservesLimit_of_preserves_limit_cone (productIsProduct K)
    apply (isLimitMapConeFanMkEquiv F K _).symm.toFun
    refine Fan.IsLimit.mk _ l (fun s n ↦ ?_) (fun s m hm ↦ ?_)
    · have : Mono (a.app (K n)) := mono_of_isLimit_fork (hk (K n))
      apply (cancel_mono (a.app (K n))).1
      change (l s ≫ F.map (Pi.π K n)) ≫ a.app (K n) = _
      rw [Category.assoc, a.naturality, ← Category.assoc]
      change ((hk P).lift (KernelFork.ofι (lift s) (hz s)) ≫
        (KernelFork.ofι (a.app P) (hab P)).ι) ≫ cg.proj n = _
      rw [Fork.IsLimit.lift_ι]
      exact Fan.IsLimit.fac hg _ n
    · have : Mono (a.app P) := mono_of_isLimit_fork (hk P)
      apply (cancel_mono (a.app P)).1
      apply Fan.IsLimit.hom_ext hg
      intro n
      dsimp [cg]
      change ∀ n, m ≫ F.map (Pi.π K n) = s.proj n at hm
      rw [Category.assoc, ← a.naturality, ← Category.assoc, hm]
      change _ = ((hk P).lift (KernelFork.ofι (lift s) (hz s)) ≫
        (KernelFork.ofι (a.app P) (hab P)).ι) ≫ cg.proj n
      rw [Fork.IsLimit.lift_ι]
      change s.proj n ≫ a.app (K n) = lift s ≫ cg.proj n
      exact (Fan.IsLimit.fac hg (fun n ↦ s.proj n ≫ a.app (K n)) n).symm
  let := h
  exact preservesLimitsOfShape_of_discrete F

private theorem products_of_essSurj
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (I : Type*) [HasProductsOfShape I C]
    (Q : C ⥤ D) [Q.EssSurj] (F : D ⥤ E)
    [PreservesLimitsOfShape (Discrete I) Q]
    [PreservesLimitsOfShape (Discrete I) (Q ⋙ F)] :
    PreservesLimitsOfShape (Discrete I) F := by
  classical
  have h (K : I → D) : PreservesLimit (Discrete.functor K) F := by
    let K' := fun n ↦ Q.objPreimage (K n)
    let e : Discrete.functor K' ⋙ Q ≅ Discrete.functor K :=
      Discrete.natIso (fun n ↦ Q.objObjPreimageIso (K n.as))
    have : PreservesLimit (Discrete.functor K' ⋙ Q) F :=
      preservesLimit_of_preserves_limit_cone
        (isLimitOfPreserves Q (limit.isLimit (Discrete.functor K')))
        (isLimitOfPreserves (Q ⋙ F) (limit.isLimit (Discrete.functor K')))
    exact preservesLimit_of_iso_diagram F e
  let := h
  exact preservesLimitsOfShape_of_discrete F

private theorem derived_products_of_Q
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (I : Type*) [HasProductsOfShape I C]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesLimitsOfShape (Discrete I) F]
    [PreservesLimitsOfShape (Discrete I) (DerivedCategory.Q (C := C))]
    [PreservesLimitsOfShape (Discrete I) (DerivedCategory.Q (C := D))] :
    PreservesLimitsOfShape (Discrete I) F.mapDerivedCategory := by
  have : PreservesLimitsOfShape (Discrete I)
      (DerivedCategory.Q ⋙ F.mapDerivedCategory) :=
    preservesLimitsOfShape_of_natIso F.mapDerivedCategoryFactors.symm
  exact products_of_essSurj I DerivedCategory.Q F.mapDerivedCategory

private noncomputable abbrev fixed_forget (Λ : Type (u + 1)) [CommRing Λ]
    (X : Scheme.{u}) :=
  sheafCompose (ProEt.topology X)
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})

private noncomputable def fixed_pullback_forget_iso (Λ : Type (u + 1)) [CommRing Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ProEtale.upperStar (ModuleCat.{u + 1} Λ) f ⋙ fixed_forget Λ X ≅
      fixed_forget Λ Y ⋙ ProEtale.upperStar AddCommGrpCat.{u + 1} f := by
  let U := forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
  let Z := ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ)
  have : Z.IsLeftAdjoint :=
    (ModuleCat.restrictCoextendScalarsAdj.{0, 0, u + 1} (Int.castRingHom Λ)).isLeftAdjoint
  have : (Z ⋙ forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).IsLeftAdjoint :=
    inferInstance
  have : U.IsLeftAdjoint :=
    inferInstanceAs (Z ⋙ forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).IsLeftAdjoint
  have : (ProEt.topology X).PreservesSheafification U :=
    GrothendieckTopology.instPreservesSheafification (ProEt.topology X) U
  let L := (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).op
  let P := sheafToPresheaf (ProEt.topology Y) (ModuleCat.{u + 1} Λ)
  let Q := presheafToSheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ)
  let R := presheafToSheaf (ProEt.topology X) AddCommGrpCat.{u + 1}
  let W := (Functor.whiskeringRight X.ProEtᵒᵖ _ _).obj U
  have : U.PreservesLeftKanExtensions L := by
    intro F
    have : U.PreservesPointwiseLeftKanExtension F L := by
      intro c
      let : PreservesColimitsOfShape (CostructuredArrow L c) U :=
        (Adjunction.ofIsLeftAdjoint U).leftAdjoint_preservesColimits.preservesColimitsOfShape
      let : PreservesColimit (CostructuredArrow.proj L c ⋙ F) U :=
        PreservesColimitsOfShape.preservesColimit
      exact Functor.preservesPointwiseLeftKanExtensionAtOfPreservesColimit U F L c
    exact Functor.preservesPointwiseLKEOfHasPointwiseAndPreservesPointwise U F L
  let e := sheafComposeNatIso (ProEt.topology X) U
    (sheafificationAdjunction _ _) (sheafificationAdjunction _ _)
  let e' := U.lanCompIsoOfPreserves L
  change (P ⋙ L.lan ⋙ Q) ⋙ sheafCompose _ U ≅ _
  refine (Functor.associator P (L.lan ⋙ Q) (sheafCompose _ U)) ≪≫ ?_
  refine Functor.isoWhiskerLeft P
    ((Functor.associator L.lan Q (sheafCompose _ U)) ≪≫
      Functor.isoWhiskerLeft L.lan e.symm ≪≫
      (Functor.associator L.lan W R).symm ≪≫
      Functor.isoWhiskerRight e' R) ≪≫ ?_
  exact Iso.refl _

private theorem fixed_pullback_products (Λ : Type (u + 1)) [CommRing Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsImmersion f] :
    CategoryTheory.Limits.PreservesLimitsOfShape (Discrete ℕ)
      (ProEtale.upperStar (ModuleCat.{u + 1} Λ) f) := by
  let U := forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
  have hforget (T : Scheme.{u}) :
      PreservesLimitsOfShape (Discrete ℕ) (fixed_forget Λ T) := by
    have : PreservesLimitsOfShape (Discrete ℕ)
        (fixed_forget Λ T ⋙ sheafToPresheaf _ _) :=
      inferInstanceAs (PreservesLimitsOfShape (Discrete ℕ)
        (sheafToPresheaf _ _ ⋙ (Functor.whiskeringRight _ _ _).obj U))
    exact preservesLimitsOfShape_of_reflects_of_preserves _ (sheafToPresheaf _ _)
  have := hforget X
  have := hforget Y
  have : PreservesLimitsOfShape (Discrete ℕ)
      (ProEtale.upperStar AddCommGrpCat.{u + 1} f) :=
    by
      have h := (proEtale_immersion_inverseImage_preservesLimits f).2.1
      have : PreservesLimitsOfShape (Discrete (ULift.{u + 1} ℕ))
          (ProEtale.upperStar AddCommGrpCat.{u + 1} f) := h.preservesLimitsOfShape
      exact preservesLimitsOfShape_of_equiv (Discrete.equivalence Equiv.ulift) _
  have : ReflectsLimitsOfShape (Discrete ℕ) (fixed_forget Λ X) :=
    reflectsLimitsOfShape_of_reflectsIsomorphisms
  have : PreservesLimitsOfShape (Discrete ℕ)
      (ProEtale.upperStar (ModuleCat.{u + 1} Λ) f ⋙ fixed_forget Λ X) :=
    preservesLimitsOfShape_of_natIso (fixed_pullback_forget_iso Λ f).symm
  exact preservesLimitsOfShape_of_reflects_of_preserves _ (fixed_forget Λ X)

private theorem fixed_open_products (Λ : Type (u + 1)) [CommRing Λ]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j] :
    PreservesLimitsOfShape (Discrete ℕ)
      (ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j) := by
  let Z : TopologicalSpace.Closeds X :=
    ⟨(Set.range j)ᶜ, (Scheme.Hom.isOpenEmbedding j).isOpen_range.isClosed_compl⟩
  let i := (IdealSheafData.vanishingIdeal Z).subschemeι
  have hi : Set.range j = (Set.range i)ᶜ := by simp [i, Z]
  let C := Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ)
  let F := ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j
  let Q := ProEtale.upperStar (ModuleCat.{u + 1} Λ) j
  let H := ProEtale.upperStar (ModuleCat.{u + 1} Λ) i ⋙
    ProEtale.lowerStar (ModuleCat.{u + 1} Λ) i
  let a : Q ⋙ F ⟶ 𝟭 C :=
    (ProEtale.openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j).counit
  let b : 𝟭 C ⟶ H :=
    (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i).unit
  have hm (M : C) := ProEtale.exact_openClosedSequence Λ i j hi M
  have hab (M : C) : a.app M ≫ b.app M = 0 := ((hm M).2.2.sc 0).zero
  have hk (M : C) : IsLimit (KernelFork.ofι (a.app M) (hab M)) := by
    have : Mono (a.app M) := (hm M).1
    have he := (hm M).2.2.exact 0 (by omega)
    change (ShortComplex.mk (a.app M) (b.app M) _).Exact at he
    exact he.fIsKernel
  have := fixed_pullback_products Λ i
  have : PreservesLimitsOfShape (Discrete ℕ) H := comp_preservesLimitsOfShape _ _
  have : PreservesLimitsOfShape (Discrete ℕ) (Q ⋙ F) :=
    kernel_preserves_products ℕ (Q ⋙ F) (𝟭 C) H a b hab hk
  have : PreservesLimitsOfShape (Discrete ℕ) Q :=
    (ProEtale.openImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} Λ) j).rightAdjoint_preservesLimits.preservesLimitsOfShape
  have : Q.EssSurj := ⟨fun N ↦ ⟨F.obj N,
    ⟨(asIso ((ProEtale.openImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} Λ) j).unit.app N)).symm⟩⟩⟩
  exact products_of_essSurj ℕ Q F

private theorem intrinsic_open_products (A : Type u) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j] :
    PreservesLimitsOfShape (Discrete ℕ) (sfIntrinsicExtensionByZero j A) := by
  have := fixed_open_products (ULift.{u + 1, u} A) j
  unfold sfIntrinsicExtensionByZero
  infer_instance

private theorem intrinsic_pullback_products (A : Type u) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsImmersion j] :
    PreservesLimitsOfShape (Discrete ℕ) (sfIntrinsicPullback A j) := by
  have := fixed_pullback_products (ULift.{u + 1, u} A) j
  unfold sfIntrinsicPullback sfIntrinsicTransport
  infer_instance

private theorem support_of_homotopyLimit
    {C D : Type*} [Category C] [Category D]
    [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    (F : C ⥤ D) (G : D ⥤ C) (adj : F ⊣ G) [F.Full] [F.Faithful]
    [F.CommShift ℤ] [G.CommShift ℤ] [F.IsTriangulated] [G.IsTriangulated]
    [F.Additive] [G.Additive]
    [PreservesLimitsOfShape (Discrete ℕ) F] [PreservesLimitsOfShape (Discrete ℕ) G]
    {T : ℕᵒᵖ ⥤ D} (c : Cone T)
    (hc : CategoryTheory.Pretriangulated.IsHomotopyLimit c)
    (h : ∀ n : ℕ, IsIso (adj.counit.app (T.obj (Opposite.op n)))) :
    IsIso (adj.counit.app c.pt) := by
  let e : (T ⋙ G) ⋙ F ≅ T := NatIso.ofComponents
    (fun n ↦ by have := h n.unop; exact asIso (adj.counit.app (T.obj n)))
    (by intro a b f; exact adj.counit.naturality (T.map f))
  let c' := (Cone.postcompose e.hom).obj (F.mapCone (G.mapCone c))
  have hh : CategoryTheory.Pretriangulated.IsHomotopyLimit c' :=
    ((hc.map G).map F).of_iso e c' (Iso.refl _) (by intro n; simp [c'])
  obtain ⟨d, _⟩ := hc.exists_iso hh
  exact adj.isIso_counit_app_of_iso d

private theorem postnikov_homotopyLimit
    (X : Scheme.{u}) (A : Type u) [CommRing A]
    (L : CochainComplex (proEtaleRingModules X (proEtaleConstantRing X A)) ℤ) :
    ∃ (c : Cone (ProEt.postnikovTower L ⋙ DerivedCategory.Q.{u + 2, u + 1, u + 2})),
      c.pt = DerivedCategory.Q.{u + 2, u + 1, u + 2}.obj L ∧
      CategoryTheory.Pretriangulated.IsHomotopyLimit c := by
  let C := proEtaleRingModules X (proEtaleConstantRing X A)
  let R := (sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing X A)
  have : HasExactLimitsOfShape (Discrete ℕ) C := ProEt.products_exact.{u, u + 1, 0} X R ℕ
  let T := ProEt.postnikovTower L
  let V := fun n : ℕ ↦ T.obj (Opposite.op n)
  let P := ∏ᶜ V
  let φ : P ⟶ P := towerTransitionEndomorphism
    (WeilConjectures.integralOperationsTowerStep T)
  let M := CochainComplex.mappingCocone φ
  let p : Fan (fun n : ℕ ↦ (T ⋙ DerivedCategory.Q.{u + 2, u + 1, u + 2}).obj (Opposite.op n)) :=
    Fan.mk (DerivedCategory.Q.{u + 2, u + 1, u + 2}.obj P)
      (fun n ↦ DerivedCategory.Q.{u + 2, u + 1, u + 2}.map (Pi.π V n))
  let hp : IsLimit p := DerivedCategory.isLimitFanQ V
  have hm : DerivedCategory.Q.{u + 2, u + 1, u + 2}.map φ = 𝟙 p.pt -
      CategoryTheory.Pretriangulated.towerShift hp := by
    apply Fan.IsLimit.hom_ext hp
    intro n
    calc
      DerivedCategory.Q.map φ ≫ p.proj n = DerivedCategory.Q.map
          (Pi.π V n - Pi.π V (n + 1) ≫ T.map (homOfLE n.le_succ).op) := by
        change DerivedCategory.Q.map φ ≫ DerivedCategory.Q.map (Pi.π V n) = _
        rw [← Functor.map_comp]
        congr 1
        simp only [φ, towerTransitionEndomorphism, Preadditive.sub_comp,
          towerProductShift, Pi.lift_π]
        rfl
      _ = _ := by
        rw [Functor.map_sub, Functor.map_comp]
        simp only [Preadditive.sub_comp,
          Pretriangulated.towerShift, Fan.IsLimit.fac]
        rfl
  let t := DerivedCategory.Q.{u + 2, u + 1, u + 2}.mapTriangle.obj
    (CochainComplex.mappingCocone.triangle φ)
  have ht := DerivedCategory.mappingCocone_triangle_distinguished φ
  have hz : t.mor₁ ≫ (𝟙 p.pt - CategoryTheory.Pretriangulated.towerShift hp) = 0 := by
    rw [← hm]
    exact CategoryTheory.Pretriangulated.comp_distTriang_mor_zero₁₂ t ht
  let c : Cone (T ⋙ DerivedCategory.Q.{u + 2, u + 1, u + 2}) :=
    { pt := t.obj₁
      π := NatTrans.ofOpSequence (fun n ↦ t.mor₁ ≫ p.proj n) (by
        intro n
        have hh := congrArg (fun g ↦ g ≫ p.proj n) hz
        dsimp only [Functor.const_obj_map]
        erw [Category.id_comp]
        have h := hh
        simp only [Preadditive.comp_sub, Preadditive.sub_comp, Category.assoc,
          zero_comp, Pretriangulated.towerShift, Fan.IsLimit.fac,
          sub_eq_zero] at h
        exact h) }
  have hc : CategoryTheory.Pretriangulated.IsHomotopyLimit c := by
    refine ⟨p, hp, t.mor₃, ?_⟩
    apply CategoryTheory.Pretriangulated.isomorphic_distinguished t ht
    refine CategoryTheory.Pretriangulated.Triangle.isoMk _ _
      (Iso.refl (DerivedCategory.Q.obj M)) (Iso.refl (DerivedCategory.Q.obj P))
      (Iso.refl (DerivedCategory.Q.obj P)) ?_ ?_ ?_
    · change Fan.IsLimit.lift hp (fun n ↦ c.π.app (Opposite.op n)) ≫ 𝟙 _ =
        𝟙 _ ≫ DerivedCategory.Q.map (CochainComplex.mappingCocone.fst φ)
      simp only [Category.comp_id, Category.id_comp]
      apply Fan.IsLimit.hom_ext hp
      intro n
      simp only [c, NatTrans.ofOpSequence_app, Fan.IsLimit.fac]
      change t.mor₁ ≫ p.proj n = t.mor₁ ≫ p.proj n
      rfl
    · change (𝟙 p.pt - Pretriangulated.towerShift hp) ≫ 𝟙 _ =
        𝟙 _ ≫ DerivedCategory.Q.map φ
      simpa only [Category.comp_id, Category.id_comp] using hm.symm
    · change t.mor₃ ≫ (shiftFunctor _ (1 : ℤ)).map (𝟙 _) = 𝟙 _ ≫ t.mor₃
      rw [CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]
  have : QuasiIso (ProEt.postnikovComparison L) := ProEt.left_complete_quasiIso.{u, u + 1} X R L
  let e : DerivedCategory.Q.{u + 2, u + 1, u + 2}.obj M ≅
      DerivedCategory.Q.{u + 2, u + 1, u + 2}.obj L :=
    (asIso (DerivedCategory.Q.{u + 2, u + 1, u + 2}.map (ProEt.postnikovComparison L))).symm
  let d : Cone (T ⋙ DerivedCategory.Q.{u + 2, u + 1, u + 2}) :=
    { pt := DerivedCategory.Q.{u + 2, u + 1, u + 2}.obj L
      π :=
        { app n := e.inv ≫ c.π.app n
          naturality a b g := by
            simpa [Category.assoc] using congrArg (e.inv ≫ ·) (c.w g).symm } }
  exact ⟨d, rfl, hc.of_iso (Iso.refl _) d e (by intro n; simp [d])⟩

end AlgebraicGeometry.Scheme

end
