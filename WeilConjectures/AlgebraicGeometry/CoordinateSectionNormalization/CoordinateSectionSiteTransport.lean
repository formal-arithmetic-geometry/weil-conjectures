/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.CoordinateSectionNormalization.TwistedCoordinateSectionCartier
public import WeilConjectures.AlgebraicGeometry.CoordinateSectionNormalization.TwistedCoordinateSectionOrdinary
public import WeilConjectures.AlgebraicGeometry.CoordinateSectionNormalization.TwistedCoordinateSectionCoprojection
public import WeilConjectures.AlgebraicGeometry.CoordinateSectionNormalization.TwistedCoordinateSectionMaps
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.Tactic.Convert
import WeilConjectures.AlgebraicGeometry.Cartier.CartierKummerMap
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedCartierKummerSupplement
import WeilConjectures.AlgebraicGeometry.CoordinateLine.CoordinateLineAdjunction
import WeilConjectures.SmoothPurity.Adic.AdicPurityRootComparisons
import WeilConjectures.SixFunctors.OpenClosed.Exact
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteTraceCounit
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Data
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
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteSingleUnitNaturality
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTwistLine
import WeilConjectures.SixFunctors.Etale.Derived.CoefficientsShift

/-! # Finite-site realization and transport of the coordinate normalization

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-an/
cor-pur-affine-space-zero-section-purity.proof.md, rank-one supported Cartier
normalization, even twists and finite etale-origin transport.
(blueprint: lem-pur-coordinate-section-site-transport)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option maxRecDepth 4000
set_option Elab.async false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CoordinateSectionNormalization

open AffineLinePurity VectorIntegrationSite
open CategoryTheory.Abelian CategoryTheory.MonoidalCategory

set_option linter.auxLemma false in
attribute [local instance 100000] Etale.DerivedCategoryModule._proof_1
  Etale.DerivedCategoryModule._proof_2
attribute [local instance 100001] Etale.ordinaryFiniteDerivedCategoryInstance
-- Match the cached abelian and localization structures used by the Cartier and ordinary APIs.
attribute [local implicit_reducible] Etale.cartierAbelianEtale Etale.cartierAbelianPro
  Etale.ordinaryFiniteDerivedCategoryInstance
attribute [local implicit_reducible] Etale.CartierEtaleKummerFamily Etale.CartierKummerFamily
attribute [local implicit_reducible] Etale.ordinaryFiniteSingleFunctor
  Etale.ordinaryFiniteDegreeZero Etale.derivedTensorRight Etale.ordinaryFiniteTwistedPullback
  sfFiniteExceptionalAt Scheme.finiteEtaleTateTwist

attribute [local irreducible] DerivedCategory HasDerivedCategory.ofIsGrothendieckAbelian
  DerivedCategory.singleFunctors Functor.mapDerivedCategory
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor

universe vC vD vCp vDp uC uD uCp uDp

private theorem unit_natural_formula
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    {L : C ⥤ D} {U : D ⥤ C} (a : L ⊣ U) {M N : C} (f : M ⟶ N) :
    a.unit.app M ≫ U.map (L.map f) = f ≫ a.unit.app N := by
  simpa only [Functor.id_map, Functor.comp_map] using (a.unit.naturality f).symm

private theorem transport_composite_identity
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    (S : D ⥤ C) (G R : C ⥤ D) (g : G ≅ R) (d : R ⋙ S ≅ 𝟭 C)
    {M M' : C} (e : M ≅ M') (o : M ⟶ S.obj (G.obj M))
    (o' : M' ⟶ S.obj (G.obj M'))
    (hn : e.hom ≫ o' = o ≫ S.map (G.map e.hom))
    (he' : o' ≫ S.map (g.hom.app M') ≫ d.hom.app M' = 𝟙 M') :
    IsIso o ∧ o ≫ S.map (g.hom.app M) ≫ d.hom.app M = 𝟙 M := by
  have hg := g.hom.naturality e.hom
  have hd := d.hom.naturality e.hom
  simp only [Functor.comp_map, Functor.id_map, Functor.comp_obj, Functor.id_obj] at hg hd
  have hw : e.hom ≫ o' ≫ S.map (g.hom.app M') ≫ d.hom.app M' =
      (o ≫ S.map (g.hom.app M) ≫ d.hom.app M) ≫ e.hom := by
    rw [← Category.assoc e.hom o', hn]
    simp only [Category.assoc]
    rw [← S.map_comp_assoc, hg, S.map_comp, Category.assoc, hd]
  have he : o ≫ S.map (g.hom.app M) ≫ d.hom.app M = 𝟙 M := by
    apply (cancel_mono e.hom).mp
    simpa only [Category.assoc, Category.id_comp, he', Category.comp_id] using hw.symm
  refine ⟨?_, he⟩
  have : IsIso (o ≫ (S.map (g.hom.app M) ≫ d.hom.app M)) := by
    rw [he]
    infer_instance
  exact IsIso.of_isIso_comp_right o (S.map (g.hom.app M) ≫ d.hom.app M)

universe wE wF wDC wDD

private theorem ext_realization_transport
    {C : Type uC} [Category.{vC} C] [Abelian C]
    {D : Type uD} [Category.{vD} D] [Abelian D]
    [HasDerivedCategory.{wDC} C] [HasDerivedCategory.{wDD} D]
    [HasExt.{wE} C] [HasExt.{wF} D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {S L : C} {S' L' : D} (κ : Ext S L 2) (c : Ext S' L' 2)
    (α : F.obj S ≅ S') (q : F.obj L ≅ L')
    (h : (Ext.mk₀ α.hom).comp c (zero_add 2) =
      (κ.mapExactFunctor F).comp (Ext.mk₀ q.hom) (add_zero 2)) :
    F.mapDerivedCategory.map κ.hom ≫
        (F.mapDerivedCategory.commShiftIso (2 : ℤ)).hom.app
          ((DerivedCategory.singleFunctor C 0).obj L) ≫
        (shiftFunctor (DerivedCategory D) (2 : ℤ)).map
          ((F.mapDerivedCategorySingleFunctor 0).hom.app L) ≫
        (shiftFunctor (DerivedCategory D) (2 : ℤ)).map
          ((DerivedCategory.singleFunctor D 0).map q.hom) =
      (F.mapDerivedCategorySingleFunctor 0).hom.app S ≫
        (DerivedCategory.singleFunctor D 0).map α.hom ≫ c.hom := by
  have hh := congrArg Ext.hom h
  simp only [Ext.comp_hom, Ext.mk₀_hom, Ext.mapExactFunctor_hom,
    ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀, ShiftedHom.map, Category.assoc] at hh
  have ht := congrArg (fun z ↦ (F.mapDerivedCategorySingleFunctor 0).hom.app S ≫ z) hh
  simpa only [Category.assoc, Iso.hom_inv_id_app_assoc,
    Functor.comp_obj, Nat.cast_ofNat] using ht.symm

private theorem supportedUnit_epi (A : Type (u + 1)) [CommRing A]
    {D X : Scheme.{u}} (i : D ⟶ X) [IsClosedImmersion i] :
    Epi ((comparisonUpperStar (ModuleCat.{u + 1} A) X).map
      (Etale.supportedConstantUnit A i)) := by
  have h := Etale.shortExact_openClosedShortComplex (ModuleCat.{u + 1} A)
    i.openComplement.ι i (Etale.ordinaryFiniteConstant A X)
    i.range_eq_compl_range_openComplement_ι
  have : Epi ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i).unit.app
      (Etale.ordinaryFiniteConstant A X)) := h.epi_g
  have : Epi (Etale.supportedConstantUnit A i) := by
    unfold Etale.supportedConstantUnit
    rw [Adjunction.homEquiv_unit]
    infer_instance
  let := Functor.preservesEpimorphisms_of_adjunction
    (comparisonAdjunction (ModuleCat.{u + 1} A) X)
  exact Functor.map_epi _ _

private theorem cartier_normalization_function
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (κ : Etale.CartierEtaleKummerFamily l E)
    (h : Etale.CartierEtaleKummerNormalization l E κ) :
  ∀ (n r : ℕ) (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    {D T : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]
    (hI : i.ker.IsInvertible) (hT : IsUnit (l : Γ(T, ⊤))),
    Etale.SupportedKummerBoundary (Scheme.finiteTateCoefficient l E n) (l ^ (r + 1)) hA i hI
      (by simpa only [Nat.cast_pow] using hT.pow (r + 1)) (κ n r hA i hI hT) := by
  unfold Etale.CartierEtaleKummerNormalization at h
  exact h

private theorem cartier_realization_function
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (κ : Etale.CartierEtaleKummerFamily l E) (c : Etale.CartierKummerFamily l E)
    (h : Etale.CartierKummerRealization l E κ c) :
  ∀ (n r : ℕ) (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    {D T : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]
    (hI : i.ker.IsInvertible) (hT : IsUnit (l : Γ(T, ⊤))),
    ∃ (α : (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)) T).obj
          ((Etale.lowerStar (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)) i).obj
            (Etale.ordinaryFiniteConstant (Scheme.finiteTateCoefficient l E n) D)) ≅
        Etale.cartierSupported l E n i)
      (q : (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)) T).obj
          (Scheme.finiteEtaleTateLine T (l ^ (r + 1)) (Scheme.finiteTateCoefficient l E n) hA) ≅
            Scheme.finiteTateProSheaf l E n T 1),
      Scheme.IsFiniteTateSiteComparison l E n T r hA 1 q ∧
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)) T).map
          (Etale.supportedConstantUnit (Scheme.finiteTateCoefficient l E n) i) ≫ α.hom =
        Etale.cartierConstantComparison (Scheme.finiteTateCoefficient l E n) T ≫
          Etale.cartierSupportedUnit l E n i ∧
      (Ext.mk₀ α.hom).comp (c n i hI hT) (zero_add 2) =
        ((κ n r hA i hI hT).mapExactFunctor
          (ProEtale.comparisonUpperStar
            (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)) T)).comp
          (Ext.mk₀ q.hom) (add_zero 2) := by
  unfold Etale.CartierKummerRealization at h
  exact h

set_option maxHeartbeats 1500000 in
-- Expand the cached derived comparison arrows within this calculation.
private theorem cartier_realization (P : WeilConjectures.PurityFiniteSetting.{u})
    (T : Scheme.{u}) (aT : T ⟶ Spec (.of P.field.k))
    (hI : (sectionMap T).ker.IsInvertible) : CartierRealization T P aT hI := by
  classical
  let X := AffineSpace PUnit.{u + 1} T
  let hX := primeUnit P X ((AffineSpace PUnit.{u + 1} T ↘ T) ≫ aT)
  have hnorm := cartier_normalization_function P.coefficients.l P.extension _
    (Etale.cartier_kummer_map P.coefficients.l P.extension).2.exists.choose_spec.1
  have hc := cartier_realization_function P.coefficients.l P.extension _ _
    (Etale.cartier_kummer_map P.coefficients.l P.extension).2.exists.choose_spec.2.2.1
  obtain ⟨r, hr⟩ := (Etale.cartier_kummer_map P.coefficients.l P.extension).1 (P.level - 1)
  obtain ⟨α, _, _, hα, _⟩ := hc (P.level - 1) r hr (sectionMap T) hI hX
  refine ⟨α, hα, ?_⟩
  intro b hA
  obtain ⟨α', q', hq', hα', he'⟩ := hc (P.level - 1) b hA (sectionMap T) hI hX
  have := supportedUnit_epi (Ring P) (sectionMap T)
  have ha : α' = α := Iso.ext ((cancel_epi _).mp (hα'.trans hα.symm))
  have hqnorm : Scheme.IsFiniteTateSiteComparison P.coefficients.l P.extension
      (P.level - 1) X b hA 1
      (twistComparison P.coefficients.l P.extension (P.level - 1) X hX b hA 1) := by
    unfold twistComparison
    exact (Scheme.finite_tate_site_descent P.coefficients.l P.extension
      (P.level - 1)).choose_spec.1 X hX b hA 1
  have hqeq : q' = twistComparison P.coefficients.l P.extension (P.level - 1) X hX b hA 1 :=
    (WeilConjectures.adicPurityRootComparison_existsUnique P.coefficients.l P.extension
      (P.level - 1) X hX b hA 1).unique
      hq' hqnorm
  rw [ha, hqeq] at he'
  let hNX : IsUnit ((P.coefficients.l ^ (b + 1) : ℕ) : Γ(X, ⊤)) := by
    simpa only [Nat.cast_pow] using hX.pow (b + 1)
  have hk : (Etale.cartier_kummer_map P.coefficients.l P.extension).2.exists.choose.1
      (P.level - 1) b hA (sectionMap T) hI hX =
      ordinaryClass (Ring P) T (P.coefficients.l ^ (b + 1))
        (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) hA
        hNX hI := by
    unfold ordinaryClass
    exact (Etale.ordinary_supported_kummer_uniqueBoundary X (P.coefficients.l ^ (b + 1))
      (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) (Ring P) hA
      hNX
      (sectionMap T) hI).unique
        (by simpa only [AffineLinePurity.Ring] using
          hnorm (P.level - 1) b hA (sectionMap T) hI hX)
        (Etale.ordinary_supported_kummer_uniqueBoundary X (P.coefficients.l ^ (b + 1))
          (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) (Ring P) hA
          hNX
          (sectionMap T) hI).exists.choose_spec
  rw [hk] at he'
  have hh := ext_realization_transport
    (comparisonUpperStar (ModuleCat.{u + 1} (Ring P)) X) _ _ α
    (twistComparison P.coefficients.l P.extension (P.level - 1) X hX b hA 1) he'
  unfold ordinarySupported Etale.supportedExactDerivedMap cartierSource twistDerived
    Etale.cartierKummerMap
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Functor.map_comp,
    Category.assoc]
  simpa only [Category.assoc, VectorIntegrationSite.comparison, geoP1Comparison,
    Scheme.finiteEtaleTateTwist, Nat.cast_ofNat] using
    congrArg (fun z ↦ (VectorIntegrationSite.comparison (Ring P) X).map
      ((Etale.lowerStar (ModuleCat.{u + 1} (Ring P))
        (sectionMap T)).singleFunctorCompRightDerivedFunctorIso.hom.app
          (Etale.ordinaryFiniteConstant (Ring P) T)) ≫ z) hh

private theorem exceptional_equation_transport
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    (R : C ⥤ D) (S : D ⥤ C) (e : R ⋙ S ≅ 𝟭 C)
    {M N : C} {V : D} (o : M ⟶ S.obj V) (g : V ⟶ R.obj M)
    (he : o ≫ S.map g ≫ e.hom.app M = 𝟙 M) (f : M ⟶ N) :
    o ≫ S.map (g ≫ R.map f) ≫ e.hom.app N = f := by
  have hn := e.hom.naturality f
  simp only [Functor.comp_map, Functor.id_map, Functor.comp_obj, Functor.id_obj] at hn
  simp only [Functor.map_comp, Category.assoc]
  rw [hn]
  simpa only [Category.assoc, Category.id_comp] using
    congrArg (fun z ↦ z ≫ f) he

private theorem unit_cancel_formula
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    {L : C ⥤ D} {U : D ⥤ C} (a : L ⊣ U) {M N : C} (f : M ⟶ N)
    [IsIso (a.unit.app N)] :
    a.unit.app M ≫ U.map (L.map f) ≫ inv (a.unit.app N) = f := by
  rw [← Category.assoc, unit_natural_formula]
  simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id]

private theorem closedProjection_natural
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u})
    {M M' : Etale.DerivedCategoryModule A T} (f : M ⟶ M') :
    ((Etale.ordinaryFiniteTensor A (AffineSpace PUnit.{u + 1} T)).map
        ((Etale.ordinaryFinitePullback A (AffineSpace PUnit.{u + 1} T ↘ T)).map f)).app
        ((closedImage A T).obj (Etale.ordinaryFiniteUnit A T)) ≫
      closedProjection A T M' = closedProjection A T M ≫ (closedImage A T).map f := by
  let Q := Etale.ordinaryFiniteTensor A T
  let J := closedImage A T
  let e := Etale.leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A)
    (sectionMap T) (AffineSpace PUnit.{u + 1} T ↘ T)
    (AffineSpace.zeroSection_comp_over PUnit.{u + 1} T)
  have hu : (Q.map f).app (Etale.ordinaryFiniteUnit A T) ≫
      (Etale.derivedTensorSingleUnitIso M').hom =
      (Etale.derivedTensorSingleUnitIso M).hom ≫ f := by
    apply (cancel_epi (Etale.derivedTensorSingleUnitIso M).inv).mp
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.inv_hom_id_assoc] using
      congrArg (fun z ↦ z ≫ (Etale.derivedTensorSingleUnitIso M').hom)
        (Etale.ordinaryFiniteSingleUnit_naturality A T f).symm
  have hn := NatTrans.congr_app (congrArg Q.map (e.hom.naturality f))
    (Etale.ordinaryFiniteUnit A T)
  simp only [Functor.map_comp, NatTrans.comp_app, Functor.comp_map, Functor.id_map] at hn
  have hh := congrArg (fun z ↦ z ≫ (Etale.derivedTensorSingleUnitIso M').hom) hn
  simp only [Category.assoc] at hh
  rw [hu] at hh
  unfold closedProjection
  rw [← Category.assoc, Etale.ordinaryFiniteProjection_naturality, Category.assoc]
  simp only [Category.assoc, ← Functor.map_comp]
  exact congrArg (fun z ↦ Etale.ordinaryFiniteProjection A (sectionMap T)
    (Etale.ordinaryFiniteUnit A T)
    ((Etale.ordinaryFinitePullback A (AffineSpace PUnit.{u + 1} T ↘ T)).obj M) ≫
      J.map z) hh

private theorem tensorSupported_natural
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u})
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (hT : IsUnit (N : Γ(T, ⊤))) (hI : (sectionMap T).ker.IsInvertible)
    {M M' : Etale.DerivedCategoryModule A T} (f : M ⟶ M')
    (hpf : IsIso (closedProjection A T M)) (hpf' : IsIso (closedProjection A T M')) :
    (closedImage A T).map f ≫ tensorSupported A T N hN hA hT hI M' hpf' =
      tensorSupported A T N hN hA hT hI M hpf ≫
        (CoordinateLine.right A N hA T).map f := by
  let := hpf
  let := hpf'
  have hi : (closedImage A T).map f ≫ inv (closedProjection A T M') =
      inv (closedProjection A T M) ≫
        ((Etale.ordinaryFiniteTensor A (AffineSpace PUnit.{u + 1} T)).map
          ((Etale.ordinaryFinitePullback A (AffineSpace PUnit.{u + 1} T ↘ T)).map f)).app
          ((closedImage A T).obj (Etale.ordinaryFiniteUnit A T)) := by
    apply (cancel_epi (closedProjection A T M)).mp
    rw [← Category.assoc, ← closedProjection_natural, Category.assoc]
    simp
  unfold tensorSupported CoordinateLine.right Etale.ordinaryFiniteTwistedPullback
  dsimp only [id_eq, Functor.comp_obj, Functor.comp_map, Etale.derivedTensorRight,
    Etale.ordinaryFiniteTensor, Functor.flip_obj_obj, Functor.flip_obj_map]
  rw [← Category.assoc, hi, Category.assoc]
  simpa only [Category.assoc, Etale.ordinaryFiniteTensor] using
    congrArg (fun z ↦ inv (closedProjection A T M) ≫ z)
      (((Etale.ordinaryFiniteTensor A (AffineSpace PUnit.{u + 1} T)).map
        ((Etale.ordinaryFinitePullback A (AffineSpace PUnit.{u + 1} T ↘ T)).map f)).naturality
          (restrictedSupported A T N hN hA hT hI)).symm

private theorem orientation_natural
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u})
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (hT : IsUnit (N : Γ(T, ⊤))) (hI : (sectionMap T).ker.IsInvertible)
    {M M' : Etale.DerivedCategoryModule A T} (f : M ⟶ M')
    (hpf : IsIso (closedProjection A T M)) (hpf' : IsIso (closedProjection A T M')) :
    f ≫ ordinaryOrientation A T N hN hA hT hI M' hpf' =
      ordinaryOrientation A T N hN hA hT hI M hpf ≫
        (closedImage A T).rightAdjoint.map ((CoordinateLine.right A N hA T).map f) := by
  unfold ordinaryOrientation
  rw [← Adjunction.homEquiv_naturality_left, tensorSupported_natural,
    Adjunction.homEquiv_naturality_right]

set_option maxHeartbeats 500000 in
-- Check the canonical cached degree-zero object comparison once, before transport.
private theorem tate_zero_eq (A : Type (u + 1)) [CommRing A]
    (T : Scheme.{u}) (N : ℕ) (hA : (N : A) = 0) :
    Etale.SectionLocalDualizingComparisons.tateObject A N hA T 0 =
      (Etale.ordinaryFiniteUnit A T)⟦(0 : ℤ)⟧ := by
  rfl

@[irreducible] private def unit_tate_iso (A : Type (u + 1)) [CommRing A]
    (T : Scheme.{u}) (N : ℕ) (hA : (N : A) = 0) :
    Etale.ordinaryFiniteUnit A T ≅
      Etale.SectionLocalDualizingComparisons.tateObject A N hA T 0 :=
  (shiftFunctorZero (Etale.DerivedCategoryModule A T) ℤ).symm.app _ ≪≫
    eqToIso (tate_zero_eq A T N hA).symm

set_option maxHeartbeats 500000 in
-- Expose only the Tate exceptional equation from the large ordinary normalization predicate.
private theorem ordinary_tate_data
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u}) [IsNoetherian T]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (hT : IsUnit (N : Γ(T, ⊤))) (hI : (sectionMap T).ker.IsInvertible)
    (hOrd : OrdinaryNormalization A T N hN hA hT hI) (r : ℕ) :
    ∃ hpf : IsIso (closedProjection A T
        (Etale.SectionLocalDualizingComparisons.tateObject A N hA T r)),
      IsIso (ordinaryOrientation A T N hN hA hT hI
        (Etale.SectionLocalDualizingComparisons.tateObject A N hA T r) hpf) ∧
      ordinaryOrientation A T N hN hA hT hI
          (Etale.SectionLocalDualizingComparisons.tateObject A N hA T r) hpf ≫
        (closedImage A T).rightAdjoint.map
          ((CoordinateLine.comparison A N hA T hN hT).hom.app
            (Etale.SectionLocalDualizingComparisons.tateObject A N hA T r)) ≫
        (exceptionalComposition A T).hom.app
          (Etale.SectionLocalDualizingComparisons.tateObject A N hA T r) = 𝟙 _ := by
  obtain ⟨hpf, ho, _, he⟩ := hOrd.2.2.2 r
  exact ⟨hpf, ho, he⟩

set_option maxHeartbeats 500000 in
-- Discard the unused coprojection witnesses before the coefficient transport calculation.
private theorem unit_projection_data
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u}) [IsNoetherian T]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (hT : IsUnit (N : Γ(T, ⊤))) (hI : (sectionMap T).ker.IsInvertible)
    (hCop : CoprojectionNormalization A T N hN hA hT hI) :
    IsIso (closedProjection A T (Etale.ordinaryFiniteUnit A T)) := by
  obtain ⟨hpf, _⟩ := hCop.2 (Etale.ordinaryFiniteUnit A T) (Or.inl rfl)
  exact hpf

private theorem orientation_transport
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u}) [IsNoetherian T]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (hT : IsUnit (N : Γ(T, ⊤))) (hI : (sectionMap T).ker.IsInvertible)
    {M M' : Etale.DerivedCategoryModule A T} (e : M ≅ M')
    (hpf : IsIso (closedProjection A T M)) (hpf' : IsIso (closedProjection A T M'))
    (he' : ordinaryOrientation A T N hN hA hT hI M' hpf' ≫
      (closedImage A T).rightAdjoint.map
        ((CoordinateLine.comparison A N hA T hN hT).hom.app M') ≫
      (exceptionalComposition A T).hom.app M' = 𝟙 M') :
    IsIso (ordinaryOrientation A T N hN hA hT hI M hpf) ∧
      ordinaryOrientation A T N hN hA hT hI M hpf ≫
        (closedImage A T).rightAdjoint.map
          ((CoordinateLine.comparison A N hA T hN hT).hom.app M) ≫
        (exceptionalComposition A T).hom.app M = 𝟙 M := by
  exact transport_composite_identity (closedImage A T).rightAdjoint
    (CoordinateLine.right A N hA T) (compact A T).rightAdjoint
    (CoordinateLine.comparison A N hA T hN hT) (exceptionalComposition A T) e
    (ordinaryOrientation A T N hN hA hT hI M hpf)
    (ordinaryOrientation A T N hN hA hT hI M' hpf')
    (orientation_natural A T N hN hA hT hI e.hom hpf hpf') he'

set_option maxHeartbeats 1500000 in
-- Instantiate naturality only after caching the degree-zero and normalization comparisons.
private theorem unit_ordinary
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u}) [IsNoetherian T]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (hT : IsUnit (N : Γ(T, ⊤))) (hI : (sectionMap T).ker.IsInvertible)
    (hOrd : OrdinaryNormalization A T N hN hA hT hI)
    (hCop : CoprojectionNormalization A T N hN hA hT hI) :
    ∃ hpf : IsIso (closedProjection A T (Etale.ordinaryFiniteUnit A T)),
      IsIso (ordinaryOrientation A T N hN hA hT hI (Etale.ordinaryFiniteUnit A T) hpf) ∧
      ordinaryOrientation A T N hN hA hT hI (Etale.ordinaryFiniteUnit A T) hpf ≫
        (closedImage A T).rightAdjoint.map
          ((CoordinateLine.comparison A N hA T hN hT).hom.app
            (Etale.ordinaryFiniteUnit A T)) ≫
        (exceptionalComposition A T).hom.app (Etale.ordinaryFiniteUnit A T) = 𝟙 _ := by
  let hpf := unit_projection_data A T N hN hA hT hI hCop
  obtain ⟨hpf0, _, he0⟩ := ordinary_tate_data A T N hN hA hT hI hOrd 0
  exact ⟨hpf, orientation_transport A T N hN hA hT hI
    (unit_tate_iso A T N hA) hpf hpf0 he0⟩

private theorem tate_properties (A : Type (u + 1)) [CommRing A] [Finite A]
    (T : Scheme.{u}) (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (hT : IsUnit (N : Γ(T, ⊤))) (r : ℕ) :
    Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) T
      (Etale.SectionLocalDualizingComparisons.tateObject A N hA T r) := by
  classical
  have ht := Scheme.finite_etale_torsion_twist_line T N hN
    (fun x ↦ by
      simpa only [map_natCast] using hT.map (T.presheaf.germ ⊤ x (by trivial)).hom)
    A hA r
  obtain ⟨cover, hc⟩ := ht.1
  have hlocal (i : cover.I₀) : Scheme.IsFiniteLocallyConstantSheaf
      ((Etale.upperStar (ModuleCat.{u + 1} A) (cover.f i)).obj
        (Scheme.finiteEtaleTateTwist T N A hA r)) := by
    let U := cover.etalePrecoverageToEtale i
    let E := Scheme.Etale.overSheafEquiv U (ModuleCat.{u + 1} A)
    let c := (Scheme.Etale.overEquiv U).constantSheafSheafCongrIso
      (T.smallEtaleTopology.over U) U.left.smallEtaleTopology (ModuleCat.{u + 1} A)
      Over.mkIdTerminal
    let e := (Scheme.overSheafEquivFunctorObjOverIso (ModuleCat.{u + 1} A) U
        (Scheme.finiteEtaleTateTwist T N A hA r)).symm ≪≫
      E.functor.mapIso (hc i).some ≪≫ c.app (ModuleCat.of A A)
    have : Scheme.IsFiniteLocallyConstantSheaf
        ((constantSheaf U.left.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
          (ModuleCat.of A A)) :=
      Etale.isFiniteLocallyConstantSheaf_constantSheaf (ModuleCat.of A A)
    exact Scheme.IsFiniteLocallyConstantSheaf.of_iso e.symm
  have := hlocal
  have hfinite := Scheme.IsFiniteLocallyConstantSheaf.of_cover cover
    (Scheme.finiteEtaleTateTwist T N A hA r)
  have := hfinite.isConstructibleSheaf
  have hflat : ObjectProperty.flat (Scheme.finiteEtaleTateTwist T N A hA r) :=
    (ObjectProperty.flat_iff_preservesFiniteLimits _).2 ht.2.2.1
  have hs : Etale.DerivedCategory.boundedConstructibleFiniteTor A T
      ((DerivedCategory.singleFunctor _ 0).obj (Scheme.finiteEtaleTateTwist T N A hA r)) :=
    ⟨Etale.DerivedCategory.boundedConstructible_singleFunctor_obj _ 0,
      0, 0, DerivedCategory.torAmplitudeIn_singleFunctor_obj_of_flat
        hflat⟩
  exact Etale.DerivedCategory.boundedConstructibleFiniteTor.shift hs (2 * (r : ℤ))

private theorem comparison_plus (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (M : Etale.DerivedCategoryModule A T) (hM : DerivedCategory.TStructure.t.plus M) :
    DerivedCategory.TStructure.t.plus ((VectorIntegrationSite.comparison A T).obj M) := by
  obtain ⟨a, ha⟩ := hM
  have := ha
  exact ⟨a, (comparisonUpperStar (ModuleCat.{u + 1} A) T).isGE_mapDerivedCategory_obj M a⟩

set_option maxHeartbeats 500000 in
-- Extract the normalized finite-site equation before cancelling its source comparisons.
private theorem gamma_normalized_equation (P : WeilConjectures.PurityFiniteSetting.{u})
    (T : Scheme.{u}) [IsNoetherian T] (b : ℕ)
    (hA : ((P.coefficients.l ^ (b + 1) : ℕ) : Ring P) = 0)
    (aT : T ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aT] [QuasiCompact aT] [IsSeparated aT]
    (hT : IsUnit ((P.coefficients.l ^ (b + 1) : ℕ) : Γ(T, ⊤)))
    (M : Etale.DerivedCategoryModule (Ring P) T)
    (hM : Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} (Ring P)) T M)
    (hplus : DerivedCategory.TStructure.t.plus
      ((VectorIntegrationSite.comparison (Ring P) T).obj M)) :
    affineLinePurityComparison P T b hA aT
      ⟨(VectorIntegrationSite.comparison (Ring P) T).obj M, hplus⟩ M hM (Iso.refl _) =
      CoordinateLine.comparedConjugate P T b hA hT
        ⟨(VectorIntegrationSite.comparison (Ring P) T).obj M, hplus⟩ M (Iso.refl _) := by
  obtain ⟨hT', _, hh⟩ := (CoordinateLine.coordinateLineAdjunction P T aT).2.2.2.2.2.1 b hA
  exact (hh ⟨_, hplus⟩ M hM (Iso.refl _)).1

set_option maxHeartbeats 1500000 in
-- Expand the cached derived comparison arrows within this calculation.
private theorem gamma_comparison (P : WeilConjectures.PurityFiniteSetting.{u})
    (T : Scheme.{u}) [IsNoetherian T] (b : ℕ)
    (hA : ((P.coefficients.l ^ (b + 1) : ℕ) : Ring P) = 0)
    (aT : T ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aT] [QuasiCompact aT] [IsSeparated aT]
    (hT : IsUnit ((P.coefficients.l ^ (b + 1) : ℕ) : Γ(T, ⊤)))
    (M : Etale.DerivedCategoryModule (Ring P) T)
    (hM : Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} (Ring P)) T M)
    (hplus : DerivedCategory.TStructure.t.plus
      ((VectorIntegrationSite.comparison (Ring P) T).obj M)) :
    gammaCoordinates T P b hA aT M hM hplus =
      (VectorIntegrationSite.comparison (Ring P) (AffineSpace PUnit.{u + 1} T)).map
        ((CoordinateLine.comparison (Ring P) (P.coefficients.l ^ (b + 1)) hA T
          (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) hT).hom.app M) ≫
        boundedSiteRho (Ring P) (compact (Ring P) T).rightAdjoint M := by
  have he := gamma_normalized_equation P T b hA aT hT M hM hplus
  unfold gammaCoordinates
  rw [he]
  unfold CoordinateLine.comparedConjugate
  simp only [Iso.refl_hom, Category.assoc,
    Iso.hom_inv_id_assoc, Functor.map_comp]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id]
  simp only [CategoryTheory.Functor.map_id, sfFiniteExceptionalAt,
    Functor.comp_obj, Category.id_comp, Category.comp_id]

set_option linter.auxLemma false in
attribute [local instance 1] Etale.DerivedCategoryModule._proof_1
  Etale.DerivedCategoryModule._proof_2 Etale.ordinaryFiniteDerivedCategoryInstance

attribute [local implicit_reducible] proComposition middleUnit boundedSiteRho proClosed
attribute [local irreducible] derivedComparisonAdjunction Functor.rightAdjoint
  exceptionalComposition

attribute [local irreducible] _root_.instCategoryDerivedCategory

section

set_option quotPrecheck false

variable (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u})
variable (M : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)))

local notation "C" => VectorIntegrationSite.comparison A T
local notation "CX" => VectorIntegrationSite.comparison A (AffineSpace PUnit T)
local notation "UX" =>
  (comparisonLowerStar (ModuleCat A)
    (AffineSpace PUnit T)).rightDerivedFunctor
local notation "U" => (comparisonLowerStar (ModuleCat A) T).rightDerivedFunctor
local notation "R" => (compact A T).rightAdjoint
local notation "S" => (closedImage A T).rightAdjoint
local notation "adj" => derivedComparisonAdjunction (ModuleCat A) T
local notation "adjX" =>
  derivedComparisonAdjunction (ModuleCat A) (AffineSpace PUnit T)
local notation "β" => (adjX).unit.app ((R).obj ((U).obj ((C).obj M)))

set_option maxHeartbeats 10000 in
-- Check the cached derived-functor coordinates without unfolding their constructions.
omit [Finite A] in
private theorem site_triangle :
    (C).map (X := M) (Y := (U).obj ((C).obj M)) ((adj).unit.app M) ≫
      (adj).counit.app ((C).obj M) = 𝟙 _ := by
  simpa only [Functor.comp_obj] using (adj).left_triangle_components M

set_option maxHeartbeats 10000 in
-- Check the cached derived-functor coordinates without unfolding their constructions.
private theorem site_exceptional_transport
    (V : DerivedCategory
      (Sheaf (AffineSpace PUnit.{u + 1} T).smallEtaleTopology (ModuleCat.{u + 1} A)))
    (o : M ⟶ (S).obj V) (g : V ⟶ (R).obj M)
    (he : o ≫ (S).map g ≫ (exceptionalComposition A T).hom.app M = 𝟙 M) :
    o ≫ (S).map
      (g ≫ (R).map (X := M) (Y := (U).obj ((C).obj M)) ((adj).unit.app M)) ≫
      (exceptionalComposition A T).hom.app ((U).obj ((C).obj M)) =
      (adj).unit.app M := by
  exact exceptional_equation_transport (R) (S) (exceptionalComposition A T)
    (N := (U).obj ((C).obj M)) o g he ((adj).unit.app M)

-- Reduce only identity and composite functors at object projections.
-- Other chosen derived functors stay folded during the structural congruence proof.
private meta def normalizeComparisonHeadAux (fuel : Nat) (e : Lean.Expr) :
    Lean.MetaM Lean.Expr := do
  let e ← Lean.instantiateMVars e
  match fuel with
  | 0 => pure e
  | n + 1 =>
    let e ← Lean.Meta.withReducible <| Lean.Meta.whnf e
    let f := e.getAppFn
    if f.isConstOf ``CategoryTheory.Functor.id || f.isConstOf ``CategoryTheory.Functor.comp then
      let f ← Lean.Meta.deltaExpand f fun name ↦
        name == ``CategoryTheory.Functor.id || name == ``CategoryTheory.Functor.comp
      normalizeComparisonHeadAux n (Lean.mkAppN f e.getAppArgs).headBeta
    else if let .proj structName idx arg := f then
      let arg' ← normalizeComparisonHeadAux n arg
      if arg' == arg then return e
      normalizeComparisonHeadAux n (Lean.mkAppN (.proj structName idx arg') e.getAppArgs)
    else
      pure e

private meta def normalizeComparisonHead (e : Lean.Expr) : Lean.MetaM Lean.Expr :=
  normalizeComparisonHeadAux 50 e

-- Build ordinary heterogeneous congruence proofs with every argument explicit.
-- Definitional equality of a whole chosen functor can otherwise unfold large localization data.
-- Only closed congruence proofs may be reused across local proof contexts.
private meta def structuralComparisonCongr
    (cache : IO.Ref (Array (Lean.Expr × Nat × Bool × Lean.Meta.CongrTheorem)))
    (fixIdentical : Bool) (fuel : Nat) (g : Lean.MVarId) :
    Lean.MetaM (List Lean.MVarId) := g.withContext do
  let g ← g.iffOfEq
  let ty ← Lean.instantiateMVars (← g.getType)
  if let some (_, a, b) := ty.consumeMData.eq? then
    if a.cleanupAnnotations == b.cleanupAnnotations then
      g.assign (← Lean.Meta.mkEqRefl a)
      return []
  if let some (_, a, _, b) := ty.consumeMData.heq? then
    if a.cleanupAnnotations == b.cleanupAnnotations then
      g.assign (← Lean.Meta.mkHEqRefl a)
      return []
  match fuel with
  | 0 => return [g]
  | n + 1 =>
    if ty.consumeMData.isForall then
      let (_, h) ← g.intro1
      return ← structuralComparisonCongr cache fixIdentical n h
    let goal ← g.eqOfHEq
    if ← goal.proofIrrelHeq then return []
    let gt ← Lean.instantiateMVars (← goal.getType)
    let some (_, lhs, _, rhs) := gt.consumeMData.heq? | return [goal]
    let lhs ← normalizeComparisonHead lhs.cleanupAnnotations
    let rhs ← normalizeComparisonHead rhs.cleanupAnnotations
    if lhs == rhs then
      goal.assign (← Lean.Meta.mkHEqRefl lhs)
      return []
    let goal ← Lean.Meta.withTransparency .default <|
      goal.change (← Lean.Meta.mkHEq lhs rhs)
    let xs := lhs.getAppArgs
    let ys := rhs.getAppArgs
    if xs.isEmpty || xs.size != ys.size then return [goal]
    let f := lhs.getAppFn
    let f' := rhs.getAppFn
    let info ← Lean.Meta.getFunInfoNArgs f xs.size
    let fixed := (xs.zip ys).map fun (x, y) ↦ fixIdentical && x == y
    let sameFun := f == f'
    let fType ← Lean.Meta.inferType f
    let saved ← cache.get
    let cthm ← match saved.find? (fun (t, k, same, _) ↦
        t == fType && k == xs.size && same == sameFun) with
      | some (_, _, _, cthm) => pure cthm
      | none =>
        let cthm ← Lean.Meta.mkRichHCongr (forceHEq := true) fType info
          (fixedFun := sameFun) (fixedParams := fixed)
        if !cthm.proof.hasFVar && !cthm.proof.hasMVar then
          cache.modify fun saved ↦ saved.push (fType, xs.size, sameFun, cthm)
        pure cthm
    let (ct, cp) := if sameFun then
      (cthm.type.bindingBody!.instantiate1 f, cthm.proof.beta #[f])
      else (cthm.type.bindingBody!.bindingBody!.instantiateRev #[f, f'],
        cthm.proof.beta #[f, f'])
    let goal ← goal.assert (← Lean.mkFreshUserName `structural_congr) ct cp
    let (id, goal) ← goal.intro1P
    let gs ← Lean.Meta.withReducible <|
      goal.apply (Lean.mkFVar id) {synthAssignedInstances := false}
    let mut rest := []
    for h in gs do
      let h ← h.tryClear id
      rest := rest ++ (← structuralComparisonCongr cache fixIdentical n h)
    return rest

set_option maxHeartbeats 1500000 in
-- Normalize the comparison functor before taking its object and morphism projections.
private theorem site_composition
    (V : DerivedCategory
      (Sheaf (AffineSpace PUnit.{u + 1} T).smallEtaleTopology (ModuleCat.{u + 1} A)))
    (o : M ⟶ (closedImage A T).rightAdjoint.obj V)
    (g : V ⟶ (compact A T).rightAdjoint.obj M)
    (he : o ≫ (closedImage A T).rightAdjoint.map g ≫
      (exceptionalComposition A T).hom.app M = 𝟙 M)
    (hunit : IsIso (middleUnit A T ((VectorIntegrationSite.comparison A T).obj M))) :
    (VectorIntegrationSite.comparison A T).map o ≫
      boundedSiteRho A (closedImage A T).rightAdjoint V ≫
      (proClosed A T).map
        ((VectorIntegrationSite.comparison A (AffineSpace PUnit.{u + 1} T)).map g ≫
          boundedSiteRho A (compact A T).rightAdjoint M) ≫
      proComposition A T _ hunit = 𝟙 _ := by
  have : IsIso (middleUnit A T ((VectorIntegrationSite.comparison A T).obj M)) := hunit
  rw [proComposition]
  dsimp only [proClosed, boundedSiteRho, Functor.comp_map]
  unfold middleUnit
  simp only [← Functor.map_comp_assoc, ← Functor.map_comp]
  rw [unit_cancel_formula]
  have h := (congrArg (fun f ↦ (C).map f ≫ (adj).counit.app ((C).obj M))
    (site_exceptional_transport A T M V o g he)).trans (site_triangle A T M)
  convert (config := {closePre := false, closePost := false}) h using 0
  run_tac
    let cache ← IO.mkRef #[]
    let gs ← structuralComparisonCongr cache false 500 (← Lean.Elab.Tactic.getMainGoal)
    Lean.Elab.Tactic.replaceMainGoal gs
  all_goals rfl

end

set_option maxHeartbeats 1500000 in
-- Expand the cached derived comparison arrows within this calculation.
private theorem pro_of_ordinary (P : WeilConjectures.PurityFiniteSetting.{u})
    (T : Scheme.{u}) [IsNoetherian T] (b : ℕ)
    (hA : ((P.coefficients.l ^ (b + 1) : ℕ) : Ring P) = 0)
    (aT : T ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aT] [QuasiCompact aT] [IsSeparated aT]
    (hT : IsUnit ((P.coefficients.l ^ (b + 1) : ℕ) : Γ(T, ⊤)))
    (hI : (sectionMap T).ker.IsInvertible)
    (M : Etale.DerivedCategoryModule (Ring P) T)
    (hM : Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} (Ring P)) T M)
    (hpf : IsIso (closedProjection (Ring P) T M))
    (ho : IsIso (ordinaryOrientation (Ring P) T (P.coefficients.l ^ (b + 1))
      (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) hA hT hI M hpf))
    (he : ordinaryOrientation (Ring P) T (P.coefficients.l ^ (b + 1))
        (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) hA hT hI M hpf ≫
      (closedImage (Ring P) T).rightAdjoint.map
        ((CoordinateLine.comparison (Ring P) (P.coefficients.l ^ (b + 1)) hA T
          (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) hT).hom.app M) ≫
      (exceptionalComposition (Ring P) T).hom.app M = 𝟙 _) :
    ∃ (hplus : DerivedCategory.TStructure.t.plus
        ((VectorIntegrationSite.comparison (Ring P) T).obj M))
      (hunit : IsIso (middleUnit (Ring P) T
        ((VectorIntegrationSite.comparison (Ring P) T).obj M))),
      IsIso (proOrientation T P b hA hT hI M hpf) ∧
      IsIso (gammaCoordinates T P b hA aT M hM hplus) ∧
      (proOrientation T P b hA hT hI M hpf ≫
        (proClosed (Ring P) T).map (gammaCoordinates T P b hA aT M hM hplus) ≫
        proComposition (Ring P) T _ hunit = 𝟙 _) := by
  let C := VectorIntegrationSite.comparison (Ring P) T
  let U := (comparisonLowerStar (ModuleCat.{u + 1} (Ring P)) T).rightDerivedFunctor
  let R := (compact (Ring P) T).rightAdjoint
  let G := CoordinateLine.right (Ring P) (P.coefficients.l ^ (b + 1)) hA T
  let g := CoordinateLine.comparison (Ring P) (P.coefficients.l ^ (b + 1)) hA T
    (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) hT
  let a := derivedComparisonAdjunction (ModuleCat.{u + 1} (Ring P)) T
  let ax := derivedComparisonAdjunction (ModuleCat.{u + 1} (Ring P))
    (AffineSpace PUnit.{u + 1} T)
  have hG : DerivedCategory.TStructure.t.plus (G.obj M) :=
    DerivedCategory.TStructure.t.plus.prop_of_iso (CoordinateLine.sourceCoordinates P T b hA M)
      (etaleSource_plus P.coefficients.l P.extension (P.level - 1) T b hA M hM)
  have hη : IsIso (a.unit.app M) :=
    isIso_derivedComparisonAdjunction_unit_app (ModuleCat.{u + 1} (Ring P)) T M hM.1.1.1
  have hR : DerivedCategory.TStructure.t.plus (R.obj (U.obj (C.obj M))) :=
    DerivedCategory.TStructure.t.plus.prop_of_iso
      (g.app M ≪≫ R.mapIso (asIso (a.unit.app M))) hG
  have hmiddle : IsIso (middleUnit (Ring P) T (C.obj M)) :=
    isIso_derivedComparisonAdjunction_unit_app (ModuleCat.{u + 1} (Ring P))
      (AffineSpace PUnit.{u + 1} T) _ hR
  have hρ : IsIso (ax.unit.app (G.obj M)) :=
    isIso_derivedComparisonAdjunction_unit_app (ModuleCat.{u + 1} (Ring P))
      (AffineSpace PUnit.{u + 1} T) _ hG
  let hplus := comparison_plus (Ring P) T M hM.1.1.1
  refine ⟨hplus, hmiddle, ?_, ?_, ?_⟩
  · have := ho
    unfold proOrientation boundedSiteRho
    infer_instance
  · rw [gamma_comparison P T b hA aT hT M hM hplus]
    unfold boundedSiteRho
    infer_instance
  · rw [gamma_comparison P T b hA aT hT M hM hplus]
    simpa only [proOrientation, Category.assoc] using
      site_composition (Ring P) T M (G.obj M)
        (ordinaryOrientation (Ring P) T (P.coefficients.l ^ (b + 1))
          (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) hA hT hI M hpf)
        (g.hom.app M) he hmiddle

set_option maxHeartbeats 1500000 in
-- Assemble the finite-site witnesses and their derived identities.
/-- The finite-site coordinate normalization transports the Cartier, ordinary, and
coprojection normalizations to the pro-etale site.

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-an/
cor-pur-affine-space-zero-section-purity.proof.md, rank-one supported Cartier
normalization, even twists and finite etale-origin transport.
(blueprint: lem-pur-coordinate-section-site-transport)

Proof:
1. Apply cartier_kummer_map to the zero divisor. Its supported-constant unit is epic, so the
   normalized source comparison is independent of the annihilating exponent. Boundary uniqueness
   identifies its ordinary family with ordinaryClass. Uniqueness of the root-normalized comparison
   identifies each target with twistComparison. Apply Ext.hom to the realization equation and
   cancel the canonical exact-image/single and comparison/single isomorphisms to obtain
   CartierRealization with exactly cartierSource and twistDerived.
2. The finite Tate powers trivialize on an etale cover. Descend finite local constancy and hence
   constructibility; their flatness gives Tor amplitude [0,0] in degree zero. Even shifts preserve
   bounded constructibility and finite Tor amplitude. The literal coefficient unit is isomorphic
   to the zeroth Tate object by the shift-zero isomorphism.
3. Projection-formula naturality, naturality of the section pullback comparison, and right-unit
   naturality show closedProjection is natural in its coefficient. Invert that square and use
   tensor interchange to obtain naturality of tensorSupported; adjunction transports this to
   ordinaryOrientation. Thus the ordinary exceptional equation at Tate degree zero transports
   along the shift-zero isomorphism to the literal unit. CoprojectionNormalization supplies its
   proper-projection isomorphism. Its exceptional equation also proves that ordinaryOrientation is
   invertible.
4. Use the normalized coordinate-line adjunction to identify gammaCoordinates with comparison of
   the ordinary comparison map followed by boundedSiteRho. Apply the already-proved adopted-
   library theorem isIso_derivedComparisonAdjunction_unit_app: the actual comparison unit is
   invertible on bounded-below ordinary objects. Transport boundedness through sourceCoordinates,
   the ordinary right-adjoint comparison, and the invertible base comparison unit to get the
   specified middleUnit isomorphism. Expand proOrientation, proClosed, boundedSiteRho, and
   proComposition. Unit naturality cancels the middle unit; naturality of exceptionalComposition
   reduces the result to comparison of the assumed ordinary exceptional equation followed by the
   base unit. The left triangle identity cancels that unit against the comparison counit. Functors
   preserve the exhibited isomorphisms. Apply this calculation to each Tate input and to the
   literal unit.
-/
theorem coordinateSectionSiteTransport
    (P : WeilConjectures.PurityFiniteSetting.{u}) (T : Scheme.{u})
    (aT : T ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aT] [QuasiCompact aT] [IsSeparated aT] [IsNoetherian T]
    (hI : (sectionMap T).ker.IsInvertible) :
    CartierRealization T P aT hI ∧
    ∀ (b : ℕ) (hA : ((P.coefficients.l ^ (b + 1) : ℕ) : Ring P) = 0)
      (hT : IsUnit ((P.coefficients.l ^ (b + 1) : ℕ) : Γ(T, ⊤))),
      OrdinaryNormalization (Ring P) T (P.coefficients.l ^ (b + 1))
        (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) hA hT hI →
      CoprojectionNormalization (Ring P) T (P.coefficients.l ^ (b + 1))
        (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) hA hT hI →
      ProNormalization T P b hA aT hT hI := by
  classical
  refine ⟨cartier_realization P T aT hI, ?_⟩
  intro b hA hT hOrd hCop M hInput
  rcases hInput with rfl | ⟨r, rfl⟩
  · obtain ⟨hpf, ho, he⟩ := unit_ordinary (Ring P) T _
      (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) hA hT hI hOrd hCop
    let e := unit_tate_iso (Ring P) T (P.coefficients.l ^ (b + 1)) hA
    have hM := (Etale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (Ring P)) T).prop_of_iso e.symm
        (tate_properties (Ring P) T _
          (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) hA hT 0)
    obtain ⟨hplus, hunit, ho', hg, he'⟩ :=
      pro_of_ordinary P T b hA aT hT hI _ hM hpf ho he
    exact ⟨hM, hplus, hpf, hunit, ho', hg, he'⟩
  · obtain ⟨hpf, ho, he⟩ := ordinary_tate_data (Ring P) T _
      (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) hA hT hI hOrd r
    have hM := tate_properties (Ring P) T _
      (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) hA hT r
    obtain ⟨hplus, hunit, ho', hg, he'⟩ :=
      pro_of_ordinary P T b hA aT hT hI _ hM hpf ho he
    exact ⟨hM, hplus, hpf, hunit, ho', hg, he'⟩

end AlgebraicGeometry.ProEtale.CoordinateSectionNormalization
