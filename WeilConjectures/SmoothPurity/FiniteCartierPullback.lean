/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.OrdinarySupportedCartierKummerSupplement
public import WeilConjectures.AlgebraicGeometry.GeoCartierCanonicalClass
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModulesSupplement
public import WeilConjectures.AlgebraicGeometry.ComparisonPullbackExact
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTwistLine
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateSheaf
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedTensorPullback
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackBase
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLinePullback
public import WeilConjectures.EtaleCohomology.TateTwist.RootsOfUnityPullback
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTensorFamily
public import WeilConjectures.CategoryTheory.NormalizedSignedTensorPowers
public import WeilConjectures.CategoryTheory.Monoidal.IntTensorFamily
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.IntTensorFamilyIso
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLocalLine
public import WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.LocallyTrivialInverse
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.MonoidalComp
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackRest
public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import WeilConjectures.AlgebraicGeometry.GeoCartierCycleClassDefsSupplement
public import WeilConjectures.AlgebraicGeometry.GeoCartierSourceComparison
public import WeilConjectures.AlgebraicGeometry.EffectiveCartier
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteFirstChern
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1KummerSupplement
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteClassArbitraryBase
public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBoundaryComparison
public import WeilConjectures.AlgebraicGeometry.EtaleModuleInjectiveForgetAcyclic
public import WeilConjectures.CategoryTheory.Sites.SheafCohomologyRightDerived
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Arrows
public import WeilConjectures.AlgebraicGeometry.RelativeKummerExchangeGeneratorsSupplement
public import WeilConjectures.AlgebraicGeometry.EtaleSinglePullbackComparisonsSupplement
public import WeilConjectures.AlgebraicGeometry.ProperProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.AlgebraicGeometry.EtaleDerivedTensorSymmetrySupplement
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.Defs.Filter
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.AlgebraicGeometry.ExactUnboundedExchange
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.SixFunctors.Etale.Derived.Shift
public import WeilConjectures.SixFunctors.Etale.Derived.ReductionConservative
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteChernPullback
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteCoefficientRecords
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Additive
public import WeilConjectures.AlgebraicGeometry.FiniteP1ChernMapBaseChange
public import WeilConjectures.AlgebraicGeometry.Sites.GmPicardPullback
public import WeilConjectures.CategoryTheory.Abelian.Ext.MapExactFunctorConj
public import WeilConjectures.AlgebraicGeometry.SupportedDerivedUnitForget
public import WeilConjectures.AlgebraicGeometry.OrdinarySupportedKummerSystemSupplement
public import WeilConjectures.ConstructibleSheaf.FinitePushforward.ConstantUnit
public import WeilConjectures.CategoryTheory.DerivedSingleUnitExact
public import WeilConjectures.CategoryTheory.DerivedSingleUnit
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import WeilConjectures.SixFunctors.OpenClosed.Exact
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
import WeilConjectures.AlgebraicGeometry.CartierClosedExchangeComparison
import WeilConjectures.AlgebraicGeometry.SupportedKummerBoundaryPullback
import WeilConjectures.AlgebraicGeometry.ComparisonPullbackCoherence
import WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparison
import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
import Mathlib.AlgebraicGeometry.Pullbacks
import WeilConjectures.SixFunctors.BaseChange.Square
import WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparisonSupplement
import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStar
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.AlgebraicGeometry.PrincipalCartierPoleLocalization
import WeilConjectures.AlgebraicGeometry.KummerLocalizationSplice
import WeilConjectures.AlgebraicGeometry.PrincipalTorsorYonedaSign
import WeilConjectures.AlgebraicGeometry.SupportedKummerIntegralEquation
import WeilConjectures.AlgebraicGeometry.EtaleSupportedIntegralDerivedUnit
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.ExactFunctorDerivedUnit
import WeilConjectures.AlgebraicGeometry.ResidueQuotientDerivedUnit
import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModulesSupplement
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Data.ZMod.Basic
import WeilConjectures.Mathlib.CategoryTheory.Sites.Whiskering
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.DerivedBaseChange
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Reduction
import WeilConjectures.AlgebraicGeometry.DivisibleExtensionDerivedReductionSupplement
import WeilConjectures.Mathlib.Algebra.Category.Grp.ZModuleEquivalence
import WeilConjectures.SixFunctors.BaseChange.DerivedForget
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Coinduce
import Mathlib.CategoryTheory.Abelian.ShortExact
import WeilConjectures.AlgebraicGeometry.SupportedKummerScalarSource
import WeilConjectures.AlgebraicGeometry.OrdinarySupportedKummerScalarSupplement
import WeilConjectures.AlgebraicGeometry.SupportedKummerScalarMaps
import WeilConjectures.AlgebraicGeometry.OrdinarySupportedKummerBoundarySupplement
import WeilConjectures.SixFunctors.BaseChange.RestrictScalars
import WeilConjectures.AlgebraicGeometry.SupportedKummerScalarDerived
import WeilConjectures.CategoryTheory.FlatScalarUnit
import WeilConjectures.CategoryTheory.ExactDegreeZeroSupplement
import WeilConjectures.CategoryTheory.ExactRightDerivedAdjointKFlatRepresentative
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import WeilConjectures.CategoryTheory.DerivedCategory.KFlatAcyclic
import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfShape
import WeilConjectures.AlgebraicGeometry.FiniteOrdinaryScalarUnit
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import WeilConjectures.SixFunctors.Finite.Stalk
import Mathlib.CategoryTheory.Sites.Adjunction
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
import Mathlib.Algebra.Category.ModuleCat.Products
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1KummerSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RestrictScalars
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
import Mathlib.AlgebraicGeometry.Scheme
import WeilConjectures.AlgebraicGeometry.ScalarUniversalDerivedUnit
import WeilConjectures.AlgebraicGeometry.SupportedIntegralResidueSequence
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
import WeilConjectures.SixFunctors.Finite.Exact
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import WeilConjectures.AlgebraicGeometry.ScalarUnitExt
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import WeilConjectures.SixFunctors.BaseChange.DerivedPasting.Identity
import WeilConjectures.ConstructibleSheaf.UpperStarConstantSheafComp

/-!
# Finite Cartier class pullback naturality

Source: blueprint latest, sec-smooth-purity/sk-prop-an/thm-pur-rank-one-thom.proof.md,
Step 3: base change, using the finite-level Cartier/Kummer class and its pullback
naturality (blueprint: lem-pur-finite-cartier-pullback).

The theorem records the ordinary supported Kummer pullback square, its identity and
composition coherence, and the corresponding pro-etale square.  The canonical class is
exactly `geoCartierCanonicalClass`; no second definition of that class is introduced.
The final local-chart clause uses the signed relative-cone convention and records the
negative Kummer boundary of a local equation.  No flatness or Noetherian hypothesis on
the pullback scheme is used.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

private theorem exact_functor_square_local
    {C D E F : Type*} [Category C] [Abelian C] [Category D] [Abelian D]
    [Category E] [Abelian E] [Category F] [Abelian F]
    [HasExt C] [HasExt D] [HasExt E] [HasExt F] [EnoughInjectives C]
    (V : C ⥤ E) (U : E ⥤ F) (H : C ⥤ D) (W : D ⥤ F)
    [V.Additive] [U.Additive] [H.Additive] [W.Additive]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits W] [PreservesFiniteColimits W]
    (s : V ⋙ U ≅ H ⋙ W) {X Y : C} (κ : Ext X Y 2) :
    (Ext.mk₀ (s.hom.app X)).comp ((κ.mapExactFunctor H).mapExactFunctor W)
        (zero_add 2) = ((κ.mapExactFunctor V).mapExactFunctor U).comp
          (Ext.mk₀ (s.hom.app Y)) (add_zero 2) := by
  have h₁ := Ext.mapExactFunctor_mapExactFunctor_of_iso V U (V ⋙ U) (Iso.refl _) κ
  simp only [Iso.refl_inv, Iso.refl_hom, NatTrans.id_app,
    Ext.mk₀_id_comp, Ext.comp_mk₀_id] at h₁
  have h₂ := Ext.mapExactFunctor_mapExactFunctor_of_iso H W (V ⋙ U) s κ
  rw [h₂, ← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀,
    Iso.hom_inv_id_app, Ext.mk₀_id_comp, h₁]

private theorem transport_ext_square_local
    {C D E F : Type*} [Category C] [Abelian C] [Category D] [Abelian D]
    [Category E] [Abelian E] [Category F] [Abelian F]
    [HasExt C] [HasExt D] [HasExt E] [HasExt F] [EnoughInjectives C]
    (V : C ⥤ E) (U : E ⥤ F) (H : C ⥤ D) (W : D ⥤ F)
    [V.Additive] [U.Additive] [H.Additive] [W.Additive]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits W] [PreservesFiniteColimits W]
    (s : V ⋙ U ≅ H ⋙ W) {X Y : C} {X' Y' : D} {P : E} {Q : F}
    (a : V.obj X ≅ P) (b : W.obj X' ≅ Q)
    (e : H.obj X ⟶ X') (l : H.obj Y ⟶ Y') (χ : U.obj P ⟶ Q)
    (hχ : U.map a.hom ≫ χ = s.hom.app X ≫ W.map e ≫ b.hom)
    (κ : Ext X Y 2) (κ' : Ext X' Y' 2)
    (hκ : (Ext.mk₀ e).comp κ' (zero_add 2) =
      (κ.mapExactFunctor H).comp (Ext.mk₀ l) (add_zero 2)) :
    (Ext.mk₀ χ).comp ((Ext.mk₀ b.inv).comp (κ'.mapExactFunctor W)
      (zero_add 2)) (zero_add 2) =
      (((Ext.mk₀ a.inv).comp (κ.mapExactFunctor V) (zero_add 2)).mapExactFunctor U).comp
        (Ext.mk₀ (s.hom.app Y ≫ W.map l)) (add_zero 2) := by
  have h := congrArg (fun z : Ext (H.obj X) Y' 2 =>
      (Ext.mk₀ (s.hom.app X)).comp (z.mapExactFunctor W) (zero_add 2)) hκ
  simp only [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀] at h
  rw [← Ext.comp_assoc_of_third_deg_zero,
    exact_functor_square_local V U H W s κ, Ext.comp_assoc_of_third_deg_zero,
    Ext.mk₀_comp_mk₀] at h
  simp only [Ext.mk₀_comp_mk₀_assoc] at h
  have h' := congrArg (fun z : Ext (U.obj (V.obj X)) (W.obj Y') 2 =>
      (Ext.mk₀ (U.map a.inv)).comp z (zero_add 2)) h
  have hχ' : U.map a.inv ≫ s.hom.app X ≫ W.map e = χ ≫ b.inv := by
    have hh := congrArg (fun f => U.map a.inv ≫ f ≫ b.inv) hχ
    simp only [← Category.assoc, ← Functor.map_comp, a.inv_hom_id] at hh
    rw [U.map_id P, Category.id_comp] at hh
    simpa only [Category.assoc, b.hom_inv_id, Category.comp_id] using hh.symm
  simpa only [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Ext.mk₀_comp_mk₀_assoc, Ext.comp_assoc_of_third_deg_zero,
    Ext.mk₀_comp_mk₀, hχ'] using h'

private theorem pro_cartier_pullback_for_transport
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA) :
    ∀ {D T D' T' : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]
      (i' : D' ⟶ T') [IsClosedImmersion i'] (v : T' ⟶ T) (w : D' ⟶ D)
      (sq : IsPullback w i' i v) (hI : i.ker.IsInvertible)
      (hI' : i'.ker.IsInvertible) (hT : IsUnit (N : Γ(T, ⊤)))
      (hT' : IsUnit (N : Γ(T', ⊤))),
      IsIso (ProEtale.geoCartierExchange A i i' v w sq.toCommSq) ∧
      (Ext.mk₀ (ProEtale.geoCartierExchange A i i' v w sq.toCommSq)).comp
          (ProEtale.geoCartierCanonicalClass A N hN hA i' hI' hT') (zero_add 2) =
        ((ProEtale.geoCartierCanonicalClass A N hN hA i hI hT).mapExactFunctor
          (ProEtale.upperStar (ModuleCat.{u + 1} A) v)).comp
          (Ext.mk₀ (ProEtale.geoCartierLinePullback A N hA t v hT).hom)
          (add_zero 2) := by
  intro D T D' T' i _ i' _ v w sq hI hI' hT hT'
  have he : IsIso (Etale.supportedConstantExchange A i i' v w sq.toCommSq) := by
    let := isIso_baseChangeMap_of_isFinite (ModuleCat.{u + 1} A) sq
    unfold Etale.supportedConstantExchange
    infer_instance
  have hx := AlgebraicGeometry.ProEtale.geoCartier_closed_exchange_comparison A i i' v w sq.toCommSq
  refine ⟨?_, ?_⟩
  · have : IsIso ((ProEtale.upperStar (ModuleCat.{u + 1} A) v).map
        (ProEtale.geoCartierSourceComparison A i) ≫
          ProEtale.geoCartierExchange A i i' v w sq.toCommSq) := by
      rw [hx]
      infer_instance
    exact IsIso.of_isIso_comp_left
      ((ProEtale.upperStar (ModuleCat.{u + 1} A) v).map
        (ProEtale.geoCartierSourceComparison A i)) _
  · have hκ := geoCartierEtaleClass_spec A N hN hA i hI hT |>.1
    have hκ' := geoCartierEtaleClass_spec A N hN hA i' hI' hT' |>.1
    have ho := supported_kummer_boundary_pullback T N hN A hA hT i hI
      (geoCartierEtaleClass A N hN hA i hI hT) hκ t i' v w sq hI'
      (geoCartierEtaleClass A N hN hA i' hI' hT') hκ'
    unfold ProEtale.geoCartierCanonicalClass ProEtale.geoCartierLinePullback
    exact transport_ext_square_local
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T)
      (ProEtale.upperStar (ModuleCat.{u + 1} A) v)
      (Etale.upperStar (ModuleCat.{u + 1} A) v)
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T')
      (ProEtale.comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) v)
      (asIso (ProEtale.geoCartierSourceComparison A i))
      (asIso (ProEtale.geoCartierSourceComparison A i'))
      (Etale.supportedConstantExchange A i i' v w sq.toCommSq)
      (t.line v hT).hom (ProEtale.geoCartierExchange A i i' v w sq.toCommSq)
      hx _ _ ho

end AlgebraicGeometry.Etale
namespace AlgebraicGeometry.ProEtale
variable (A : Type (u + 1)) [CommRing A]

private theorem comparison_comp_local {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) (f ≫ g)).hom.app F ≫
        (comparisonUpperStar (ModuleCat.{u + 1} A) X).map
          ((Etale.upperStarComp (ModuleCat.{u + 1} A) f g).hom.app F) =
      (upperStarComp (ModuleCat.{u + 1} A) f g).hom.app _ ≫
        (upperStar (ModuleCat.{u + 1} A) f).map
          ((comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) g).hom.app F) ≫
        (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) f).hom.app
          ((Etale.upperStar (ModuleCat.{u + 1} A) g).obj F) := by
  have h := (comparison_pullback_coherent.2.2 A).2.1 X Y Z f g F
  change (comparisonUpperStar (ModuleCat.{u + 1} A) X).map
      ((Etale.upperStarComp (ModuleCat.{u + 1} A) f g).hom.app F) ≫
    (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) f).inv.app
      ((Etale.upperStar (ModuleCat.{u + 1} A) g).obj F) ≫
    (upperStar (ModuleCat.{u + 1} A) f).map
      ((comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) g).inv.app F) =
    (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) (f ≫ g)).inv.app F ≫
      (upperStarComp (ModuleCat.{u + 1} A) f g).hom.app _ at h
  apply (cancel_epi
    ((comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) (f ≫ g)).inv.app F)).mp
  simp only [Iso.inv_hom_id_app_assoc]
  rw [← reassoc_of% h]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app, Category.comp_id]

private theorem comparison_id_local (T : Scheme.{u})
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) (𝟙 T)).hom.app F ≫
      (comparisonUpperStar (ModuleCat.{u + 1} A) T).map
        ((Etale.upperStarId (ModuleCat.{u + 1} A) T).hom.app F) =
      (upperStarId (ModuleCat.{u + 1} A) T).hom.app _ := by
  have h := (comparison_pullback_coherent.2.2 A).1 T F
  change (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) (𝟙 T)).inv.app F ≫
    (upperStarId (ModuleCat.{u + 1} A) T).hom.app _ =
      (comparisonUpperStar (ModuleCat.{u + 1} A) T).map
        ((Etale.upperStarId (ModuleCat.{u + 1} A) T).hom.app F) at h
  rw [← h, ← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]

end AlgebraicGeometry.ProEtale
namespace AlgebraicGeometry.Etale

private theorem constant_id_local (A : Type (u + 1)) [CommRing A]
    (T : Scheme.{u}) :
    (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) (𝟙 T)).hom.app
      (ModuleCat.of A A) =
    (upperStarId (ModuleCat.{u + 1} A) T).hom.app (ordinaryFiniteConstant A T) := by
  let adj := constantSheafAdj T.smallEtaleTopology (ModuleCat.{u + 1} A)
    terminalIsTerminal
  let adjId := upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) (𝟙 T)
  let e := lowerStarCompSheafSectionsTerminalIso (ModuleCat.{u + 1} A) (𝟙 T)
  have h : (upperStarId (ModuleCat.{u + 1} A) T).hom.app
      ((constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A)) =
      (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) (𝟙 T)).hom.app
        (ModuleCat.of A A) := by
    apply (((adj.comp adjId).ofNatIsoRight e).homEquiv (ModuleCat.of A A) _).injective
    change _ = (((adj.comp adjId).ofNatIsoRight e).homEquiv (ModuleCat.of A A) _)
      ((((adj.comp adjId).ofNatIsoRight e).leftAdjointUniq adj).hom.app (ModuleCat.of A A))
    rw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
    rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv]
    change adj.homEquiv (ModuleCat.of A A) _ (adjId.homEquiv _ _
      ((upperStarId (ModuleCat.{u + 1} A) T).hom.app
        ((constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A)))) ≫
      e.hom.app _ = _
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    dsimp only [adjId]
    rw [upperStarId_hom_app_unit_app]
    have ht : PreservesTerminal.iso (Scheme.Hom.Etale (𝟙 T)) =
        (MorphismProperty.Over.pullbackId @Etale ⊤ T).app (⊤_ T.Etale) := by
      apply Iso.ext
      exact terminalIsTerminal.hom_ext _ _
    simp [e, lowerStarCompSheafSectionsTerminalIso, lowerStarId,
      GrothendieckTopology.lowerStarId, ht, ← Functor.map_comp, ← op_comp]
  exact h.symm

private theorem exchange_id_local (A : Type (u + 1)) [CommRing A]
    {D T : Scheme.{u}} (i : D ⟶ T) (sq : CommSq (𝟙 D) i i (𝟙 T)) :
    supportedConstantExchange A i i (𝟙 T) (𝟙 D) sq =
      (upperStarId (ModuleCat.{u + 1} A) T).hom.app
        ((lowerStar (ModuleCat.{u + 1} A) i).obj (ordinaryFiniteConstant A D)) := by
  unfold supportedConstantExchange
  rw [baseChangeMap_id]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.rightUnitor_hom_app, Functor.leftUnitor_inv_app, Category.id_comp,
    Iso.app_hom, Category.assoc]
  simp only [constant_id_local, ← Functor.map_comp, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id]
  erw [Category.comp_id]

private theorem exchange_comp_local (A : Type (u + 1)) [CommRing A]
    {D T D' T' D'' T'' : Scheme.{u}} (i : D ⟶ T) (i' : D' ⟶ T')
    (i'' : D'' ⟶ T'') (v : T' ⟶ T) (w : D' ⟶ D) (v₂ : T'' ⟶ T')
    (w₂ : D'' ⟶ D') (sq : CommSq w i' i v) (sq₂ : CommSq w₂ i'' i' v₂)
    (sq₁₂ : CommSq (w₂ ≫ w) i'' i (v₂ ≫ v)) :
    (upperStarComp (ModuleCat.{u + 1} A) v₂ v).hom.app
        ((lowerStar (ModuleCat.{u + 1} A) i).obj (ordinaryFiniteConstant A D)) ≫
      (upperStar (ModuleCat.{u + 1} A) v₂).map
        (supportedConstantExchange A i i' v w sq) ≫
      supportedConstantExchange A i' i'' v₂ w₂ sq₂ =
    supportedConstantExchange A i i'' (v₂ ≫ v) (w₂ ≫ w) sq₁₂ := by
  unfold supportedConstantExchange
  rw [baseChangeMap_paste_horiz_app (ModuleCat.{u + 1} A) sq sq₂ sq₁₂]
  simp only [Functor.map_comp, Iso.app_hom, Category.assoc]
  rw [reassoc_of% ((baseChangeMap (ModuleCat.{u + 1} A) sq₂).naturality
    ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) w).hom.app
      (ModuleCat.of A A)))]
  simp only [← Functor.map_comp]
  congr 3
  have hc := Scheme.upperStarConstantSheafIso_comp (ModuleCat.{u + 1} A)
    w₂ w (ModuleCat.of A A)
  apply congrArg (lowerStar (ModuleCat.{u + 1} A) i'').map
  apply (cancel_epi ((upperStarComp (ModuleCat.{u + 1} A) w₂ w).hom.app
    (ordinaryFiniteConstant A D))).mp
  simpa only [Category.assoc, Iso.hom_inv_id_app_assoc] using hc

private theorem pro_exchange_id_local (A : Type (u + 1)) [CommRing A] [Finite A]
    {D T : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]
    (sq : IsPullback (𝟙 D) i i (𝟙 T)) :
    ProEtale.geoCartierExchange A i i (𝟙 T) (𝟙 D) sq.toCommSq =
      (ProEtale.upperStarId (ModuleCat.{u + 1} A) T).hom.app
        ((ProEtale.lowerStar (ModuleCat.{u + 1} A) i).obj
          (ProEtale.geoCartierConstant A D)) := by
  apply (cancel_epi ((ProEtale.upperStar (ModuleCat.{u + 1} A) (𝟙 T)).map
    (ProEtale.geoCartierSourceComparison A i))).mp
  rw [ProEtale.geoCartier_closed_exchange_comparison A i i (𝟙 T) (𝟙 D) sq.toCommSq,
    exchange_id_local]
  rw [← Category.assoc, ProEtale.comparison_id_local]
  exact ((ProEtale.upperStarId (ModuleCat.{u + 1} A) T).hom.naturality
    (ProEtale.geoCartierSourceComparison A i)).symm

private theorem pro_exchange_comp_local (A : Type (u + 1)) [CommRing A] [Finite A]
    {D T D' T' D'' T'' : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]
    (i' : D' ⟶ T') [IsClosedImmersion i'] (i'' : D'' ⟶ T'') [IsClosedImmersion i'']
    (v : T' ⟶ T) (w : D' ⟶ D) (v₂ : T'' ⟶ T') (w₂ : D'' ⟶ D')
    (sq : IsPullback w i' i v) (sq₂ : IsPullback w₂ i'' i' v₂)
    (sq₁₂ : IsPullback (w₂ ≫ w) i'' i (v₂ ≫ v)) :
    (ProEtale.upperStarComp (ModuleCat.{u + 1} A) v₂ v).hom.app
        ((ProEtale.lowerStar (ModuleCat.{u + 1} A) i).obj
          (ProEtale.geoCartierConstant A D)) ≫
      (ProEtale.upperStar (ModuleCat.{u + 1} A) v₂).map
        (ProEtale.geoCartierExchange A i i' v w sq.toCommSq) ≫
      ProEtale.geoCartierExchange A i' i'' v₂ w₂ sq₂.toCommSq =
    ProEtale.geoCartierExchange A i i'' (v₂ ≫ v) (w₂ ≫ w) sq₁₂.toCommSq := by
  apply (cancel_epi ((ProEtale.upperStar (ModuleCat.{u + 1} A) (v₂ ≫ v)).map
    (ProEtale.geoCartierSourceComparison A i))).mp
  rw [reassoc_of% ((ProEtale.upperStarComp (ModuleCat.{u + 1} A) v₂ v).hom.naturality
    (ProEtale.geoCartierSourceComparison A i))]
  rw [← Functor.map_comp_assoc,
    ProEtale.geoCartier_closed_exchange_comparison A i i' v w sq.toCommSq]
  simp only [Functor.map_comp, Category.assoc]
  rw [ProEtale.geoCartier_closed_exchange_comparison A i' i'' v₂ w₂ sq₂.toCommSq]
  rw [reassoc_of% ((ProEtale.comparisonUpperStarCompUpperStarIso
    (ModuleCat.{u + 1} A) v₂).hom.naturality
      (supportedConstantExchange A i i' v w sq.toCommSq))]
  rw [← reassoc_of% (ProEtale.comparison_comp_local A v₂ v _)]
  simp only [← Functor.map_comp_assoc]
  rw [exchange_comp_local]
  exact (ProEtale.geoCartier_closed_exchange_comparison A i i''
    (v₂ ≫ v) (w₂ ≫ w) sq₁₂.toCommSq).symm

private theorem principal_canonical_sign_local
    (A : Type (u + 1)) [CommRing A] [Finite A] (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (U : Scheme.{u}) (f : Γ(U, ⊤))
    (hI : (U.zeroLocusSubschemeι {f}).ker.IsInvertible)
    (hU : IsUnit (N : Γ(U, ⊤)))
    (h : Set.range (U.zeroLocusSubschemeι {f}).base =
      (Set.range (U.basicOpen f).ι.base)ᶜ) :
    ProEtale.geoCartierCanonicalClass A N hN hA (U.zeroLocusSubschemeι {f}) hI hU =
      -(Ext.mk₀ (asIso (ProEtale.geoCartierSourceComparison A
        (U.zeroLocusSubschemeι {f}))).inv).comp
        ((finiteKummerLocalizationBoundary A N hA t (U.zeroLocusSubschemeι {f})
          (U.basicOpen f) h hU (U.basicOpenUnit f)).mapExactFunctor
            (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) U)) (zero_add 2) := by
  let k := U.zeroLocusSubschemeι {f}
  obtain ⟨C, hC, _, hCF⟩ := principal_torsor_yoneda_sign.{u}
  have heq := supported_kummer_integral_equation A N hA k hI hU
    (geoCartierEtaleClass A N hN hA k hI hU)
    (geoCartierEtaleClass_spec A N hN hA k hI hU).1
  have hpole := principalCartierPoleLocalization U f hI C hCF h
  have hcoef := kummerLocalizationSplice A N hA t C hC k (U.basicOpen f) h hU
    (U.basicOpenUnit f)
  have hclass : geoCartierEtaleClass A N hN hA k hI hU =
      -finiteKummerLocalizationBoundary A N hA t k (U.basicOpen f) h hU
        (U.basicOpenUnit f) := by
    apply (scalar_unit_ext_bijective (RawModuleScalarComparison.forget A U)
      (supportedIntegralGenerator A k)
      (supported_integral_derived_unit U N hN A hA k) 2).1
    dsimp only
    erw [heq, hpole]
    simpa only [← Functor.mapExtAddHom_apply, map_neg, Ext.comp_neg, Ext.neg_comp] using
      congrArg Neg.neg hcoef.symm
  unfold ProEtale.geoCartierCanonicalClass
  rw [hclass, ← Functor.mapExtAddHom_apply, map_neg, Ext.comp_neg]
  erw [Functor.mapExtAddHom_apply]

/-- Finite Cartier classes are natural under Cartier-preserving pullback, with ordinary
and pro-etale identity/composition coherence and the signed local-chart normalization.

Source: Stacks Tags 03PL and 0A45 and the relative-cone local equation;
(blueprint: lem-pur-finite-cartier-pullback).

Proof:
1. Choose the roots- and pure-tensor-normalized finite twist transport.  Apply
   `supported_kummer_boundary_pullback` to the unique normalized ordinary classes;
   finite closed base change makes the supported constant exchange invertible.
2. Apply exact comparison inverse image.  The comparison/exchange source square and
   cancellation of the canonical source isomorphisms give the pro-etale square and
   its invertible closed exchange, as in `geoCartierCanonicalClass_pullback`.
3. For an identity square the exchange is the inverse-image unitor.  The roots
   inclusion and the pure root tensors characterize the line maps, so they too are
   the identity inverse-image unitors on both sites.
4. For two squares, the adjunction mate pasting law gives the displayed exchange
   equations after the inverse-image compositor.  The roots inclusions and pure
   tensors give the line compositor equations.  Pasting the class squares therefore
   agrees with the square of the composite, on each site.
5. On an etale principal chart set W=D(f).  Multiplication by f trivializes the
   Cartier ideal, with dual frame f⁻¹ and complementary divisor section f times
   that frame.  The relative torsor Yoneda sign formula identifies the normalized
   Cartier extension with minus the localization boundary of the Kummer class of f.
6. Here κ is the unique module representative of the scalar-extended Kummer class;
   κopen is its extension by zero followed by the twist counit; and δκ is its
   splice with the actual open-closed coefficient sequence.  The coefficient
   comparison morphism intertwines its extension class with the integral splice;
   the derived scalar-unit bijection then identifies the ordinary classes.
   Exact site comparison and the canonical source comparison give β.  The last
   equation consequently states the pullback of cl_A(D) is -β=-∂κ_A(f).
No step requires smoothness, flatness of A or of the base map, or Noetherianness of
T'.  The same constructions include N=1, zero coefficients and empty schemes.
-/
theorem finite_cartier_class_pullback
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {D T : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]
    (hI : i.ker.IsInvertible) (hT : IsUnit (N : Γ(T, ⊤)))
    {D' T' : Scheme.{u}} (i' : D' ⟶ T') [IsClosedImmersion i']
    (v : T' ⟶ T) (w : D' ⟶ D) (sq : IsPullback w i' i v)
    (hI' : i'.ker.IsInvertible) (hT' : IsUnit (N : Γ(T', ⊤))) :
    ∃ t : OrdinaryFiniteTwistTransport A N hA,
      IsIso (supportedConstantExchange A i i' v w sq.toCommSq) ∧
      (Ext.mk₀ (supportedConstantExchange A i i' v w sq.toCommSq)).comp
          (geoCartierEtaleClass A N hN hA i' hI' hT') (zero_add 2) =
        ((geoCartierEtaleClass A N hN hA i hI hT).mapExactFunctor
            (upperStar (ModuleCat.{u + 1} A) v)).comp
          (Ext.mk₀ (t.line v hT).hom) (add_zero 2) ∧
      IsIso (ProEtale.geoCartierExchange A i i' v w sq.toCommSq) ∧
      (Ext.mk₀ (ProEtale.geoCartierExchange A i i' v w sq.toCommSq)).comp
          (ProEtale.geoCartierCanonicalClass A N hN hA i' hI' hT') (zero_add 2) =
        ((ProEtale.geoCartierCanonicalClass A N hN hA i hI hT).mapExactFunctor
            (ProEtale.upperStar (ModuleCat.{u + 1} A) v)).comp
          (Ext.mk₀ (ProEtale.geoCartierLinePullback A N hA t v hT).hom)
          (add_zero 2) ∧
      (∀ sqId : IsPullback (𝟙 D) i i (𝟙 T),
        supportedConstantExchange A i i (𝟙 T) (𝟙 D) sqId.toCommSq =
          (upperStarId (ModuleCat.{u + 1} A) T).hom.app
            ((lowerStar (ModuleCat.{u + 1} A) i).obj (ordinaryFiniteConstant A D)) ∧
        ProEtale.geoCartierExchange A i i (𝟙 T) (𝟙 D) sqId.toCommSq =
          (ProEtale.upperStarId (ModuleCat.{u + 1} A) T).hom.app
            ((ProEtale.lowerStar (ModuleCat.{u + 1} A) i).obj
              (ProEtale.geoCartierConstant A D))) ∧
      (t.line (𝟙 T) hT).hom =
        (upperStarId (ModuleCat.{u + 1} A) T).hom.app
          (Scheme.finiteEtaleTateLine T N A hA) ∧
      (ProEtale.geoCartierLinePullback A N hA t (𝟙 T) hT).hom =
        (ProEtale.upperStarId (ModuleCat.{u + 1} A) T).hom.app
          (ProEtale.geoCartierLine A N hA T) ∧
      (∀ {D'' T'' : Scheme.{u}} (i'' : D'' ⟶ T'') [IsClosedImmersion i'']
        (v₂ : T'' ⟶ T') (w₂ : D'' ⟶ D')
        (sq₂ : IsPullback w₂ i'' i' v₂)
        (sq₁₂ : IsPullback (w₂ ≫ w) i'' i (v₂ ≫ v)),
        (upperStarComp (ModuleCat.{u + 1} A) v₂ v).hom.app
              ((lowerStar (ModuleCat.{u + 1} A) i).obj (ordinaryFiniteConstant A D)) ≫
            (upperStar (ModuleCat.{u + 1} A) v₂).map
              (supportedConstantExchange A i i' v w sq.toCommSq) ≫
            supportedConstantExchange A i' i'' v₂ w₂ sq₂.toCommSq =
          supportedConstantExchange A i i'' (v₂ ≫ v) (w₂ ≫ w) sq₁₂.toCommSq) ∧
      (∀ {D'' T'' : Scheme.{u}} (i'' : D'' ⟶ T'') [IsClosedImmersion i'']
        (v₂ : T'' ⟶ T') (w₂ : D'' ⟶ D')
        (sq₂ : IsPullback w₂ i'' i' v₂)
        (sq₁₂ : IsPullback (w₂ ≫ w) i'' i (v₂ ≫ v)),
        (ProEtale.upperStarComp (ModuleCat.{u + 1} A) v₂ v).hom.app
              ((ProEtale.lowerStar (ModuleCat.{u + 1} A) i).obj
                (ProEtale.geoCartierConstant A D)) ≫
            (ProEtale.upperStar (ModuleCat.{u + 1} A) v₂).map
              (ProEtale.geoCartierExchange A i i' v w sq.toCommSq) ≫
            ProEtale.geoCartierExchange A i' i'' v₂ w₂ sq₂.toCommSq =
          ProEtale.geoCartierExchange A i i'' (v₂ ≫ v) (w₂ ≫ w) sq₁₂.toCommSq) ∧
      (∀ {T'' : Scheme.{u}} (v₂ : T'' ⟶ T'),
        (upperStarComp (ModuleCat.{u + 1} A) v₂ v).hom.app
              (Scheme.finiteEtaleTateLine T N A hA) ≫
            (upperStar (ModuleCat.{u + 1} A) v₂).map (t.line v hT).hom ≫
            (t.line v₂ hT').hom = (t.line (v₂ ≫ v) hT).hom ∧
        (ProEtale.upperStarComp (ModuleCat.{u + 1} A) v₂ v).hom.app
              (ProEtale.geoCartierLine A N hA T) ≫
            (ProEtale.upperStar (ModuleCat.{u + 1} A) v₂).map
              (ProEtale.geoCartierLinePullback A N hA t v hT).hom ≫
            (ProEtale.geoCartierLinePullback A N hA t v₂ hT').hom =
          (ProEtale.geoCartierLinePullback A N hA t (v₂ ≫ v) hT).hom) ∧
      (∀ (U : Scheme.{u}) (e : U ⟶ T) [Etale e] (f : Γ(U, ⊤))
        (d : U.zeroLocusSubscheme {f} ⟶ D)
        (sqf : IsPullback d (U.zeroLocusSubschemeι {f}) i e),
        let k := U.zeroLocusSubschemeι {f}
        let W := U.basicOpen f
        let j := W.ι
        let hU : IsUnit (N : Γ(U, ⊤)) := by simpa using hT.map e.appTop.hom
        let hW : IsUnit (N : Γ(W.toScheme, ⊤)) := by simpa using hU.map j.appTop.hom
        let hkj : Set.range k.base = (Set.range j.base)ᶜ := by
          rw [Scheme.range_zeroLocusSubschemeι_singleton, Scheme.Opens.range_ι]
        let S := openClosedShortComplex (ModuleCat.{u + 1} A) j k
          (disjoint_range_of_range_eq_compl j k hkj) (ordinaryFiniteConstant A U)
        let hS : S.ShortExact := shortExact_openClosedShortComplex
          (ModuleCat.{u + 1} A) j k (ordinaryFiniteConstant A U) hkj
        let K := Scheme.finiteEtaleTateLine W.toScheme N A hA
        let κ : Ext (ordinaryFiniteConstant A W.toScheme) K 1 :=
          (ordinaryFiniteExtHomEquiv A W.toScheme _ K 1).symm
            ((ordinaryFiniteClassEquiv A W.toScheme K 1).symm
              (Sheaf.H.map (ordinaryFiniteRootMap A N hA W.toScheme) 1
                (W.toScheme.kummerδ₀ N hW (Additive.ofMul (U.basicOpenUnit f)))))
        let J := openImmersionLowerShriek (ModuleCat.{u + 1} A) j
        let ε := J.map (t.line j hU).inv ≫
          (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j).counit.app
            (Scheme.finiteEtaleTateLine U N A hA)
        let κopen : Ext S.X₁ (Scheme.finiteEtaleTateLine U N A hA) 1 :=
          (Ext.mk₀ (J.map ((Scheme.upperStarConstantSheafIso
            (ModuleCat.{u + 1} A) j).app (ModuleCat.of A A)).hom)).comp
              ((κ.mapExactFunctor J).comp (Ext.mk₀ ε) (add_zero 1)) (zero_add 1)
        let δκ : Ext ((lowerStar (ModuleCat.{u + 1} A) k).obj
            (ordinaryFiniteConstant A (U.zeroLocusSubscheme {f})))
            (Scheme.finiteEtaleTateLine U N A hA) 2 :=
          (Ext.mk₀ ((lowerStar (ModuleCat.{u + 1} A) k).map
            ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) k).app
              (ModuleCat.of A A)).inv)).comp
                (hS.extClass.comp κopen (rfl : 1 + 1 = 2)) (zero_add 2)
        let β := (Ext.mk₀ (asIso (ProEtale.geoCartierSourceComparison A k)).inv).comp
          (δκ.mapExactFunctor (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) U))
          (zero_add 2)
        ((ProEtale.geoCartierCanonicalClass A N hN hA i hI hT).mapExactFunctor
            (ProEtale.upperStar (ModuleCat.{u + 1} A) e)).comp
              (Ext.mk₀ (ProEtale.geoCartierLinePullback A N hA t e hT).hom) (add_zero 2) =
          (Ext.mk₀ (ProEtale.geoCartierExchange A i k e d sqf.toCommSq)).comp
            (-β) (zero_add 2)) := by
  obtain ⟨d⟩ := Scheme.nonempty_finiteEtaleTwistPullbackData A N hN hA
  rcases d.laws with ⟨hcover, hr, hgen, hc0, hcplus, hcneg, hid, hcomp, hunit0,
    hunit1, hpos, hassoc, hsymm, heval, htensor, hexp⟩
  let t : OrdinaryFiniteTwistTransport A N hA :=
    { roots := d.r
      line := fun v hT => d.c v hT (by simpa using hT.map v.appTop.hom) 1
      roots_normalization := hr
      line_normalization := fun v hT =>
        hgen v hT (by simpa using hT.map v.appTop.hom) }
  have ht := pro_cartier_pullback_for_transport A N hN hA t
    (D := D) (T := T) (D' := D') (T' := T') i i' v w sq hI hI' hT hT'
  have hκ := geoCartierEtaleClass_spec A N hN hA i hI hT |>.1
  have hκ' := geoCartierEtaleClass_spec A N hN hA i' hI' hT' |>.1
  have hord := supported_kummer_boundary_pullback T N hN A hA hT i hI
    (geoCartierEtaleClass A N hN hA i hI hT) hκ t i' v w sq hI'
    (geoCartierEtaleClass A N hN hA i' hI' hT') hκ'
  refine ⟨t, ?_, hord, ht.1, ht.2, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · let := isIso_baseChangeMap_of_isFinite (ModuleCat.{u + 1} A) sq
    unfold supportedConstantExchange
    infer_instance
  · intro sqId
    exact ⟨exchange_id_local A i sqId.toCommSq, pro_exchange_id_local A i sqId⟩
  · exact congrArg Iso.hom (hid T hT 1)
  · unfold ProEtale.geoCartierLinePullback ProEtale.geoCartierLine
    simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom]
    change (ProEtale.comparisonUpperStarCompUpperStarIso
        (ModuleCat.{u + 1} A) (𝟙 T)).hom.app _ ≫
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).map
          (t.line (𝟙 T) hT).hom = _
    rw [show (t.line (𝟙 T) hT).hom = _ from congrArg Iso.hom (hid T hT 1)]
    exact ProEtale.comparison_id_local A T _
  · intro D'' T'' i'' hi'' v₂ w₂ sq₂ sq₁₂
    exact exchange_comp_local A i i' i'' v w v₂ w₂ sq.toCommSq sq₂.toCommSq sq₁₂.toCommSq
  · intro D'' T'' i'' hi'' v₂ w₂ sq₂ sq₁₂
    exact pro_exchange_comp_local A i i' i'' v w v₂ w₂ sq sq₂ sq₁₂
  · intro T'' v₂
    constructor
    · exact (congrArg Iso.hom (hcomp v v₂ hT hT'
        (by simpa using hT'.map v₂.appTop.hom) 1)).symm
    · have hc : (t.line (v₂ ≫ v) hT).hom =
          (upperStarComp (ModuleCat.{u + 1} A) v₂ v).hom.app _ ≫
            (upperStar (ModuleCat.{u + 1} A) v₂).map (t.line v hT).hom ≫
            (t.line v₂ hT').hom := congrArg Iso.hom
              (hcomp v v₂ hT hT' (by simpa using hT'.map v₂.appTop.hom) 1)
      simp only [ProEtale.geoCartierLinePullback, ProEtale.geoCartierLine,
        Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom]
      rw [hc]
      simp only [Functor.map_comp, Category.assoc]
      rw [reassoc_of% ((ProEtale.comparisonUpperStarCompUpperStarIso
        (ModuleCat.{u + 1} A) v₂).hom.naturality (t.line v hT).hom)]
      rw [← reassoc_of% (ProEtale.comparison_comp_local A v₂ v _)]
  · intro U e he f d sqf
    let k := U.zeroLocusSubschemeι {f}
    have hker : k.ker = i.ker.comap e := by
      change (U.zeroLocusSubschemeι {f}).ker = i.ker.comap e
      rw [← sqf.flip.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso,
        Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]
    have hIU : k.ker.IsInvertible := by
      rw [hker]
      exact hI.comap_of_flat e
    have hU : IsUnit (N : Γ(U, ⊤)) := by simpa using hT.map e.appTop.hom
    have hkj : Set.range k.base = (Set.range (U.basicOpen f).ι.base)ᶜ := by
      rw [Scheme.range_zeroLocusSubschemeι_singleton, Scheme.Opens.range_ι]
    have hchart := pro_cartier_pullback_for_transport A N hN hA t
      i k e d sqf hI hIU hT hU
    have hsign := principal_canonical_sign_local A N hN hA t U f hIU hU hkj
    rw [← hchart.2, hsign]
    rfl

end AlgebraicGeometry.Etale
