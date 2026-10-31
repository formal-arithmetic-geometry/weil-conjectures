/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralDerivedCoefficientData
public import WeilConjectures.AlgebraicGeometry.CondensedConstantConstructibilitySupplement
public import WeilConjectures.AlgebraicGeometry.FormalClosedSupportSheaves
public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.CohomologicalDimension
import all WeilConjectures.AlgebraicGeometry.CohomologicalDimension
import WeilConjectures.AlgebraicGeometry.PrincipalTensorScalarExtension
import WeilConjectures.AlgebraicGeometry.DerivedNakayamaResolution
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.RingTheory.Ideal.Quotient.Index
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
import Mathlib.Topology.Category.Profinite.EffectiveEpi
import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
import Mathlib.Condensed.TopComparison
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
import Mathlib.Topology.Algebra.Ring.Ideal
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import WeilConjectures.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
import WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntSheafLinear
import WeilConjectures.CategoryTheory.Sites.MonObj
import Mathlib.Algebra.Homology.ShortComplex.Ab
import WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
import Mathlib.Topology.Bases
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.LocallyConstant.Basic
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.TensorMappingCone
import WeilConjectures.CategoryTheory.Monoidal.Closed.UnitEnd
import Mathlib.CategoryTheory.Center.Linear
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Kernels
import WeilConjectures.NumberTheory.Padics.ContinuousUniformizerDivision
import Mathlib.Topology.Algebra.Order.Field
import WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp
import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.FractionRing
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.SixFunctors.ProEtale.DerivedCompletionSupplement
import WeilConjectures.Algebra.Homology.InternalKFlatScalarTowerRealizationSupplement
import WeilConjectures.AlgebraicGeometry.FiniteCoefficientModelComparison
import WeilConjectures.AlgebraicGeometry.FiniteModelSheafQuotientConstructible
import WeilConjectures.SixFunctors.ProEtale.Comparison.ForgetUpperStar
import all WeilConjectures.AlgebraicGeometry.IntegralPositiveReductionConstructible
import WeilConjectures.CategoryTheory.DerivedCategory.PlusDevissage
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import all WeilConjectures.AlgebraicGeometry.FormalClosedSupportDerived
import all WeilConjectures.AlgebraicGeometry.FormalClosedSupportSheaves
import all WeilConjectures.AlgebraicGeometry.IntegralReductionUnderlyingDirectImage
import WeilConjectures.CategoryTheory.BoundedHeartAmplitude
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated

/-!
# Cohomology of the restricted support of an integral derived reduction

Source: blueprint `sk-prop-int-compactness/sk-lem-int-ext-bound.proof.md`,
first paragraph and first finite-reduction bullet.
(blueprint: lem-route-integral-reduction-support-amplitude).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [-instance] InternalAbelianSheafModule.comparison_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
private noncomputable instance abSheafNatColimits (X : Scheme.{u}) :
    HasColimitsOfShape ℕ (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) := by
  have : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  have : HasSheafify (Scheme.ProEt.topology X) Ab.{u + 1} :=
    GrothendieckTopology.hasSheafify_of_essentiallySmall.{u + 2, u, u, u + 1} _ _
  exact Sheaf.instHasColimitsOfShape

private theorem ab_classical_iso {X : Scheme.{u}}
    {M N : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} (e : M ≅ N)
    (hM : IsClassicalAbelian M) : IsClassicalAbelian N :=
  (ProEtale.isClassical_iso_iff
    ((sheafCompose (Scheme.ProEt.topology X) (forget Ab.{u + 1})).mapIso e)).mp hM

private theorem ab_classical_image (X : Scheme.{u})
    (M : Sheaf X.smallEtaleTopology Ab.{u + 1}) :
    IsClassicalAbelian ((comparisonUpperStar Ab.{u + 1} X).obj M) := by
  apply (classical_iff_counit X _).mpr
  infer_instance

private theorem ab_classical_image_derived (X : Scheme.{u})
    (M : DerivedCategory (Sheaf X.smallEtaleTopology Ab.{u + 1})) (q : ℤ) :
    IsClassicalAbelian ((DerivedCategory.homologyFunctor _ q).obj
      ((comparisonUpperStar Ab.{u + 1} X).mapDerivedCategory.obj M)) := by
  exact ab_classical_iso
    (((comparisonUpperStar Ab.{u + 1} X).mapDerivedCategoryHomologyFunctorIso q).app M)
    (ab_classical_image X _)

private theorem ab_classical_pullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (hM : IsClassicalAbelian M) :
    IsClassicalAbelian ((ProEtale.upperStar Ab.{u + 1} f).obj M) := by
  have := (classical_iff_counit Y M).mp hM
  let e := asIso ((comparisonAdjunction Ab.{u + 1} Y).counit.app M)
  apply ab_classical_iso
    ((comparisonUpperStarCompUpperStarIso Ab.{u + 1} f).symm.app _ ≪≫
      (ProEtale.upperStar Ab.{u + 1} f).mapIso e)
  exact ab_classical_image X _

private theorem ab_comparison_derived_unit (X : Scheme.{u}) :
    IsIso (comparisonAdjunction Ab.{u + 1} X).derivedPlus.unit := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro K
  exact Adjunction.isIso_derivedPlus_unit_app_of_rightAcyclic
    (comparisonAdjunction Ab.{u + 1} X)
    (fun _ _ ↦ inferInstance)
    (fun I _ ↦ rightAcyclic_comparisonUpperStar_obj_of_injective Ab.{u + 1} X I) K

private theorem ab_classical_counit (X : Scheme.{u})
    (K : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}))
    (a b : ℤ) [K.IsGE a] [K.IsLE b]
    (hK : ∀ q : ℤ, IsClassicalAbelian ((DerivedCategory.homologyFunctor _ q).obj K.obj)) :
    IsIso ((comparisonAdjunction Ab.{u + 1} X).derivedPlus.counit.app K) := by
  have := ab_comparison_derived_unit X
  let L := comparisonUpperStar Ab.{u + 1} X
  let adj := (comparisonAdjunction Ab.{u + 1} X).derivedPlus
  let G := (comparisonLowerStar Ab.{u + 1} X).rightDerivedFunctorPlus
  let : G.CommShift ℤ := adj.rightAdjointCommShift ℤ
  let : adj.CommShift ℤ := adj.commShift_of_leftAdjoint ℤ
  let : G.IsTriangulated := adj.isTriangulated_rightAdjoint
  have ff := adj.fullyFaithfulLOfIsIsoUnit
  have := ff.full
  have := ff.faithful
  have hsingle (Y : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (hY : L.essImage Y) :
      IsIso (adj.counit.app ((DerivedCategory.Plus.singleFunctor _ 0).obj Y)) := by
    obtain ⟨Z, ⟨e⟩⟩ := hY
    let e' := (L.mapDerivedCategoryPlusSingleFunctor 0).app Z ≪≫
      (DerivedCategory.Plus.singleFunctor _ 0).mapIso e
    exact adj.isIso_counit_app_of_iso e'.symm
  apply DerivedCategory.Plus.isIso_app_of_bounded adj.counit L.essImage hsingle K a b
  intro q
  let Y := (DerivedCategory.Plus.homologyFunctor _ q).obj K
  have hY : IsClassicalAbelian Y := hK q
  have := (classical_iff_counit X Y).mp hY
  exact ⟨_, ⟨asIso ((comparisonAdjunction Ab.{u + 1} X).counit.app Y)⟩⟩

private theorem ab_classical_direct_image {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f]
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}))
    (a b : ℤ) (hbound : ∀ q : ℤ, q < a ∨ b < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj K))
    (hK : ∀ q : ℤ, IsClassicalAbelian ((DerivedCategory.homologyFunctor _ q).obj K))
    (q : ℤ) :
    IsClassicalAbelian ((DerivedCategory.homologyFunctor _ q).obj
      ((ProEtale.lowerStar Ab.{u + 1} f).rightDerivedFunctor.obj K)) := by
  have hge : K.IsGE a := (DerivedCategory.isGE_iff K a).mpr
    (fun q hq ↦ hbound q (Or.inl hq))
  have hle : K.IsLE b := (DerivedCategory.isLE_iff K b).mpr
    (fun q hq ↦ hbound q (Or.inr hq))
  let Kp : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) :=
    ⟨K, a, hge⟩
  have : Kp.IsGE a := (DerivedCategory.Plus.isGE_ι_obj_iff Kp a).mp hge
  have : Kp.IsLE b := (DerivedCategory.Plus.isLE_ι_obj_iff Kp b).mp hle
  have := ab_classical_counit X Kp a b hK
  let e := asIso ((comparisonAdjunction Ab.{u + 1} X).derivedPlus.counit.app Kp)
  let M := (comparisonLowerStar Ab.{u + 1} X).rightDerivedFunctorPlus.obj Kp
  have : IsIso (Functor.rightDerivedFunctorPlusBaseChange
      (lowerStarComparisonUpperStarBaseChange f Ab.{u + 1})) := by
    have := isIso_lowerStarComparisonUpperStarBaseChange f Ab.{u + 1}
    exact Functor.isIso_rightDerivedFunctorPlusBaseChange_of_rightAcyclic
      (asIso (lowerStarComparisonUpperStarBaseChange f Ab.{u + 1}))
      (fun I _ ↦ rightAcyclic_lowerStar_comparisonUpperStar_obj_of_injective
        Ab.{u + 1} f I)
  let c := asIso (Functor.rightDerivedFunctorPlusBaseChange
    (lowerStarComparisonUpperStarBaseChange f Ab.{u + 1}))
  let d := c.app M ≪≫ (ProEtale.lowerStar Ab.{u + 1} f).rightDerivedFunctorPlus.mapIso e
  let Z := (Etale.lowerStar Ab.{u + 1} f).rightDerivedFunctorPlus.obj M
  let d' := ((comparisonUpperStar Ab.{u + 1} Y).mapDerivedCategoryPlusCompatibility.app Z) ≪≫
    DerivedCategory.Plus.ι.mapIso d ≪≫
    (ProEtale.lowerStar Ab.{u + 1} f).rightDerivedFunctorPlusCompatibility.app Kp
  apply ab_classical_iso ((DerivedCategory.homologyFunctor _ q).mapIso d')
  exact ab_classical_image_derived Y Z.obj q

private theorem ab_classical_triangle (X : Scheme.{u})
    (T : Pretriangulated.Triangle
      (DerivedCategory (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})))
    (hT : T ∈ Pretriangulated.distinguishedTriangles) (a b c d : ℤ)
    (h₂ : ∀ q : ℤ, q < a ∨ b < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj T.obj₂))
    (h₃ : ∀ q : ℤ, q < c ∨ d < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj T.obj₃))
    (hc₂ : ∀ q : ℤ, IsClassicalAbelian ((DerivedCategory.homologyFunctor _ q).obj T.obj₂))
    (hc₃ : ∀ q : ℤ, IsClassicalAbelian ((DerivedCategory.homologyFunctor _ q).obj T.obj₃))
    (q : ℤ) : IsClassicalAbelian ((DerivedCategory.homologyFunctor _ q).obj T.obj₁) := by
  have := ab_comparison_derived_unit X
  let L := comparisonUpperStar Ab.{u + 1} X
  let adj := (comparisonAdjunction Ab.{u + 1} X).derivedPlus
  let ff := adj.fullyFaithfulLOfIsIsoUnit
  have : L.mapDerivedCategoryPlus.Full := ff.full
  let F := L.mapDerivedCategoryPlus ⋙ DerivedCategory.Plus.ι
  have hmem (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}))
      (a b : ℤ) (hb : ∀ q : ℤ, q < a ∨ b < q →
        IsZero ((DerivedCategory.homologyFunctor _ q).obj K))
      (hK : ∀ q : ℤ, IsClassicalAbelian ((DerivedCategory.homologyFunctor _ q).obj K)) :
      F.essImage K := by
    have hge : K.IsGE a := (DerivedCategory.isGE_iff K a).mpr
      (fun q hq ↦ hb q (Or.inl hq))
    have hle : K.IsLE b := (DerivedCategory.isLE_iff K b).mpr
      (fun q hq ↦ hb q (Or.inr hq))
    let Kp : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) :=
      ⟨K, a, hge⟩
    have : Kp.IsGE a := (DerivedCategory.Plus.isGE_ι_obj_iff Kp a).mp hge
    have : Kp.IsLE b := (DerivedCategory.Plus.isLE_ι_obj_iff Kp b).mp hle
    have := ab_classical_counit X Kp a b hK
    exact ⟨_, ⟨DerivedCategory.Plus.ι.mapIso (asIso (adj.counit.app Kp))⟩⟩
  obtain ⟨M, ⟨e⟩⟩ := F.essImage.ext_of_isTriangulatedClosed₁ T hT
    (hmem _ a b h₂ hc₂) (hmem _ c d h₃ hc₃)
  apply ab_classical_iso ((DerivedCategory.homologyFunctor _ q).mapIso e)
  exact ab_classical_image_derived X M.obj q

private theorem module_classical_pullback
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : pulledBackModuleObjects Λ Y) (hM : IsClassicalAbelian M.X) :
    IsClassicalAbelian ((upperStar Λ f).obj M).X := by
  apply ab_classical_iso ((profinitePointModuleForgetPullbackIso Λ f).app M).symm
  exact ab_classical_pullback f M.X hM

private theorem module_classical_derived_pullback
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (pulledBackModuleObjects Λ Y))
    (hK : ∀ q : ℤ, IsClassicalAbelian ((DerivedCategory.homologyFunctor _ q).obj K).X)
    (q : ℤ) :
    IsClassicalAbelian ((DerivedCategory.homologyFunctor _ q).obj
      ((upperStar Λ f).mapDerivedCategory.obj K)).X := by
  apply ab_classical_iso ((Mod.forget (condensedRingObj Λ X)).mapIso
    (((upperStar Λ f).mapDerivedCategoryHomologyFunctorIso q).app K))
  exact module_classical_pullback Λ f _ (hK q)

private theorem module_classical_reflect_closed
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Z V : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (j : V ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range j = (Set.range i)ᶜ)
    (M : pulledBackModuleObjects Λ Z)
    (hM : IsClassicalAbelian ((lowerStar Λ i).obj M).X) : IsClassicalAbelian M.X := by
  have := moduleCounitOfAbelian Λ i (ProEtale.abelian_closed_support i j hij).1
  apply ab_classical_iso ((Mod.forget (condensedRingObj Λ Z)).mapIso
    (asIso ((upperStarLowerStarAdjunction Λ i).counit.app M)))
  exact module_classical_pullback Λ i _ hM

private theorem reduction_bound
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) (N : pulledBackModuleObjects (integralCoefficientRing l E) X)
    (n : ℕ) (q : ℤ) (hq : q < -1 ∨ 0 < q) :
    IsZero ((DerivedCategory.homologyFunctor _ q).obj
      ((integralReductionFunctor l E X (n + 1)).obj
        ((DerivedCategory.singleFunctor _ 0).obj N))) := by
  obtain ⟨d, _, r, _, i, t, _, _, hres⟩ :=
    DerivedNakayama.derived_nakayama_resolution l E
  obtain ⟨_, ⟨e⟩, _⟩ := hres X (n + 1) (by omega)
  let C := (CochainComplex.singleFunctor
    (pulledBackModuleObjects (integralCoefficientRing l E) X) 0).obj N
  let f := DerivedNakayama.scalarOnComplex l E X (d ^ (n + 1)) C
  have hs (r : ℤ) (hr : r ≠ 0) :
      IsZero ((DerivedCategory.homologyFunctor _ r).obj (DerivedCategory.Q.obj C)) := by
    apply IsZero.of_iso _ ((DerivedCategory.homologyFunctor _ r).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ _ 0).app N).symm)
    rcases lt_or_gt_of_ne hr with hr | hr
    · exact DerivedCategory.isZero_of_isGE _ 0 r hr
    · exact DerivedCategory.isZero_of_isLE _ 0 r hr
  have hc : IsZero ((DerivedCategory.homologyFunctor _ q).obj
      (DerivedCategory.Q.obj (CochainComplex.mappingCone f))) :=
    (DerivedCategory.HomologySequence.exact₃ _
      (DerivedCategory.mappingCone_triangle_distinguished f) q (q + 1) rfl).isZero_X₂
        ((hs q (by rcases hq with hq | hq <;> omega)).eq_of_src _ _)
        ((hs (q + 1) (by rcases hq with hq | hq <;> omega)).eq_of_tgt _ _)
  exact hc.of_iso ((DerivedCategory.homologyFunctor _ q).mapIso
    ((integralReductionFunctor l E X (n + 1)).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ _ 0).app N) ≪≫ e.app C))

set_option maxHeartbeats 1600000 in
-- Elaborating the integral module adjunctions and their exactness instances is expensive.
private theorem actual_support_triangle
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Z V : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (j : V ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range j = (Set.range i)ᶜ)
    [hAdd : (closedModuleSectionsWithSupport Λ i j).Additive] :
    ∃ adj : lowerStar Λ i ⊣ closedModuleSectionsWithSupport Λ i j,
      letI : PreservesFiniteColimits (lowerStar Λ i) := by
        have : PreservesColimitsOfSize.{u + 1, u + 1} (lowerStar Λ i) :=
          adj.leftAdjoint_preservesColimits
        infer_instance
      ∃ δ : (upperStar Λ j).mapDerivedCategory ⋙ (lowerStar Λ j).rightDerivedFunctor ⟶
        ((closedModuleSectionsWithSupport Λ i j).rightDerivedFunctor ⋙
          (lowerStar Λ i).mapDerivedCategory) ⋙
            shiftFunctor (DerivedCategory (pulledBackModuleObjects Λ X)) (1 : ℤ),
        ∀ K, Pretriangulated.Triangle.mk
          (adj.mapDerivedCategoryRightDerivedAdjunction.counit.app K)
          ((upperStarLowerStarAdjunction Λ j).mapDerivedCategoryRightDerivedAdjunction.unit.app K)
          (δ.app K) ∈ Pretriangulated.distinguishedTriangles := by
  classical
  have hji : Set.range i.base = (Set.range j.base)ᶜ := by rw [hij, compl_compl]
  have : PreservesFiniteColimits (lowerStar Λ i) := closedSupport_lowerStarExact Λ i j hji
  obtain ⟨hAb, hsupportAb⟩ := ProEtale.abelian_closed_support i j hij
  have hi := moduleCounitOfAbelian Λ i hAb
  have ff := (upperStarLowerStarAdjunction Λ i).fullyFaithfulROfIsIsoCounit
  have := ff.full
  have := ff.faithful
  have hzero := openRestrictionPushforwardZero Λ i j hij
  have hsupport (M : pulledBackModuleObjects Λ X)
      (hM : IsZero ((upperStar Λ j).obj M)) :
      IsIso ((upperStarLowerStarAdjunction Λ i).unit.app M) := by
    apply moduleUnitOfAbelian Λ i M
    apply hsupportAb
    exact ((Mod.forget _).map_isZero hM).of_iso
      ((profinitePointModuleForgetPullbackIso Λ j).app M).symm
  have hjAb : IsIso (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} j).counit := by
    have ff := (ProEtale.openImmersionRestrictionLowerStarAdjunction
      Ab.{u + 1} j).fullyFaithfulROfIsIsoCounit
    have := ff.full
    have := ff.faithful
    exact (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} j).counit_isIso_of_R_fully_faithful
  have hjcounit := moduleCounitOfAbelian Λ j hjAb
  obtain ⟨_, ⟨adj⟩⟩ := kernelSupportAdjunction
    (upperStar Λ i) (lowerStar Λ i) (upperStar Λ j) (lowerStar Λ j)
    (upperStarLowerStarAdjunction Λ i) (upperStarLowerStarAdjunction Λ j) hzero hsupport
  change lowerStar Λ i ⊣ closedModuleSectionsWithSupport Λ i j at adj
  refine ⟨adj, ?_⟩
  exact transportAdjunctionTriangle adj.mapDerivedCategoryRightDerivedAdjunction
    (closedSupportDerivedAdjunction Λ i j hji)
    (upperStarLowerStarAdjunction Λ j).mapDerivedCategoryRightDerivedAdjunction
    (closedSupportOpenDerivedAdjunction Λ j) (closedSupport_triangle Λ i j hji)

private theorem abelian_direct_image_heart_bound
    (l : ℕ) [Fact l.Prime] {V X : Scheme.{u}} (j : V ⟶ X)
    [QuasiCompact j] [QuasiSeparated j] (c : ℕ)
    (hc : (c : WithTop ℕ) = relativeCohomologicalDimension.{u} l (Fact.out : l.Prime) j)
    (M : Sheaf (Scheme.ProEt.topology V) Ab.{u + 1})
    (hM : IsClassicalAbelian M ∧ IsEllPowerTorsion l (Fact.out : l.Prime) M)
    (q : ℤ) (hq : q < 0 ∨ (c : ℤ) < q) :
    IsZero ((DerivedCategory.homologyFunctor _ q).obj
      ((ProEtale.lowerStar Ab.{u + 1} j).rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj M))) := by
  rcases hq with hq | hq
  · have := (ProEtale.lowerStar Ab.{u + 1} j).isGE_rightDerivedFunctor_obj_singleFunctor M
    exact DerivedCategory.isZero_of_isGE _ 0 q hq
  · obtain ⟨r, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ q)
    by_contra hn
    have hle : (r : WithTop ℕ) ≤
        relativeCohomologicalDimension.{u} l (Fact.out : l.Prime) j :=
      le_sSup ⟨r, rfl, M, hM.1, hM.2, hn⟩
    rw [← hc] at hle
    have hrc : r ≤ c := WithTop.coe_le_coe.mp hle
    exact (not_le_of_gt hq) (Int.ofNat_le.mpr hrc)

private theorem abelian_direct_image_bound
    (l : ℕ) [Fact l.Prime] {V X : Scheme.{u}} (j : V ⟶ X)
    [QuasiCompact j] [QuasiSeparated j] (c : ℕ)
    (hc : (c : WithTop ℕ) = relativeCohomologicalDimension.{u} l (Fact.out : l.Prime) j)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1}))
    (hK : ∀ q : ℤ, q < -1 ∨ 0 < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj K))
    (hclass : ∀ q : ℤ,
      IsClassicalAbelian ((DerivedCategory.homologyFunctor _ q).obj K) ∧
      IsEllPowerTorsion l (Fact.out : l.Prime)
        ((DerivedCategory.homologyFunctor _ q).obj K)) :
    ∀ q : ℤ, q < -1 ∨ (c : ℤ) < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj
        ((ProEtale.lowerStar Ab.{u + 1} j).rightDerivedFunctor.obj K)) := by
  let T := (ProEtale.lowerStar Ab.{u + 1} j).rightDerivedFunctor
  let P : Sheaf (Scheme.ProEt.topology V) Ab.{u + 1} → Prop := fun M ↦
    ∀ q : ℤ, q < 0 ∨ (c : ℤ) < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj
        (T.obj ((DerivedCategory.singleFunctor _ 0).obj M)))
  have h := DerivedCategory.bounded_heart_amplitude _ _ T P
    (fun M N e h q hq ↦ (h q hq).of_iso
      ((DerivedCategory.homologyFunctor _ q).mapIso
        (T.mapIso ((DerivedCategory.singleFunctor _ 0).mapIso e))).symm)
    (fun q _ ↦ (DerivedCategory.homologyFunctor _ q).map_isZero
      (T.map_isZero ((DerivedCategory.singleFunctor _ 0).map_isZero (isZero_zero _))))
    0 c (by omega) (fun _ h ↦ h) (-1) 0 (by omega) K hK
    (fun q ↦ abelian_direct_image_heart_bound l j c hc _ (hclass q))
  simpa using h

private theorem support_bound
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X S Z V : Scheme.{u}} (v : S ⟶ Z) (i : Z ⟶ X) (j : V ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range j = (Set.range i)ᶜ)
    [hAdd : (closedModuleSectionsWithSupport (integralCoefficientRing l E) i j).Additive]
    (c : ℕ)
    (hc : (c : WithTop ℕ) = relativeCohomologicalDimension.{u} l (Fact.out : l.Prime) j)
    (B : integralDerived l E X)
    (hB : ∀ q : ℤ, q < -1 ∨ 0 < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj B))
    (hclass : ∀ q : ℤ,
      IsClassicalAbelian ((DerivedCategory.homologyFunctor _ q).obj
        ((Mod.forget (D := Sheaf (Scheme.ProEt.topology V) Ab.{u + 1})
          (AdicCompletion.ring l E V)).mapDerivedCategory.obj
          ((upperStar (integralCoefficientRing l E) j).mapDerivedCategory.obj B))) ∧
      IsEllPowerTorsion l (Fact.out : l.Prime)
        ((DerivedCategory.homologyFunctor _ q).obj
          ((Mod.forget (D := Sheaf (Scheme.ProEt.topology V) Ab.{u + 1})
            (AdicCompletion.ring l E V)).mapDerivedCategory.obj
            ((upperStar (integralCoefficientRing l E) j).mapDerivedCategory.obj B)))) :
    ∀ q : ℤ, q < -1 ∨ (c : ℤ) + 1 < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj
        ((upperStar (integralCoefficientRing l E) v).mapDerivedCategory.obj
          ((closedModuleSectionsWithSupport
          (integralCoefficientRing l E) i j).rightDerivedFunctor.obj B))) := by
  let Λ := integralCoefficientRing l E
  let J := (upperStar Λ j).mapDerivedCategory.obj B
  let U := Mod.forget (D := Sheaf (Scheme.ProEt.topology V) Ab.{u + 1})
    (AdicCompletion.ring l E V)
  let W := Mod.forget (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (AdicCompletion.ring l E X)
  have hJ (q : ℤ) (hq : q < -1 ∨ 0 < q) :
      IsZero ((DerivedCategory.homologyFunctor _ q).obj (U.mapDerivedCategory.obj J)) :=
    U.isZero_homologyFunctor_mapDerivedCategory_obj
      ((upperStar Λ j).isZero_homologyFunctor_mapDerivedCategory_obj (hB q hq))
  have hL := abelian_direct_image_bound l j c hc _ hJ hclass
  have hLi (q : ℤ) (hq : q < -1 ∨ (c : ℤ) < q) :
      IsZero ((DerivedCategory.homologyFunctor _ q).obj
        ((lowerStar Λ j).rightDerivedFunctor.obj J)) := by
    apply W.isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj
    exact (hL q hq).of_iso ((DerivedCategory.homologyFunctor _ q).mapIso
      ((integralForgetDirectImageIso l E j).app J))
  obtain ⟨adj, htri⟩ := actual_support_triangle Λ i j hij
  let : PreservesFiniteColimits (lowerStar Λ i) := by
    have : PreservesColimitsOfSize.{u + 1, u + 1} (lowerStar Λ i) :=
      adj.leftAdjoint_preservesColimits
    infer_instance
  obtain ⟨δ, hδ⟩ := htri
  have hcounit := moduleCounitOfAbelian Λ i (ProEtale.abelian_closed_support i j hij).1
  have ff := (upperStarLowerStarAdjunction Λ i).fullyFaithfulROfIsIsoCounit
  have := ff.faithful
  intro q hq
  apply (upperStar Λ v).isZero_homologyFunctor_mapDerivedCategory_obj
  apply (lowerStar Λ i).isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj
  have h₁ := hLi (q - 1) (by rcases hq with hq | hq <;> omega)
  have h₃ := hB q (by rcases hq with hq | hq <;> omega)
  exact (DerivedCategory.HomologySequence.exact₁ _ (hδ B) (q - 1) q (by omega)).isZero_X₂
    (h₁.eq_of_src _ _) (h₃.eq_of_tgt _ _)

private theorem support_classical
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X S Z V : Scheme.{u}} (v : S ⟶ Z) (i : Z ⟶ X) (j : V ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range j = (Set.range i)ᶜ)
    [hAdd : (closedModuleSectionsWithSupport (integralCoefficientRing l E) i j).Additive]
    (c : ℕ)
    (hc : (c : WithTop ℕ) = relativeCohomologicalDimension.{u} l (Fact.out : l.Prime) j)
    (B : integralDerived l E X)
    (hB : ∀ q : ℤ, q < -1 ∨ 0 < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj B))
    (hBc : ∀ q : ℤ, IsClassicalAbelian ((DerivedCategory.homologyFunctor _ q).obj B).X)
    (hclass : ∀ q : ℤ,
      IsClassicalAbelian ((DerivedCategory.homologyFunctor _ q).obj
        ((Mod.forget (D := Sheaf (Scheme.ProEt.topology V) Ab.{u + 1})
          (AdicCompletion.ring l E V)).mapDerivedCategory.obj
          ((upperStar (integralCoefficientRing l E) j).mapDerivedCategory.obj B))) ∧
      IsEllPowerTorsion l (Fact.out : l.Prime)
        ((DerivedCategory.homologyFunctor _ q).obj
          ((Mod.forget (D := Sheaf (Scheme.ProEt.topology V) Ab.{u + 1})
            (AdicCompletion.ring l E V)).mapDerivedCategory.obj
            ((upperStar (integralCoefficientRing l E) j).mapDerivedCategory.obj B))))
    (q : ℤ) :
    IsClassicalAbelian ((DerivedCategory.homologyFunctor _ q).obj
      ((upperStar (integralCoefficientRing l E) v).mapDerivedCategory.obj
        ((closedModuleSectionsWithSupport
          (integralCoefficientRing l E) i j).rightDerivedFunctor.obj B))).X := by
  let Λ := integralCoefficientRing l E
  let J := (upperStar Λ j).mapDerivedCategory.obj B
  let U := Mod.forget (D := Sheaf (Scheme.ProEt.topology V) Ab.{u + 1})
    (AdicCompletion.ring l E V)
  let W := Mod.forget (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (AdicCompletion.ring l E X)
  have hJ (r : ℤ) (hr : r < -1 ∨ 0 < r) :
      IsZero ((DerivedCategory.homologyFunctor _ r).obj (U.mapDerivedCategory.obj J)) :=
    U.isZero_homologyFunctor_mapDerivedCategory_obj
      ((upperStar Λ j).isZero_homologyFunctor_mapDerivedCategory_obj (hB r hr))
  have hL := abelian_direct_image_bound l j c hc _ hJ hclass
  let L := (lowerStar Λ j).rightDerivedFunctor.obj J
  let e := (integralForgetDirectImageIso l E j).app J
  have hLb (r : ℤ) (hr : r < -1 ∨ (c : ℤ) < r) :
      IsZero ((DerivedCategory.homologyFunctor _ r).obj (W.mapDerivedCategory.obj L)) :=
    (hL r hr).of_iso ((DerivedCategory.homologyFunctor _ r).mapIso e)
  have hLc (r : ℤ) : IsClassicalAbelian
      ((DerivedCategory.homologyFunctor _ r).obj (W.mapDerivedCategory.obj L)) :=
    ab_classical_iso ((DerivedCategory.homologyFunctor _ r).mapIso e.symm)
      (ab_classical_direct_image j _ (-1) 0 hJ (fun r ↦ (hclass r).1) r)
  obtain ⟨adj, htri⟩ := actual_support_triangle Λ i j hij
  let : PreservesFiniteColimits (lowerStar Λ i) := by
    have : PreservesColimitsOfSize.{u + 1, u + 1} (lowerStar Λ i) :=
      adj.leftAdjoint_preservesColimits
    infer_instance
  obtain ⟨δ, hδ⟩ := htri
  let A := (closedModuleSectionsWithSupport Λ i j).rightDerivedFunctor.obj B
  let T := W.mapDerivedCategory.mapTriangle.obj
    (Pretriangulated.Triangle.mk
      (adj.mapDerivedCategoryRightDerivedAdjunction.counit.app B)
      ((upperStarLowerStarAdjunction Λ j).mapDerivedCategoryRightDerivedAdjunction.unit.app B)
      (δ.app B))
  have hT := W.mapDerivedCategory.map_distinguished _ (hδ B)
  have hAc (r : ℤ) : IsClassicalAbelian
      ((DerivedCategory.homologyFunctor _ r).obj
        (W.mapDerivedCategory.obj ((lowerStar Λ i).mapDerivedCategory.obj A))) :=
    ab_classical_triangle X T hT (-1) 0 (-1) c
      (fun r hr ↦ W.isZero_homologyFunctor_mapDerivedCategory_obj (hB r hr)) hLb
      (fun r ↦ ab_classical_iso ((W.mapDerivedCategoryHomologyFunctorIso r).app B)
        (hBc r)) hLc r
  apply module_classical_derived_pullback Λ v A
  intro r
  apply module_classical_reflect_closed Λ i j hij
  apply ab_classical_iso
    (W.mapIso (((lowerStar Λ i).mapDerivedCategoryHomologyFunctorIso r).app A) ≪≫
      (W.mapDerivedCategoryHomologyFunctorIso r).app
        ((lowerStar Λ i).mapDerivedCategory.obj A)).symm
  exact hAc r

private theorem reduction_classical
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [IsNoetherian X]
    (N : pulledBackModuleObjects (integralCoefficientRing l E) X)
    (hN : IsConstantModelConstructible (integralCoefficientRing l E) X N)
    (n : ℕ) (q : ℤ) :
    IsClassicalAbelian ((DerivedCategory.homologyFunctor _ q).obj
      ((integralReductionFunctor l E X (n + 1)).obj
        ((DerivedCategory.singleFunctor _ 0).obj N))).X := by
  classical
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let A := Padic.coefficientExtensionRing l E (n + 1)
  obtain ⟨hf, hd, _, hbc, _⟩ :=
    FiniteModelQuotient.finite_model_sheaf_quotient_constructible l E X N hN n
  let : Finite A := hf
  let : DiscreteTopology A := hd
  obtain ⟨e, _⟩ := FiniteDiscreteOrdinary.finiteCoefficientModelComparison A X
  let Q := (AdicCompletion.derivedReduction l E X n).obj
    ((DerivedCategory.singleFunctor _ 0).obj N)
  let F := e.ordinary.functor ⋙ e.fixed.functor
  let U := sheafCompose (Scheme.ProEt.topology X)
    (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} A)) Ab.{u + 1})
  have underlying (M : FiniteDiscreteOrdinary.Internal A X) :
      U.obj (F.obj M) ≅ M.X := by
    dsimp only [F, Functor.comp_obj]
    rw [e.ordinary_functor, e.fixed_functor]
    exact ObjectProperty.isoMk _
      (NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl))
  have hfixed := (fixedCriterion A X e Q).mp hbc
  obtain ⟨L, hL, ⟨eL⟩⟩ := hfixed
  let C := comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) X
  let H := (DerivedCategory.homologyFunctor _ q).obj L
  let eH := (C.mapDerivedCategoryHomologyFunctorIso q).app L ≪≫
    (DerivedCategory.homologyFunctor _ q).mapIso eL
  have hfixedclass : IsClassicalAbelian
      (U.obj ((DerivedCategory.homologyFunctor _ q).obj (F.mapDerivedCategory.obj Q))) :=
    ab_classical_iso
      ((sheafComposeForget₂CompComparisonUpperStarIso (ULift.{u + 1} A) X).app H ≪≫
        U.mapIso eH) (ab_classical_image X _)
  have hquot : IsClassicalAbelian ((DerivedCategory.homologyFunctor _ q).obj Q).X :=
    ab_classical_iso
      (U.mapIso ((F.mapDerivedCategoryHomologyFunctorIso q).app Q).symm ≪≫ underlying _)
      hfixedclass
  obtain ⟨norm, _⟩ := PrincipalNormalization.principal_tensor_scalar_extension l E X
  let R := Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (AdicCompletion.quotient l E X n)
  let W := Mod.forget (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (AdicCompletion.ring l E X)
  apply ab_classical_iso
    (W.mapIso ((R.mapDerivedCategoryHomologyFunctorIso q).app Q) ≪≫
      W.mapIso ((DerivedCategory.homologyFunctor _ q).mapIso
        ((norm n).app ((DerivedCategory.singleFunctor _ 0).obj N)).symm))
  exact hquot

private theorem quotient_annihilator
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ) :
    (l ^ n : Padic.coefficientExtensionRing l E n) = 0 := by
  let O := Padic.coefficientExtensionIntegers l E
  let π := Padic.coefficientExtensionUniformizer l E
  have h := (Padic.extension_integers_dvr l E (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := Padic l) (L := E))).choose_spec.choose_spec
  have hgen : Ideal.span ({π} : Set O) = Padic.coefficientExtensionMaximalIdeal l E :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hval : Padic.coefficientExtensionAbsoluteValue l E (l : E) < 1 := by
    have hext := spectralNorm_extends (K := Padic l) (L := E) (l : Padic l)
    change spectralNorm (Padic l) E (l : E) < 1
    simpa only [map_natCast] using hext.trans_lt (Padic.norm_p_lt_one (p := l))
  have hl : (l : O) ∈ Ideal.span ({π} : Set O) := by
    rw [hgen]
    exact (h.2.1 (l : O)).mpr hval
  have hp : (l : O) ^ n ∈ Padic.coefficientExtensionIdeal l E n :=
    Ideal.pow_mem_pow hl n
  have hz := Ideal.Quotient.eq_zero_iff_mem.mpr hp
  simpa only [map_pow, map_natCast] using hz

private theorem functor_annihilator
    {A B : Type*} [Category* A] [Category* B] [Preadditive A] [Preadditive B]
    (F : A ⥤ B) [F.Additive] (M : A) (r : ℕ) (h : r • 𝟙 M = 0) :
    r • 𝟙 (F.obj M) = 0 := by
  calc
    r • 𝟙 (F.obj M) = r • F.map (𝟙 M) :=
      congrArg (fun f ↦ r • f) (F.map_id M).symm
    _ = F.map (r • 𝟙 M) := F.map_nsmul.symm
    _ = F.map 0 := congrArg F.map h
    _ = 0 := F.map_zero M M

attribute [-instance] InternalAbelianSheafModule.comparison_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
private theorem reduction_annihilator
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) (B : integralDerived l E X) (n : ℕ) :
    (l ^ n) • 𝟙 ((integralReductionFunctor l E X n).obj B) = 0 := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  have : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  have : HasSheafify (Scheme.ProEt.topology X) Ab.{u + 1} :=
    GrothendieckTopology.hasSheafify_of_essentiallySmall.{u + 2, u, u, u + 1} _ _
  have hq : (l ^ n) • 𝟙 (DerivedNakayama.quotientModule l E n) = 0 := by
    apply Mod.hom_ext
    apply Sheaf.hom_ext
    ext S f
    apply ULift.ext
    apply ContinuousMap.ext
    intro s
    change (l ^ n) • f.down s = 0
    rw [nsmul_eq_mul, Nat.cast_pow, quotient_annihilator l E n, zero_mul]
  have : PreservesFiniteLimits (DerivedNakayama.pullback l E X) :=
    DerivedNakayama.pullbackFiniteLimits l E X
  have : (DerivedNakayama.pullback l E X).Additive :=
    Functor.additive_of_preserves_binary_products _
  have : ((derivedTensor (integralCoefficientRing l E) X).obj B).Additive := by
    dsimp only [derivedTensor]
    exact DerivedCategory.additive_tensorLeft B
  exact functor_annihilator ((derivedTensor (integralCoefficientRing l E) X).obj B) _ _
    (functor_annihilator (DerivedCategory.singleFunctor _ 0) _ _
      (functor_annihilator (DerivedNakayama.pullback l E X) _ _ hq))

private theorem ell_torsion_of_annihilated
    {A : Type*} [Category* A] [Abelian A] [HasColimitsOfShape ℕ A]
    (l : ℕ) (hl : l.Prime) (M : A) (e : ℕ) (he : (l ^ e) • 𝟙 M = 0) :
    IsEllPowerTorsion l hl M := by
  have hi : 𝟙 M ≫ ((l ^ e) • 𝟙 M) = 0 := by simpa using he
  let D := ellPowerKernelFunctor l (F := M)
  let a := ellPowerKernelColimitMap l (F := M)
  let b : M ⟶ colimit D :=
    kernel.lift ((l ^ e) • 𝟙 M) (𝟙 M) hi ≫ colimit.ι D e
  have hba : b ≫ a = 𝟙 M := by
    dsimp [b, a, ellPowerKernelColimitMap]
    rw [Category.assoc, colimit.ι_desc]
    exact kernel.lift_ι _ _ _
  have hab : a ≫ b = 𝟙 (colimit D) := by
    apply colimit.hom_ext
    intro r
    let t := e + r
    have her : e ≤ t := Nat.le_add_right e r
    have hrt : r ≤ t := Nat.le_add_left r e
    have hmap : kernel.ι ((l ^ r) • 𝟙 M) ≫
        kernel.lift ((l ^ e) • 𝟙 M) (𝟙 M) hi ≫ D.map (homOfLE her) =
        D.map (homOfLE hrt) := by
      apply (cancel_mono (kernel.ι ((l ^ t) • 𝟙 M))).mp
      simp only [D, ellPowerKernelFunctor, ellPowerKernelMap, Category.assoc,
        kernel.lift_ι, Category.comp_id]
    calc
      colimit.ι D r ≫ a ≫ b =
          kernel.ι ((l ^ r) • 𝟙 M) ≫
            kernel.lift ((l ^ e) • 𝟙 M) (𝟙 M) hi ≫ colimit.ι D e := by
        dsimp [a, b, ellPowerKernelColimitMap]
        rw [← Category.assoc, colimit.ι_desc]
        rfl
      _ = kernel.ι ((l ^ r) • 𝟙 M) ≫
            kernel.lift ((l ^ e) • 𝟙 M) (𝟙 M) hi ≫
              D.map (homOfLE her) ≫ colimit.ι D t := by rw [colimit.w]
      _ = D.map (homOfLE hrt) ≫ colimit.ι D t := by
        simpa only [Category.assoc] using congrArg (fun f ↦ f ≫ colimit.ι D t) hmap
      _ = colimit.ι D r ≫ 𝟙 _ := by rw [colimit.w, Category.comp_id]
  exact ⟨⟨b, hab, hba⟩⟩

private theorem support_torsion
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X S Z V : Scheme.{u}} (v : S ⟶ Z) (i : Z ⟶ X) (j : V ⟶ X)
    [hAdd : (closedModuleSectionsWithSupport (integralCoefficientRing l E) i j).Additive]
    (B : integralDerived l E X) (n : ℕ) (q : ℤ) :
    IsEllPowerTorsion l (Fact.out : l.Prime)
      ((DerivedCategory.homologyFunctor _ q).obj
        ((upperStar (integralCoefficientRing l E) v).mapDerivedCategory.obj
          ((closedModuleSectionsWithSupport
            (integralCoefficientRing l E) i j).rightDerivedFunctor.obj
            ((integralReductionFunctor l E X n).obj B)))).X := by
  apply ell_torsion_of_annihilated l (Fact.out : l.Prime) _ n
  exact functor_annihilator
    (Mod.forget (D := Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (AdicCompletion.ring l E S)) _ _
    (functor_annihilator (DerivedCategory.homologyFunctor _ q) _ _
      (functor_annihilator (upperStar (integralCoefficientRing l E) v).mapDerivedCategory _ _
        (functor_annihilator
          (closedModuleSectionsWithSupport
            (integralCoefficientRing l E) i j).rightDerivedFunctor _ _
          (reduction_annihilator l E X B n))))

attribute [-instance] abSheafNatColimits

/-- The restricted support of a positive derived reduction has classical prime-power
torsion cohomology in the interval `[-1,c+1]`. No source sheaf or derived dual occurs here.

Source: blueprint `sk-prop-int-compactness/sk-lem-int-ext-bound.proof.md`,
first paragraph and first finite-reduction bullet; Stacks Tags 093J, 093M, 09A6 and 08J5.
(blueprint: lem-route-integral-reduction-support-amplitude).

Proof: the completed quotient resolution represents the actual integral reduction
by the cone of pi^(n+1) on N[0], giving amplitude [-1,0]. Principal tensor/scalar
extension and the constructible finite quotient calculation show its underlying
cohomology is classical. Since ell lies in the ideal generated by pi, ell^(n+1)
annihilates the quotient module, hence the actual reduction and its images under
all additive functors. An explicit inverse to the power-kernel colimit map gives
local ell-power torsion. Exact j^* preserves the bounds. Relative cohomological
dimension bounds abelian direct image on classical torsion heart objects by [0,c];
bounded-heart devissage gives [-1,c] on the reduction. The integral forget/direct-image
comparison identifies this with the actual integral Rj_*j^*. The actual integral
support adjunction triangle and faithful exact i_* give the fibre bound [-1,c+1].
For classicality, finite devissage of the comparison counit identifies bounded
classical complexes with the triangulated image of the etale derived category;
qcqs direct-image comparison and the support triangle preserve that image. Exact
inverse image and the closed immersion counit give classicality on Z and then S.
The scalar annihilator gives local torsion there as well. No torsion-freeness of N,
compactness of S, or quotient-linear support construction is used. Zero modules,
n=0, c=0 and empty schemes satisfy the same argument. -/
theorem integral_reduction_support_amplitude
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    (S Z V : Scheme.{u}) (v : S ⟶ Z) (i : Z ⟶ X) (j : V ⟶ X)
    [IsOpenImmersion v] [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range j = (Set.range i)ᶜ)
    (hAdd : (closedModuleSectionsWithSupport (integralCoefficientRing l E) i j).Additive)
    (c : ℕ)
    (hc : (c : WithTop ℕ) = relativeCohomologicalDimension l (Fact.out : l.Prime) j)
    (N : pulledBackModuleObjects (integralCoefficientRing l E) X)
    (hN : IsConstantModelConstructible (integralCoefficientRing l E) X N) (n : ℕ) :
    let K := (upperStar (integralCoefficientRing l E) v).mapDerivedCategory.obj
      ((closedModuleSectionsWithSupport (integralCoefficientRing l E) i j).rightDerivedFunctor.obj
        ((integralReductionFunctor l E X (n + 1)).obj
          ((DerivedCategory.singleFunctor _ 0).obj N)))
    (∀ q : ℤ, q < -1 ∨ (c : ℤ) + 1 < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj K)) ∧
    (∀ q : ℤ,
      IsClassicalAbelian ((DerivedCategory.homologyFunctor _ q).obj K).X ∧
      IsEllPowerTorsion l (Fact.out : l.Prime)
        ((DerivedCategory.homologyFunctor _ q).obj K).X) := by
  have _ := hl
  let := abSheafNatColimits V
  let := abSheafNatColimits S
  have : (closedModuleSectionsWithSupport (integralCoefficientRing l E) i j).Additive := hAdd
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of D.k))
  have : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of D.k))
  have : IsNoetherian X := ⟨⟩
  let B := (integralReductionFunctor l E X (n + 1)).obj
    ((DerivedCategory.singleFunctor _ 0).obj N)
  have hB := reduction_bound l E X N n
  have hBc := reduction_classical l E X N hN n
  let U := Mod.forget (D := Sheaf (Scheme.ProEt.topology V) Ab.{u + 1})
    (AdicCompletion.ring l E V)
  have hJ (q : ℤ) :
      IsClassicalAbelian ((DerivedCategory.homologyFunctor _ q).obj
        (U.mapDerivedCategory.obj
          ((upperStar (integralCoefficientRing l E) j).mapDerivedCategory.obj B))) ∧
      IsEllPowerTorsion l (Fact.out : l.Prime)
        ((DerivedCategory.homologyFunctor _ q).obj
          (U.mapDerivedCategory.obj
            ((upperStar (integralCoefficientRing l E) j).mapDerivedCategory.obj B))) := by
    constructor
    · exact ab_classical_iso ((U.mapDerivedCategoryHomologyFunctorIso q).app _)
        (module_classical_derived_pullback (integralCoefficientRing l E) j B hBc q)
    · apply ell_torsion_of_annihilated l (Fact.out : l.Prime) _ (n + 1)
      exact functor_annihilator (DerivedCategory.homologyFunctor _ q) _ _
        (functor_annihilator U.mapDerivedCategory _ _
          (functor_annihilator (upperStar (integralCoefficientRing l E) j).mapDerivedCategory
            _ _ (reduction_annihilator l E X ((DerivedCategory.singleFunctor _ 0).obj N)
              (n + 1))))
  exact ⟨support_bound l E v i j hij c hc B hB hJ,
    fun q ↦ ⟨support_classical l E v i j hij c hc B hB hBc hJ q,
      support_torsion l E v i j ((DerivedCategory.singleFunctor _ 0).obj N) (n + 1) q⟩⟩

end AlgebraicGeometry.ProEtale.CondensedRing
