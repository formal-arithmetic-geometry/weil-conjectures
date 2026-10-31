/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.CoefficientLisseWeilExtension
public import WeilConjectures.AlgebraicGeometry.CondensedStrictWeilComplex
public import WeilConjectures.AlgebraicGeometry.HenselianBoundaryLocalData
public import WeilConjectures.AlgebraicGeometry.LisseQlbarRepresentations
public import WeilConjectures.AlgebraicGeometry.CoefficientHeart
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TransitionUnits
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Line
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
import WeilConjectures.DeligneLaumon.CondensedLisseFrobeniusLift
import WeilConjectures.DeligneLaumon.CondensedLisseRestrictionFullyFaithful
import WeilConjectures.DeligneLaumon.CondensedUnderlyingExtensionInertia
import WeilConjectures.AlgebraicGeometry.ContinuousLocallyFreePullbackSupplement
import all WeilConjectures.AlgebraicGeometry.CondensedFieldLfpLocalTriviality
import all WeilConjectures.AlgebraicGeometry.CondensedFieldContinuousRealization
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import all WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import all WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import all WeilConjectures.CategoryTheory.Monoidal.Conjugate
import all WeilConjectures.ConstructibleSheaf.Pullback
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import all WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
import all Mathlib.Topology.Category.Profinite.EffectiveEpi
import all WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
import all Mathlib.Condensed.TopComparison
import all WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
import all WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import all Mathlib.Topology.NoetherianSpace
import all WeilConjectures.AlgebraicGeometry.ProEtalePointComponentsMaps
import all WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import all WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import all Mathlib.AlgebraicGeometry.Sites.Proetale
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.Topology.Category.Profinite.AsLimit
import all Mathlib.CategoryTheory.Limits.Shapes.Products
import all Mathlib.Topology.Category.Profinite.CofilteredLimit
import all Mathlib.Topology.Connected.TotallyDisconnected
import all WeilConjectures.Topology.SpectralSpace.ConnectedComponent
import all WeilConjectures.AlgebraicGeometry.ProEtaleSheafificationWcontractibleSections
import all WeilConjectures.AlgebraicGeometry.PointLanAffineEvaluation
import all Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import all Mathlib.CategoryTheory.Whiskering
import all Mathlib.Algebra.Category.Ring.Basic
import all WeilConjectures.AlgebraicGeometry.PointLanFiniteProducts
import all WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation
import all Mathlib.AlgebraicGeometry.Limits
import all WeilConjectures.AlgebraicGeometry.FiniteCoproductLfpQcqs
import all WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductSections
import all WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import all WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import all WeilConjectures.CategoryTheory.Sites.MonObj
import all WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import all Mathlib.Analysis.Normed.Module.FiniteDimension
import all Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import all WeilConjectures.AlgebraicGeometry.LocallyClosedStratification
import all WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
import all WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.CategoryTheory.SiteInverseImageTensor
import all WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all Mathlib.CategoryTheory.Monoidal.Ring
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import all WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import all WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationCorank
import all WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationMatrix
import all Mathlib.LinearAlgebra.Matrix.Rank
import all WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationEvaluation
import all Mathlib.Algebra.Category.ModuleCat.Basic
import all WeilConjectures.AlgebraicGeometry.CondensedFieldRegularModuleScalars
import all WeilConjectures.AlgebraicGeometry.CondensedFieldEvaluationFunctors
import all WeilConjectures.AlgebraicGeometry.GeometricFieldProEtaleEvaluation
import all WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import all WeilConjectures.Mathlib.CategoryTheory.Adjunction.Reflective
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all WeilConjectures.AlgebraicGeometry.GeometricFieldProfiniteDenseSubsite
import all WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import all WeilConjectures.CategoryTheory.DenseSubsiteModuleRestriction
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import all WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
import all WeilConjectures.CategoryTheory.RingObjects.Ab
import all Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.AlgebraicGeometry.CondensedFieldGeometricRegularCoefficient
import all WeilConjectures.AlgebraicGeometry.ContinuousChartSchemeNaturality
import all WeilConjectures.AlgebraicGeometry.IntegralMatrixAnalyticData
import all WeilConjectures.AlgebraicGeometry.ContinuousCoefficientRealizations
import all WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientData
import all Mathlib.NumberTheory.Padics.PadicNumbers
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import all WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
import all Mathlib.Analysis.Normed.Algebra.Ultra
import all Mathlib.Topology.Algebra.Valued.NormedValued
import all Mathlib.Topology.Algebra.Ring.Ideal
import all Mathlib.Topology.ContinuousMap.Compact
import all Mathlib.NumberTheory.Padics.ProperSpace
import all WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
import all Mathlib.CategoryTheory.Abelian.ShortExact
import all WeilConjectures.AlgebraicGeometry.IntegralScalarContractive
import all Mathlib.Data.Matrix.Basic
import all WeilConjectures.AlgebraicGeometry.IntegralRegularCoefficientPullback
import all Mathlib.Algebra.Category.ModuleCat.Biproducts
import all Mathlib.Algebra.Category.ModuleCat.Kernels
import all Mathlib.AlgebraicGeometry.PullbackCarrier
import all Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import all WeilConjectures.AlgebraicGeometry.CondensedFieldRankDescent
import all Mathlib.AlgebraicGeometry.Morphisms.Flat
import all Mathlib.Topology.LocallyConstant.Basic
import all Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import all WeilConjectures.AlgebraicGeometry.ContinuousFieldCokernelLocalFree
import all WeilConjectures.AlgebraicGeometry.ContinuousFieldPresentationNormalForm
import all WeilConjectures.AlgebraicGeometry.ContinuousFieldMatrixSheafNormalForm
import all WeilConjectures.AlgebraicGeometry.ContinuousFieldMatrixElimination
import all Mathlib.Logic.Equiv.Set
import all Mathlib.Data.Fintype.Basic
import all Mathlib.Topology.ContinuousMap.Algebra
import all Mathlib.Analysis.Normed.Field.Lemmas
import all Mathlib.LinearAlgebra.Matrix.SchurComplement
import all WeilConjectures.Mathlib.LinearAlgebra.Matrix.Rank
import all WeilConjectures.Mathlib.LinearAlgebra.Matrix.SchurComplement

/-! # Extending a condensed lisse Weil sheaf across infinity

Source: latest blueprint, sec-deligne-laumon-a1/sk-lem-wft-curve-heart/
rem-dl-a1-conventions.md, unramifiedness paragraph; Stacks 0BSM, 0BTD, 0BSW.
(blueprint: lem-dl-a1-condensed-lisse-extension-inertia).

The opens are represented inside the standard projective line. The coefficient
objects, Weil pairs, normalized monodromy, and henselian inertia are the published
constructions. The local presentation can be made on the geometric curve: its
inertia is the same geometric inertia as that of the rational point over the finite
field. No arithmetic descent of the Weil sheaf is assumed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale AlgebraicGeometry.Scheme.FiniteEtale
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedLisseExtensionInertia

/-- Geometric base change of a model, with no finite-type assumption in the construction.
Source: the geometric-fibre convention of def-weil-finite-field-fiber.
(blueprint: lem-dl-a1-condensed-lisse-extension-inertia). -/
abbrev geometricModel (D : WeilConjectures.FiniteFieldDatum.{u})
    (T₀ : Over (Spec (.of D.k₀))) :=
  pullback T₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))

/-- The canonical map of geometric fibres induced by a map of models.
Source: base change in the unramifiedness paragraph of rem-dl-a1-conventions.
(blueprint: lem-dl-a1-condensed-lisse-extension-inertia). -/
def geometricMap (D : WeilConjectures.FiniteFieldDatum.{u})
    {T₀ S₀ : Over (Spec (.of D.k₀))} (f : T₀ ⟶ S₀) :
    geometricModel D T₀ ⟶ geometricModel D S₀ :=
  ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map f).left

/-- An open of the projective line as a model over the finite field.
Source: standard projective-line charts, def-sc-p1-standard.
(blueprint: lem-dl-a1-condensed-lisse-extension-inertia). -/
abbrev openModel (D : WeilConjectures.FiniteFieldDatum.{u})
    (U₀ : (ProjectiveLine (Spec (.of D.k₀))).Opens) : Over (Spec (.of D.k₀)) :=
  Over.mk (U₀.ι ≫ ProjectiveLine (Spec (.of D.k₀)) ↘ Spec (.of D.k₀))

/-- Inclusion between two open models, as a morphism over the finite field.
Source: the inclusion U_0 into C_0 in rem-dl-a1-conventions.
(blueprint: lem-dl-a1-condensed-lisse-extension-inertia). -/
def openInclusion (D : WeilConjectures.FiniteFieldDatum.{u})
    {U₀ C₀ : (ProjectiveLine (Spec (.of D.k₀))).Opens} (h : U₀ ≤ C₀) :
    openModel D U₀ ⟶ openModel D C₀ :=
  Over.homMk ((ProjectiveLine (Spec (.of D.k₀))).homOfLE h)
    ((Category.assoc _ _ _).symm.trans
      (congrArg (fun f ↦ f ≫ ProjectiveLine (Spec (.of D.k₀)) ↘ Spec (.of D.k₀))
        (Scheme.homOfLE_ι _ h)))

/-- The extension clause, using the canonical pullback comparison of a commuting square.
Source: rem-dl-a1-conventions, extension as a lisse Weil sheaf across infinity.
(blueprint: lem-dl-a1-condensed-lisse-extension-inertia). -/
@[irreducible] def HasLisseWeilExtension (l : ℕ) [Fact l.Prime]
    {U C : Scheme.{u}} (gU : U ≅ U) (gC : C ≅ C) (j : U ⟶ C)
    (F : CondensedRing.StrictWeil.WeilModule (Profinite.padicAlgClRingObj l) gU) : Prop :=
  HasLisseWeilExtensionForCoefficient (Profinite.padicAlgClRingObj l) gU gC j F

/-- The inertia clause on the actual normalized geometric-fibre representation.
Source: rem-dl-a1-conventions, equivalent inertia criterion; d-real-boundary's residue kernel.
(blueprint: lem-dl-a1-condensed-lisse-extension-inertia). -/
@[irreducible] def HasTrivialInertia (l : ℕ) [Fact l.Prime]
    {U C : Scheme.{u}} (gU : U ≅ U) (j : U ⟶ C)
    (F : CondensedRing.StrictWeil.WeilModule (Profinite.padicAlgClRingObj l) gU)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (b : Spec (.of Ω) ⟶ U) (x : C)
    (B : HenselianBoundaryLocalData j b x)
    (G : ProfiniteGrp.{u}) [∀ P, MulAction G ((fiber b).obj P)]
    (eG : G ≃ₜ* Aut (fiber b)) (R : LisseQlbar.Correspondence l b G) : Prop :=
  ∃ h : LisseQlbar.integralClosure l U F.carrier,
    ∀ σ : B.Ω ≃ₐ[B.K] B.Ω, σ ∈ B.residueAction.ker →
      (R.algebraic.functor.obj ⟨F.carrier, h⟩).ρ (eG.symm (B.decomposition σ)) = 1

set_option maxHeartbeats 0 in
-- Canonical sheaf-module categories require a larger elaboration budget.
private theorem lisse_iff_locallyFree
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}}
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    IsLisseCoefficientModule Λ M ↔ CondensedRing.LocallyFree (condensedRingObj Λ X) M := by
  constructor
  · rintro ⟨U, hU⟩
    refine ⟨U, fun i ↦ ?_⟩
    let φ := condensedPullbackHom Λ (U.f i)
    apply free_of_comap (inv φ)
    exact free_of_iso (hU i) ((Mod.extendScalarsIsoComapInv φ).app _)
  · rintro ⟨U, hU⟩
    refine ⟨U, fun i ↦ ?_⟩
    let φ := condensedPullbackHom Λ (U.f i)
    exact free_of_iso (free_comap (inv φ) (hU i))
      ((Mod.extendScalarsIsoComapInv φ).app _).symm

set_option maxHeartbeats 0 in
-- Canonical sheaf-module categories require a larger elaboration budget.
private theorem lisse_pullback
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : Y ⟶ X)
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (hM : IsLisseCoefficientModule Λ M) :
    IsLisseCoefficientModule Λ ((CondensedRing.upperStar Λ f).obj M) :=
  (lisse_iff_locallyFree Λ _).mpr
    (CondensedRing.locallyFree_upperStar Λ f ((lisse_iff_locallyFree Λ M).mp hM))

set_option maxHeartbeats 0 in
-- Canonical sheaf-module categories require a larger elaboration budget.
private theorem modelFrobenius_naturality (D : WeilConjectures.FiniteFieldDatum.{u})
    {T₀ S₀ : Over (Spec (.of D.k₀))} (f : T₀ ⟶ S₀) :
    (CondensedRing.StrictWeil.modelFrobenius D T₀).hom ≫ geometricMap D f =
      geometricMap D f ≫ (CondensedRing.StrictWeil.modelFrobenius D S₀).hom := by
  let := Fintype.ofFinite D.k₀
  apply pullback.hom_ext
  · simp only [Category.assoc, geometricMap, Over.pullback_map_left, pullback.lift_fst]
    simp only [← Category.assoc, CondensedRing.StrictWeil.modelFrobenius]
    rw [(D.galoisMap_projections _ _).1]
    rw [Category.assoc, (D.galoisMap_projections _ _).1]
    simp only [pullback.lift_fst]
  · simp only [Category.assoc, geometricMap, Over.pullback_map_left, pullback.lift_snd]
    simp only [CondensedRing.StrictWeil.modelFrobenius]
    rw [(D.galoisMap_projections _ _).2]
    rw [(D.galoisMap_projections _ _).2]
    rw [← Category.assoc, pullback.lift_snd]

set_option maxHeartbeats 0 in
-- Canonical sheaf-module categories require a larger elaboration budget.
private theorem frobenius_commutes (D : WeilConjectures.FiniteFieldDatum.{u})
    {T₀ S₀ : Over (Spec (.of D.k₀))} (f : T₀ ⟶ S₀)
    {U C : Scheme.{u}} (eU : U ≅ geometricModel D T₀)
    (eC : C ≅ geometricModel D S₀) :
    (eU ≪≫ CondensedRing.StrictWeil.modelFrobenius D T₀ ≪≫ eU.symm).hom ≫
        (eU.hom ≫ geometricMap D f ≫ eC.inv) =
      (eU.hom ≫ geometricMap D f ≫ eC.inv) ≫
        (eC ≪≫ CondensedRing.StrictWeil.modelFrobenius D S₀ ≪≫ eC.symm).hom := by
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc (CondensedRing.StrictWeil.modelFrobenius D T₀).hom,
    modelFrobenius_naturality, Category.assoc]

private theorem lift_isoAlgebra
    {A : Type*} [Category A] {B : Type*} [Category B]
    (J : A ⥤ B) (PC : A ⥤ A) (PU : B ⥤ B)
    (c : J ⋙ PU ≅ PC ⋙ J) (P : A → Prop)
    (hJ : ∀ X Y, P X → P Y →
      Function.Bijective (J.map : (X ⟶ Y) → (J.obj X ⟶ J.obj Y)))
    (F : CategoryTheory.Endofunctor.IsoAlgebra PU) (L : A)
    (hL : P L) (hPL : P (PC.obj L)) (e : J.obj L ≅ F.carrier) :
    ∃ K : CategoryTheory.Endofunctor.IsoAlgebra PC, P K.carrier ∧
      ∃ e : J.obj K.carrier ≅ F.carrier,
        PU.map e.hom ≫ F.str.hom = c.hom.app K.carrier ≫ J.map K.str.hom ≫ e.hom := by
  obtain ⟨α, hα⟩ := CategoryTheory.exists_frobenius_iso_of_map_bijective J PC PU c
    P hJ hL hPL F.str e
  exact ⟨CategoryTheory.Endofunctor.IsoAlgebra.mk L α, hL, e, hα⟩

private theorem isoAlgebra_extension_intro
    {A : Type*} [Category A] {B : Type*} [Category B]
    (J : A ⥤ B) (PC : A ⥤ A) (PU : B ⥤ B)
    (H : Prop) (c : H → (J ⋙ PU ≅ PC ⋙ J)) (P : A → Prop)
    (hJ : ∀ X Y, P X → P Y →
      Function.Bijective (J.map : (X ⟶ Y) → (J.obj X ⟶ J.obj Y)))
    (F : CategoryTheory.Endofunctor.IsoAlgebra PU) (L : A)
    (hL : P L) (hPL : P (PC.obj L)) (e : J.obj L ≅ F.carrier) (h : H) :
    CategoryTheory.HasIsoAlgebraExtension J PC PU H c P F := by
  obtain ⟨K, hK, e, he⟩ := lift_isoAlgebra J PC PU (c h) P hJ F L hL hPL e
  exact ⟨K, hK, h, e, he⟩

private theorem isoAlgebra_extension_forget
    {A : Type*} [Category A] {B : Type*} [Category B]
    (J : A ⥤ B) (PC : A ⥤ A) (PU : B ⥤ B)
    (H : Prop) (c : H → (J ⋙ PU ≅ PC ⋙ J)) (P : A → Prop)
    (F : CategoryTheory.Endofunctor.IsoAlgebra PU)
    (h : CategoryTheory.HasIsoAlgebraExtension J PC PU H c P F) :
    ∃ L : A, P L ∧ Nonempty (J.obj L ≅ F.carrier) := by
  obtain ⟨K, hK, _, e, _⟩ := h
  exact ⟨K.carrier, hK, ⟨e⟩⟩

attribute [local irreducible] CondensedRing.upperStar CondensedRing.upperStarComp
  CondensedRing.upperStarCongr

set_option maxHeartbeats 200000 in
-- Instantiate the extension condition while keeping the comparison as an argument.
private theorem generic_weil_extension_of_underlying
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {U C : Scheme.{u}} (gU : U ≅ U) (gC : C ≅ C) (j : U ⟶ C)
    (hcomm : gU.hom ≫ j = j ≫ gC.hom)
    (hmap : ∀ L M, IsLisseCoefficientModule Λ L → IsLisseCoefficientModule Λ M →
      Function.Bijective ((CondensedRing.upperStar Λ j).map : (L ⟶ M) → _))
    (F : CondensedRing.StrictWeil.WeilModule Λ gU)
    (L : Mod (Sheaf (Scheme.ProEt.topology C) Ab.{u + 1}) (condensedRingObj Λ C))
    (hL : IsLisseCoefficientModule Λ L)
    (e : (CondensedRing.upperStar Λ j).obj L ≅ F.carrier) :
    HasLisseWeilExtensionForCoefficient Λ gU gC j F := by
  unfold HasLisseWeilExtensionForCoefficient
  exact isoAlgebra_extension_intro _ _ _ _ _ _ hmap F L hL
    (lisse_pullback Λ gC.hom hL) e hcomm

private theorem generic_weil_extension_forget
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {U C : Scheme.{u}} (gU : U ≅ U) (gC : C ≅ C) (j : U ⟶ C)
    (F : CondensedRing.StrictWeil.WeilModule Λ gU)
    (h : HasLisseWeilExtensionForCoefficient Λ gU gC j F) :
    ∃ L : Mod (Sheaf (Scheme.ProEt.topology C) Ab.{u + 1}) (condensedRingObj Λ C),
      IsLisseCoefficientModule Λ L ∧
        Nonempty ((CondensedRing.upperStar Λ j).obj L ≅ F.carrier) := by
  unfold HasLisseWeilExtensionForCoefficient at h
  exact isoAlgebra_extension_forget _ _ _ _ _ _ F h

set_option maxHeartbeats 200000 in
-- Keep the canonical comparison in separately checked categorical lemmas.
private theorem weil_extension_of_underlying
    (l : ℕ) [Fact l.Prime] {U C : Scheme.{u}}
    (gU : U ≅ U) (gC : C ≅ C) (j : U ⟶ C)
    (hcomm : gU.hom ≫ j = j ≫ gC.hom)
    (hmap : ∀ L M,
      IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) L →
      IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) M →
      Function.Bijective ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) j).map :
        (L ⟶ M) → _))
    (F : CondensedRing.StrictWeil.WeilModule (Profinite.padicAlgClRingObj l) gU)
    (L : Mod (Sheaf (Scheme.ProEt.topology C) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj l) C))
    (hL : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) L)
    (e : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) j).obj L ≅ F.carrier) :
    HasLisseWeilExtension l gU gC j F := by
  unfold HasLisseWeilExtension
  exact generic_weil_extension_of_underlying (Profinite.padicAlgClRingObj l)
    gU gC j hcomm hmap F L hL e

set_option maxHeartbeats 0 in
-- Elaborate the actual coefficient-module functors and their comparisons.
/-- Extension as a lisse Weil sheaf is equivalent to trivial geometric inertia.
Source: rem-dl-a1-conventions, the sentence beginning "A lisse Weil sheaf F on U_0
is unramified at infinity"; Stacks 0BTD and 0BSW.
(blueprint: lem-dl-a1-condensed-lisse-extension-inertia).

Proof: apply condensed_underlying_extension_inertia to the carrier. Its proof
combines the normalized condensed extension-kernel criterion with the geometric
henselian inertia-kernel formula and closedness of a continuous representation's
kernel. Forgetting a Weil extension gives an underlying lisse extension, hence
trivial inertia. Conversely obtain an underlying lisse extension L and its actual
restriction isomorphism e. Pullback preserves lisseness: transport between the
coefficient and raw LocallyFree predicates, then apply locallyFree_upperStar.
The native coefficient encoding and its pullback comparison transport the known
native dense-open Hom bijections to actual condensed restriction. Naturality of
the geometric Galois map, checked on the two fibre-product projections, shows that
the specified Frobenius maps commute with j. Conjugate the given Weil isomorphism
by e and the canonical pullback comparison, then lift it and its inverse through
the Hom bijections. Faithfulness proves the two inverse identities, giving the
Weil structure on L and exactly the required compatibility equation. The generic
extension predicates only keep these same existential witnesses and canonical
comparison folded while specializing the coefficient ring. The integrality
witness in HasTrivialInertia is supplied by the underlying equivalence; no lattice
is chosen for, or assumed stable under, the Frobenius isomorphism.
-/
theorem condensed_lisse_extension_inertia
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (_hl : l ≠ D.p)
    (U₀ C₀ : (ProjectiveLine (Spec (.of D.k₀))).Opens)
    (_hU : U₀ ≤ (ProjectiveLine.affineChart (Spec (.of D.k₀))).opensRange)
    (_hdense : Dense (U₀ : Set (ProjectiveLine (Spec (.of D.k₀)))))
    (_hC : (C₀ : Set (ProjectiveLine (Spec (.of D.k₀)))) =
      (U₀ : Set (ProjectiveLine (Spec (.of D.k₀)))) ∪
        Set.range (ProjectiveLine.infinity (Spec (.of D.k₀))))
    (hUC : U₀ ≤ C₀)
    (U C : Scheme.{u}) (eU : U ≅ geometricModel D (openModel D U₀))
    (eC : C ≅ geometricModel D (openModel D C₀))
    (j : U ⟶ C)
    (_hj : j = eU.hom ≫ geometricMap D (openInclusion D hUC) ≫ eC.inv)
    (gU : U ≅ U) (gC : C ≅ C)
    (_hgU : gU = eU ≪≫ CondensedRing.StrictWeil.modelFrobenius D (openModel D U₀) ≪≫
      eU.symm)
    (_hgC : gC = eC ≪≫ CondensedRing.StrictWeil.modelFrobenius D (openModel D C₀) ≪≫
      eC.symm)
    (F : CondensedRing.StrictWeil.WeilModule (Profinite.padicAlgClRingObj l) gU)
    (_hF : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) F.carrier)
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (b : Spec (.of Ω) ⟶ U)
    (_hb : IsGenericPoint (b (IsLocalRing.closedPoint Ω)) Set.univ)
    (x : C)
    (_hx : (pullback.fst (openModel D C₀).hom
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))) (eC.hom x) ∉
      Set.range ((ProjectiveLine (Spec (.of D.k₀))).homOfLE hUC))
    (B : HenselianBoundaryLocalData j b x)
    (G : ProfiniteGrp.{u}) [∀ P, MulAction G ((fiber b).obj P)]
    (eG : G ≃ₜ* Aut (fiber b))
    (_haction : ∀ (g : G) (P : U.FiniteEtale) (z : (fiber b).obj P),
      g • z = (eG g).hom.app P z)
    (R : LisseQlbar.Correspondence l b G) :
    HasLisseWeilExtension l gU gC j F ↔ HasTrivialInertia l gU j F b x B G eG R := by
  have underlying := condensed_underlying_extension_inertia D l U₀ C₀ _hl _hU _hdense _hC
    hUC U C eU eC (openInclusion D hUC) rfl j _hj F.carrier _hF Ω b _hb x _hx B G eG
    _haction R
  constructor
  · intro h
    unfold HasLisseWeilExtension at h
    unfold HasTrivialInertia
    exact underlying.mp (generic_weil_extension_forget _ gU gC j F h)
  · intro h
    unfold HasTrivialInertia at h
    obtain ⟨L, hL, ⟨e⟩⟩ := underlying.mpr h
    have hcomm : gU.hom ≫ j = j ≫ gC.hom := by
      rw [_hgU, _hgC, _hj]
      exact frobenius_commutes D (openInclusion D hUC) eU eC
    exact weil_extension_of_underlying l gU gC j hcomm
      (fun A M hA hM ↦ condensed_lisse_restriction_map_bijective D l U₀ C₀ _hl _hdense
        hUC U C eU eC (openInclusion D hUC) rfl j _hj A M hA hM) F L hL e

end AlgebraicGeometry.ProEtale.CondensedLisseExtensionInertia
