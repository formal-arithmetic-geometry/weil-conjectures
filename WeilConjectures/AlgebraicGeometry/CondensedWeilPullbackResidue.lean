/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedWeilReality
public import WeilConjectures.AlgebraicGeometry.ConstantExtensionWeilHeartData
public import WeilConjectures.AlgebraicGeometry.CondensedStrictWeilComplex
public import WeilConjectures.AlgebraicGeometry.CoefficientHeart
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.BaseChange
import WeilConjectures.AlgebraicGeometry.PullbackConstantModelConstructible
import all WeilConjectures.AlgebraicGeometry.DeligneLaumonCondensedFibres
import all WeilConjectures.AlgebraicGeometry.FiniteEtaleLocallyFreeModels
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import all WeilConjectures.CategoryTheory.ModuleObjects.Free
import all Mathlib.AlgebraicGeometry.Morphisms.Etale
import all Mathlib.AlgebraicGeometry.Morphisms.Finite
import all WeilConjectures.AlgebraicGeometry.FiniteEtaleEtaleLocalSplit
import all WeilConjectures.AlgebraicGeometry.SplitProEtaleModuleProductMap
import all Mathlib.CategoryTheory.Limits.Shapes.Products
import all WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
import all WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import all WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import all Mathlib.AlgebraicGeometry.Sites.Proetale
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
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
import all WeilConjectures.CategoryTheory.Monoidal.Conjugate
import all WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import all WeilConjectures.CategoryTheory.Sites.MonObj
import all WeilConjectures.AlgebraicGeometry.SplitProEtaleAbelianProductMap
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Mathlib.CategoryTheory.Adjunction.Unique
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso
import all WeilConjectures.Mathlib.AlgebraicGeometry.PullbackCarrier
import all Mathlib.AlgebraicGeometry.Limits
import all WeilConjectures.AlgebraicGeometry.CondensedConstructibleSerre
import all WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import all WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
import all Mathlib.NumberTheory.Padics.PadicNumbers
import all Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import all Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import all Mathlib.Algebra.Field.ULift
import all Mathlib.CategoryTheory.Sites.EpiMono
import all WeilConjectures.ConstructibleSheaf.Refinement
import all WeilConjectures.AlgebraicGeometry.CondensedFieldLfpLocalTriviality
import all WeilConjectures.AlgebraicGeometry.CondensedFieldContinuousRealization
import all WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import all WeilConjectures.ConstructibleSheaf.Pullback
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
import all Mathlib.Topology.Category.Profinite.AsLimit
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
import all WeilConjectures.AlgebraicGeometry.FiniteCoproductLfpQcqs
import all WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductSections
import all WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import all WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import all WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import all Mathlib.Analysis.Normed.Module.FiniteDimension
import all Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import all WeilConjectures.AlgebraicGeometry.LocallyClosedStratification
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
import all WeilConjectures.AlgebraicGeometry.CondensedQbarLfpLocalTriviality
import all WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
import all WeilConjectures.AlgebraicGeometry.CondensedQbarLfpMatrixRefinement
import all WeilConjectures.AlgebraicGeometry.CondensedQbarFunctionPresentations
import all Mathlib.LinearAlgebra.Matrix.ToLin
import all WeilConjectures.AlgebraicGeometry.CondensedQbarFunctionCoefficients
import all WeilConjectures.AlgebraicGeometry.CondensedQbarCoefficientConstruction
import all WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
import all WeilConjectures.CategoryTheory.Monoidal.Mod.EvaluationPairing
import all WeilConjectures.AlgebraicGeometry.CondensedQbarScalarPullback
import all WeilConjectures.AlgebraicGeometry.CondensedQbarFieldFiberExtension
import all WeilConjectures.AlgebraicGeometry.CondensedQbarFieldEvaluationLinearity
import all WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal
import all WeilConjectures.AlgebraicGeometry.CondensedQbarFieldCoefficientSquare
import all WeilConjectures.AlgebraicGeometry.CondensedQbarFieldPointCoefficientValue
import all WeilConjectures.AlgebraicGeometry.CondensedCoefficientPointUnitPasting
import all WeilConjectures.AlgebraicGeometry.CondensedQbarLfpCoverComposition
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FinitelyPresentedStalk
import all WeilConjectures.AlgebraicGeometry.ConstantExtensionWeilHeartData

/-! # Exact condensed Weil pullback and residue-degree Frobenius

Source: latest blueprint, sec-deligne-laumon-general/sk-i-dl-general-real/
thm-zl-real-mixed-by-curves.proof.md, paragraphs 1--4 and 7
(blueprint: lem-zl-condensed-pullback-frobenius).

The source model is over the fixed subfield k_m of k; f₀ is a morphism over k₀
from that model with its restricted structure map. The geometric map is its literal
pullback lift. Its Weil structure uses the ordered m-fold iterate and the canonical
module pullback square. Every module is over the existing finite-subextension-valued
condensed ring pulled back from the point.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open CategoryTheory.Endofunctor
open scoped CategoryTheory.Obj
namespace WeilConjectures.CondensedWeil.Pullback

/-- Canonical composition of coefficient pullbacks, before choosing Weil data.
Source: latest blueprint, paragraphs 1--3
(blueprint: lem-zl-condensed-pullback-frobenius). -/
@[irreducible] def coefficientComparison (l : ℕ) [Fact l.Prime]
    {X Y Z : Scheme.{u}} (f : Y ⟶ X) (p : Z ⟶ Y) (q : Z ⟶ X) (hc : p ≫ f = q)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj l) X)) :
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) p).obj
        ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) f).obj M) ≅
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) q).obj M :=
  ((CondensedRing.upperStarComp (Profinite.padicAlgClRingObj l) p f).symm.app M) ≪≫
    (CondensedRing.upperStarCongr (Profinite.padicAlgClRingObj l) hc).app M

/-- Canonical coefficient composition after geometric-field evaluation.
Source: latest blueprint, paragraphs 2--3
(blueprint: lem-zl-condensed-pullback-frobenius). -/
@[irreducible] def evaluatedComparison (K : Type u) [Field K] [IsAlgClosed K]
    (l : ℕ) [Fact l.Prime] {X Y : Scheme.{u}} (f : Y ⟶ X)
    (p : Spec (.of K) ⟶ Y) (q : Spec (.of K) ⟶ X) (hc : p ≫ f = q)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj l) X)) :
    (CondensedQbarGeometricEvaluation.fieldFiber K l).obj
        ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) p).obj
          ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) f).obj M)) ≅
      (CondensedQbarGeometricEvaluation.fieldFiber K l).obj
        ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) q).obj M) :=
  (CondensedQbarGeometricEvaluation.fieldFiber K l).mapIso
    (coefficientComparison l f p q hc M)

/-- Transport of a specified isomorphism along an equality of its source object.
Source: latest blueprint, canonical geometric-fibre comparison in paragraph 3
(blueprint: lem-zl-condensed-pullback-frobenius). -/
@[irreducible] def transportComparison
    {C : Type v} [Category.{w} C] {A B E : C} (h : A = B) (e : B ≅ E) : A ≅ E :=
  eqToIso h ≪≫ e

/-- Canonical transport of the target of an isomorphism.
Source: latest blueprint, paragraph 3
(blueprint: lem-zl-condensed-pullback-frobenius). -/
@[irreducible] def transportTarget
    {C : Type v} [Category.{w} C] {A B E : C} (h : B = E) (e : A ≅ B) : A ≅ E :=
  e ≪≫ eqToIso h

private theorem geometric_compact (E : FiniteFieldDatum.{u}) (X₀ : Over (Spec (.of E.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] :
    CompactSpace (E.geometricFiber X₀).left := by
  change CompactSpace ((pullback X₀.hom
    (Spec.map (CommRingCat.ofHom (algebraMap E.k₀ E.k)))) : Scheme.{u})
  exact QuasiCompact.compactSpace_of_compactSpace (pullback.snd X₀.hom _)

private theorem geometric_quasiseparated (E : FiniteFieldDatum.{u}) (X₀ : Over (Spec (.of E.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom] :
    QuasiSeparatedSpace (E.geometricFiber X₀).left := by
  change QuasiSeparatedSpace ((pullback X₀.hom
    (Spec.map (CommRingCat.ofHom (algebraMap E.k₀ E.k)))) : Scheme.{u})
  exact quasiSeparatedSpace_of_quasiSeparated (pullback.snd X₀.hom _)

private theorem coefficient_pullback (l : ℕ) [Fact l.Prime] :
    ConstantModelPullbackStatement (Profinite.padicAlgClRingObj.{u} l) := by
  apply pullback_constantModelConstructible l (Profinite.padicAlgClCondensedRing l)
  exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))

private theorem ordered_naturality {C : Type v} [Category.{w} C] {X : Scheme.{u}}
    (g : X ⟶ X) (P : (X ⟶ X) → C ⥤ C)
    (comp : ∀ f h : X ⟶ X, P (f ≫ h) ≅ P h ⋙ P f)
    (M N : C) (θ : (P g).obj M ≅ M) (η : (P g).obj N ≅ N) (f : M ⟶ N)
    (hf : (P g).map f ≫ η.hom = θ.hom ≫ f) (n : ℕ) :
    (P (localPositivePower g n)).map f ≫ (iterateAux g P comp N η n).hom =
      (iterateAux g P comp M θ n).hom ≫ f := by
  induction n with
  | zero => exact hf
  | succ n ih =>
    simp only [iterateAux, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
      Category.assoc]
    rw [NatTrans.naturality_assoc]
    simp only [Functor.comp_map]
    rw [← Functor.map_comp_assoc, hf, Functor.map_comp_assoc, ih]

private theorem square_naturality {C : Type v} [Category.{w} C]
    {E : Type*} [Category* E] (L : C ⥤ E) (G : C ⥤ C) (H : E ⥤ E)
    (c : G ⋙ L ≅ L ⋙ H) (M N : C)
    (θ : G.obj M ≅ M) (η : G.obj N ≅ N) (f : M ⟶ N)
    (hf : G.map f ≫ η.hom = θ.hom ≫ f) :
    H.map (L.map f) ≫ (c.symm.app N ≪≫ L.mapIso η).hom =
      (c.symm.app M ≪≫ L.mapIso θ).hom ≫ L.map f := by
  dsimp only [Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Functor.mapIso_hom]
  change (L ⋙ H).map f ≫ c.inv.app N ≫ _ = _
  rw [NatTrans.naturality_assoc]
  simp only [Functor.comp_map]
  rw [← Functor.map_comp, hf, Functor.map_comp, Category.assoc]


private theorem fixedMap_exact {C : Type*} [Category* C] [Abelian C]
    {E : Type*} [Category* E] [Abelian E]
    (G : C ⥤ C) (H : E ⥤ E) [G.IsEquivalence] [H.IsEquivalence]
    [G.Additive] [H.Additive]
    (L : C ⥤ E) [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (R : IsoAlgebra G ⥤ IsoAlgebra H)
    (e : R ⋙ IsoAlgebra.forget H ≅ IsoAlgebra.forget G ⋙ L) :
    PreservesFiniteLimits R ∧ PreservesFiniteColimits R := by
  have : PreservesFiniteLimits (R ⋙ IsoAlgebra.forget H) :=
    preservesFiniteLimits_of_natIso e.symm
  have : PreservesFiniteColimits (R ⋙ IsoAlgebra.forget H) :=
    preservesFiniteColimits_of_natIso e.symm
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves R (IsoAlgebra.forget H),
    preservesFiniteColimits_of_reflects_of_preserves R (IsoAlgebra.forget H)⟩

private theorem restrictedMap_exact {C : Type*} [Category* C]
    {E : Type*} [Category* E] (P : ObjectProperty C) (Q : ObjectProperty E)
    (L : C ⥤ E) [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits P.ι] [PreservesFiniteColimits P.ι]
    (h : ∀ M : P.FullSubcategory, Q (L.obj M.obj)) :
    PreservesFiniteLimits (ObjectProperty.lift Q (P.ι ⋙ L) h) ∧
      PreservesFiniteColimits (ObjectProperty.lift Q (P.ι ⋙ L) h) := by
  let R := ObjectProperty.lift Q (P.ι ⋙ L) h
  have : PreservesFiniteLimits (R ⋙ Q.ι) := by
    change PreservesFiniteLimits (P.ι ⋙ L)
    infer_instance
  have : PreservesFiniteColimits (R ⋙ Q.ι) := by
    change PreservesFiniteColimits (P.ι ⋙ L)
    infer_instance
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves R Q.ι,
    preservesFiniteColimits_of_reflects_of_preserves R Q.ι⟩

private theorem exact_filtration {C : Type*} [Category* C] [Abelian C]
    {E : Type*} [Category* E] [Abelian E]
    (L : C ⥤ E) [PreservesFiniteLimits L] [PreservesFiniteColimits L] [L.Additive]
    (P : C → Prop) (Q : E → Prop)
    (hL : ∀ M, P M → Q (L.obj M))
    (hQ : ∀ {M N : E}, (M ≅ N) → Q N → Q M)
    (M : C) (t : ℕ) (G : Fin (t + 1) → C)
    (a : ∀ i : Fin t, G i.castSucc ⟶ G i.succ)
    (hz : IsZero (G 0)) (he : Nonempty (G (Fin.last t) ≅ M))
    (hmono : ∀ i, Mono (a i)) :
    IsZero (L.obj (G 0)) ∧
    Nonempty (L.obj (G (Fin.last t)) ≅ L.obj M) ∧
    (∀ i, Mono (L.map (a i))) ∧
    (∀ i, Nonempty (cokernel (L.map (a i)) ≅ L.obj (cokernel (a i)))) ∧
    (∀ i, P (G i) → Q (L.obj (G i))) ∧
    (∀ i, P (cokernel (a i)) → Q (cokernel (L.map (a i)))) := by
  classical
  have hmono' (i : Fin t) : Mono (a i) := hmono i
  exact ⟨L.map_isZero hz, ⟨L.mapIso he.some⟩, fun i ↦ inferInstance,
    fun i ↦ ⟨(PreservesCokernel.iso L (a i)).symm⟩,
    fun i ↦ hL (G i),
    fun i h ↦ hQ (PreservesCokernel.iso L (a i)).symm (hL _ h)⟩


private theorem fixedRank_pullback
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : Y ⟶ X)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (r : ℕ) (U : Scheme.Cover.{u} Scheme.proetalePrecoverage X)
    (hU : ∀ i, Nonempty ((CondensedRing.upperStar Λ (U.f i)).obj M ≅
      Mod.finiteFree (condensedRingObj Λ (U.X i)) r)) :
    ∀ i, Nonempty ((CondensedRing.upperStar Λ (pullback.fst f (U.f i))).obj
      ((CondensedRing.upperStar Λ f).obj M) ≅
      Mod.finiteFree (condensedRingObj Λ (pullback f (U.f i))) r) := by
  intro i
  let sq : CommSq (pullback.fst f (U.f i)) (pullback.snd f (U.f i)) f (U.f i) :=
    ⟨pullback.condition⟩
  exact ⟨((CondensedRing.upperStarSquareComparison Λ sq).symm.app M) ≪≫
    (CondensedRing.upperStar Λ (pullback.snd f (U.f i))).mapIso (hU i).some ≪≫
    Mod.finiteFreeIsoMap _ (CondensedRing.upperStarObjRegularIso Λ
      (pullback.snd f (U.f i))) r⟩


private theorem pullback_heq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y Z : Scheme.{u}} (h : Y = Z)
    (p : Y ⟶ X) (q : Z ⟶ X) (hp : HEq p q) :
    HEq (CondensedRing.upperStar Λ p) (CondensedRing.upperStar Λ q) := by
  subst Z
  cases hp
  rfl

variable (D : FiniteFieldDatum.{u}) (m : ℕ) (hm : 1 ≤ m)
  (T₀ : Over (Spec (.of D.k₀))) [hTft : LocallyOfFiniteType T₀.hom] [hTqc : QuasiCompact T₀.hom]
  [hTs : IsSeparated T₀.hom]
  (Y₀ : Over (Spec (.of (constantExtensionDatum D m hm).k₀)))
  [hYft : LocallyOfFiniteType Y₀.hom] [hYqc : QuasiCompact Y₀.hom]
  [hYs : IsSeparated Y₀.hom]
  (f₀ : Over.mk (Y₀.hom ≫
    Spec.map (CommRingCat.ofHom (D.extensionEmbedding m hm))) ⟶ T₀)

include hTs hYs

set_option linter.unusedSectionVars false in
/-- The two components of the induced geometric map are compatible.
Source: latest blueprint, paragraphs 1--3
(blueprint: lem-zl-condensed-pullback-frobenius).
Proof: compose the source pullback projection equation with Spec(k_m → k₀),
use the defining equation of f₀, and use that k₀ → k_m → k is its fixed inclusion. -/
theorem geometricMap_compatible :
    (pullback.fst Y₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap
        (constantExtensionDatum D m hm).k₀ (constantExtensionDatum D m hm).k))) ≫
      f₀.left) ≫ T₀.hom =
    ((constantExtensionDatum D m hm).geometricFiber Y₀).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)) := by
  have hcomp : (D.extensionSubfield m hm).subtype.comp (D.extensionEmbedding m hm) =
      algebraMap D.k₀ D.k :=
    (FiniteField.exists_unique_subfield_of_closure D.p D.a D.q D.prime D.exponent_pos
      D.cardinality_eq D.k₀ D.card_base D.k m hm).choose_spec.2.2.2.2.2.2.choose_spec
  rw [Category.assoc, Over.w f₀]
  change pullback.fst _ _ ≫ (Y₀.hom ≫ _) = pullback.snd _ _ ≫ _
  have hcomp' : (algebraMap (constantExtensionDatum D m hm).k₀
      (constantExtensionDatum D m hm).k).comp (D.extensionEmbedding m hm) =
      algebraMap D.k₀ D.k := hcomp
  rw [← Category.assoc, pullback.condition, Category.assoc,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp, hcomp']

/-- The induced f:Y → T, using the fixed inclusion k_m ⊂ k.
Source: latest blueprint, paragraphs 1--3
(blueprint: lem-zl-condensed-pullback-frobenius). -/
def geometricMap : ((constantExtensionDatum D m hm).geometricFiber Y₀).left ⟶
    (D.geometricFiber T₀).left :=
  pullback.lift
    (pullback.fst Y₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap
        (constantExtensionDatum D m hm).k₀ (constantExtensionDatum D m hm).k))) ≫ f₀.left)
    ((constantExtensionDatum D m hm).geometricFiber Y₀).hom
    (geometricMap_compatible D m hm T₀ Y₀ f₀)

/-- The source q^m-Frobenius commutes with f and the mth target Frobenius power.
Source: latest blueprint, paragraphs 1--3
(blueprint: lem-zl-condensed-pullback-frobenius).
Proof: the two composites have the same model projection, since Frobenius fixes the
models. Their closure projection is Spec(z ↦ z^(1/q^m)) on both sides. The mth
geometric field Frobenius fixes k_m. Pullback uniqueness gives the square. -/
theorem geometricMap_frobenius :
    CommSq ((constantExtensionDatum D m hm).geometricFrobenius Y₀).hom
      (geometricMap D m hm T₀ Y₀ f₀) (geometricMap D m hm T₀ Y₀ f₀)
      (localPositivePower (D.geometricFrobenius T₀).hom (m - 1))  := by
  let := Fintype.ofFinite D.k₀
  let : Algebra (constantExtensionDatum D m hm).k₀ D.k :=
    (constantExtensionDatum D m hm).algebra_closure
  let : IsAlgClosure (constantExtensionDatum D m hm).k₀ D.k :=
    (constantExtensionDatum D m hm).isAlgClosure
  let := Fintype.ofFinite (constantExtensionDatum D m hm).k₀
  have hn := (constantExtensionDatum D m hm).galoisMap_projections Y₀.hom
    (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic
      (constantExtensionDatum D m hm).k₀ D.k)
  have ho := WeilConjectures.frobeniusPower_projections D T₀ (m - 1)
  have hm' : m - 1 + 1 = m := Nat.sub_add_cancel hm
  have he := WeilConjectures.extensionFrobenius_power D m hm
  refine ⟨?_⟩
  apply pullback.hom_ext
  · simp only [Category.assoc]
    rw [ho.1]
    simp only [geometricMap, pullback.lift_fst]
    exact hn.1 =≫ f₀.left
  · simp only [Category.assoc]
    rw [ho.2, hm']
    simp only [geometricMap, pullback.lift_snd, pullback.lift_snd_assoc]
    rw [← he]
    exact hn.2

variable (l : ℕ) [Fact l.Prime]

/-- Pullback of a Weil object: canonical square comparison followed by f*theta^[m].
Source: latest blueprint, paragraphs 1--3
(blueprint: lem-zl-condensed-pullback-frobenius). -/
def object (M : WeilModule D l T₀) : WeilModule (constantExtensionDatum D m hm) l Y₀ :=
  IsoAlgebra.mk
    ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
      (geometricMap D m hm T₀ Y₀ f₀)).obj M.carrier)
    (((CondensedRing.upperStarSquareComparison (Profinite.padicAlgClRingObj l)
      (geometricMap_frobenius D m hm T₀ Y₀ f₀)).symm.app M.carrier) ≪≫
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
        (geometricMap D m hm T₀ Y₀ f₀)).mapIso
          (iterate (Profinite.padicAlgClRingObj l) (D.geometricFrobenius T₀).hom
            M.carrier M.str (m - 1)))

/-- Pullback of a Weil arrow commutes with the induced source Weil structures.
Source: latest blueprint, paragraph 2
(blueprint: lem-zl-condensed-pullback-frobenius).
Proof: induction on the ordered iterate gives the equivariance equation for theta^[m].
Apply f* and naturality of the canonical square comparison to this equation. -/
theorem map_equivariance {M N : WeilModule D l T₀} (a : M ⟶ N) :
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
      ((constantExtensionDatum D m hm).geometricFrobenius Y₀).hom).map
        ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
          (geometricMap D m hm T₀ Y₀ f₀)).map a.hom.f) ≫
        (object D m hm T₀ Y₀ f₀ l N).str.hom =
      (object D m hm T₀ Y₀ f₀ l M).str.hom ≫
        (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
          (geometricMap D m hm T₀ Y₀ f₀)).map a.hom.f  := by
  apply square_naturality
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
      (geometricMap D m hm T₀ Y₀ f₀))
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
      (localPositivePower (D.geometricFrobenius T₀).hom (m - 1)))
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
      ((constantExtensionDatum D m hm).geometricFrobenius Y₀).hom)
    (CondensedRing.upperStarSquareComparison (Profinite.padicAlgClRingObj l)
      (geometricMap_frobenius D m hm T₀ Y₀ f₀)) M.carrier N.carrier
    (iterate (Profinite.padicAlgClRingObj l) (D.geometricFrobenius T₀).hom
      M.carrier M.str (m - 1))
    (iterate (Profinite.padicAlgClRingObj l) (D.geometricFrobenius T₀).hom
      N.carrier N.str (m - 1)) a.hom.f
  exact ordered_naturality _ _ _ _ _ _ _ _ a.hom.h (m - 1)

/-- The actual module inverse-image map, with its Weil equivariance.
Source: latest blueprint, paragraph 2
(blueprint: lem-zl-condensed-pullback-frobenius). -/
def map {M N : WeilModule D l T₀} (a : M ⟶ N) :
    object D m hm T₀ Y₀ f₀ l M ⟶ object D m hm T₀ Y₀ f₀ l N :=
  ObjectProperty.homMk
    { f := (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
        (geometricMap D m hm T₀ Y₀ f₀)).map a.hom.f
      h := map_equivariance D m hm T₀ Y₀ f₀ l a }

/-- The induced arrow construction preserves identities.
Source: latest blueprint, paragraph 2
(blueprint: lem-zl-condensed-pullback-frobenius).
Proof: forgetting the Weil structure is faithful; the underlying arrow is f*(id)=id. -/
theorem map_identity (M : WeilModule D l T₀) :
    map D m hm T₀ Y₀ f₀ l (𝟙 M) = 𝟙 (object D m hm T₀ Y₀ f₀ l M) := by
  apply IsoAlgebra.hom_ext
  simp [map, object]

/-- The induced arrow construction preserves composites.
Source: latest blueprint, paragraph 2
(blueprint: lem-zl-condensed-pullback-frobenius).
Proof: forgetting the Weil structure is faithful; the underlying equation is functoriality
of module inverse image on a composable pair of arrows. -/
theorem map_composition {M N P : WeilModule D l T₀} (a : M ⟶ N) (b : N ⟶ P) :
    map D m hm T₀ Y₀ f₀ l (a ≫ b) =
      map D m hm T₀ Y₀ f₀ l a ≫ map D m hm T₀ Y₀ f₀ l b := by
  apply IsoAlgebra.hom_ext
  simp [map]

/-- The canonical ambient Weil pullback functor, including its arrow action.
Source: latest blueprint, paragraphs 1--3
(blueprint: lem-zl-condensed-pullback-frobenius). -/
@[irreducible] def functor :
    WeilModule D l T₀ ⥤ WeilModule (constantExtensionDatum D m hm) l Y₀ where
  obj := object D m hm T₀ Y₀ f₀ l
  map := map D m hm T₀ Y₀ f₀ l
  map_id := map_identity D m hm T₀ Y₀ f₀ l
  map_comp := map_composition D m hm T₀ Y₀ f₀ l

end WeilConjectures.CondensedWeil.Pullback

namespace WeilConjectures.CondensedWeil.Pullback

variable (D : FiniteFieldDatum.{u}) (m : ℕ) (hm : 1 ≤ m)
  (T₀ : Over (Spec (.of D.k₀))) [hTft : LocallyOfFiniteType T₀.hom] [hTqc : QuasiCompact T₀.hom]
  [hTs : IsSeparated T₀.hom]
  (Y₀ : Over (Spec (.of (constantExtensionDatum D m hm).k₀)))
  [hYft : LocallyOfFiniteType Y₀.hom] [hYqc : QuasiCompact Y₀.hom]
  [hYs : IsSeparated Y₀.hom]
  (f₀ : Over.mk (Y₀.hom ≫
    Spec.map (CommRingCat.ofHom (D.extensionEmbedding m hm))) ⟶ T₀)
  (l : ℕ) [Fact l.Prime]

include hTs hYs

/-- The explicit Weil functor has exactly the module inverse-image carrier.
Source: latest blueprint, paragraphs 1--2
(blueprint: lem-zl-condensed-pullback-frobenius).
Proof: expand functor, object and IsoAlgebra.mk; its carrier is the specified module
pullback. This named equality keeps the kernel from unfolding the full Weil functor
inside the scalar-fibre comparison. -/
theorem carrier_eq (M : WeilModule D l T₀) :
    ((functor D m hm T₀ Y₀ f₀ l).obj M).carrier =
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
        (geometricMap D m hm T₀ Y₀ f₀)).obj M.carrier := by
  simp only [functor]
  rfl

/-- Pullback preserves the actual finite-constant-model constructible heart.
Source: latest blueprint, paragraphs 1--2
(blueprint: lem-zl-condensed-pullback-frobenius).
Proof: the carrier of the Weil pullback is the module inverse image along the geometric
map (carrier_eq). Both geometric schemes are quasi-compact and quasi-separated, being
base changes of separated finite-type models over finite fields. The constant-model
pullback statement lem-sfb-pullback-constant-model-constructible, for the condensed
coefficient ring of PadicAlgCl l, then says that the inverse image of a constructible
module is constructible. -/
theorem constructible (M : WeilModule D l T₀)
    (hM : IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
      (D.geometricFiber T₀).left M.carrier) :
    IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
      ((constantExtensionDatum D m hm).geometricFiber Y₀).left
      ((functor D m hm T₀ Y₀ f₀ l).obj M).carrier := by
  let := geometric_compact D T₀
  let := geometric_compact (constantExtensionDatum D m hm) Y₀
  let := geometric_quasiseparated D T₀
  let := geometric_quasiseparated (constantExtensionDatum D m hm) Y₀
  rw [carrier_eq]
  exact (coefficient_pullback l
    (geometricMap D m hm T₀ Y₀ f₀) M.carrier hM).1

/-- The full constructible Weil heart, using the coefficient-heart predicate verbatim.
Source: latest blueprint, paragraphs 1--2
(blueprint: lem-zl-condensed-pullback-frobenius). -/
abbrev heart (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] :=
  ObjectProperty.FullSubcategory (fun M : WeilModule D l X₀ ↦
    IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
      (D.geometricFiber X₀).left M.carrier)

/-- Restriction of the explicit Weil pullback to the constructible hearts.
Source: latest blueprint, paragraphs 1--2
(blueprint: lem-zl-condensed-pullback-frobenius). -/
def heartFunctor : heart D l T₀ ⥤ heart (constantExtensionDatum D m hm) l Y₀ :=
  ObjectProperty.lift _
    (ObjectProperty.ι _ ⋙ functor D m hm T₀ Y₀ f₀ l)
    (fun M ↦ constructible D m hm T₀ Y₀ f₀ l M.obj M.property)

set_option linter.unusedSectionVars false in
include hTft hTqc hYft hYqc in
/-- A closed source point maps to a closed target point.
Source: latest blueprint, paragraph 3
(blueprint: lem-zl-condensed-pullback-frobenius).
Proof: kappa(y) is finite over k_m and hence over k₀. Its subfield kappa(f₀(y))
is finite over k₀; the closed-point criterion lem-kun-closed-point-field on T₀
therefore makes the image point closed. -/
theorem image_closed (y : {y : Y₀.left // y ∈ closedPoints Y₀.left}) :
    f₀.left y.val ∈ closedPoints T₀.left := by
  let := (Y₀.hom.residueFieldAlgebraMap y.val).toAlgebra
  have : Module.Finite (constantExtensionDatum D m hm).k₀ (Y₀.left.residueField y.val) :=
    Y₀.hom.finite_residueField_of_isClosed y.val y.property
  have : Finite (Y₀.left.residueField y.val) :=
    Module.finite_of_finite (constantExtensionDatum D m hm).k₀
  let r : T₀.left.residueField (f₀.left y.val) →+* Y₀.left.residueField y.val :=
    (f₀.left.residueFieldMap y.val).hom
  have : Finite (T₀.left.residueField (f₀.left y.val)) :=
    Finite.of_injective r r.injective
  rw [← T₀.hom.finitePoints_eq_closedPoints]
  exact T₀.left.mem_finitePoints.mpr inferInstance

/-- The closed image point, with its unchanged underlying scheme point.
Source: latest blueprint, paragraph 3
(blueprint: lem-zl-condensed-pullback-frobenius). -/
abbrev closedImage (y : {y : Y₀.left // y ∈ closedPoints Y₀.left}) :
    {x : T₀.left // x ∈ closedPoints T₀.left} :=
  ⟨f₀.left y.val, image_closed D m hm T₀ Y₀ f₀ y⟩

/-- Compatible target lifts exist for every specified source residue embedding.
Source: latest blueprint, paragraph 3
(blueprint: lem-zl-condensed-pullback-frobenius).
Proof: restrict the source residue embedding along f₀'s injective residue homomorphism.
The equation over k₀ follows from f₀'s structure equation and k₀ → k_m → k.
The two lifts then have equal model and closure projections, so pullback uniqueness
proves their compatibility. Thus the local comparison has no additional restriction
on the source geometric point. -/
theorem compatible_lifts
    (y : {y : Y₀.left // y ∈ closedPoints Y₀.left})
    (iy : Y₀.left.residueField y.val →+* (constantExtensionDatum D m hm).k)
    (hiy : iy.comp (Y₀.hom.residueFieldAlgebraMap y.val) =
      algebraMap (constantExtensionDatum D m hm).k₀ (constantExtensionDatum D m hm).k) :
    ∃ (ix : T₀.left.residueField (closedImage D m hm T₀ Y₀ f₀ y).val →+* D.k)
      (hix : ix.comp (T₀.hom.residueFieldAlgebraMap
        (closedImage D m hm T₀ Y₀ f₀ y).val) = algebraMap D.k₀ D.k),
      localClosedPoint (constantExtensionDatum D m hm) Y₀ y iy hiy ≫
          geometricMap D m hm T₀ Y₀ f₀ =
        localClosedPoint D T₀ (closedImage D m hm T₀ Y₀ f₀ y) ix hix := by
  let ix : T₀.left.residueField (closedImage D m hm T₀ Y₀ f₀ y).val →+* D.k :=
    iy.comp (f₀.left.residueFieldMap y.val).hom
  have hcomp : (algebraMap (constantExtensionDatum D m hm).k₀
      (constantExtensionDatum D m hm).k).comp (D.extensionEmbedding m hm) =
      algebraMap D.k₀ D.k :=
    (FiniteField.exists_unique_subfield_of_closure D.p D.a D.q D.prime D.exponent_pos
      D.cardinality_eq D.k₀ D.card_base D.k m hm).choose_spec.2.2.2.2.2.2.choose_spec
  have hr : Scheme.Hom.residueFieldAlgebraMap
      (Y₀.hom ≫ Spec.map (CommRingCat.ofHom (D.extensionEmbedding m hm))) y.val =
      (Y₀.hom.residueFieldAlgebraMap y.val).comp (D.extensionEmbedding m hm) := by
    have h := Scheme.Hom.specMap_residueFieldAlgebraMap
      (Y₀.hom ≫ Spec.map (CommRingCat.ofHom (D.extensionEmbedding m hm))) y.val
    rw [← Category.assoc, ← Y₀.hom.specMap_residueFieldAlgebraMap,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp] at h
    exact congrArg CommRingCat.Hom.hom (Spec.map_inj.1 h)
  have hw : f₀.left ≫ T₀.hom =
      Y₀.hom ≫ Spec.map (CommRingCat.ofHom (D.extensionEmbedding m hm)) := Over.w f₀
  have hix : ix.comp (T₀.hom.residueFieldAlgebraMap
      (closedImage D m hm T₀ Y₀ f₀ y).val) = algebraMap D.k₀ D.k := by
    change (iy.comp (f₀.left.residueFieldMap y.val).hom).comp _ = _
    rw [RingHom.comp_assoc, ← Scheme.Hom.residueFieldAlgebraMap_comp,
      hw, hr, ← RingHom.comp_assoc, hiy]
    exact hcomp
  refine ⟨ix, hix, ?_⟩
  apply pullback.hom_ext
  · simp only [Category.assoc, geometricMap, pullback.lift_fst, localClosedPoint,
      pullback.lift_fst_assoc]
    dsimp only [ix]
    rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    exact congrArg (fun z ↦ Spec.map (CommRingCat.ofHom iy) ≫ z)
      (f₀.left.SpecMap_residueFieldMap_fromSpecResidueField y.val).symm
  · simp only [Category.assoc, geometricMap, pullback.lift_snd, localClosedPoint]
    change pullback.lift _ _ _ ≫ pullback.snd _ _ = _
    exact pullback.lift_snd _ _ _

/-- The source scalar fibre is evaluation of the literal coefficient pullback.
Source: latest blueprint, paragraphs 1--3
(blueprint: lem-zl-condensed-pullback-frobenius).
Proof: expand closedFiber, apply carrier_eq under point pullback and field evaluation,
and use that constantExtensionDatum has the very same closure field k. -/
theorem pulledFibre_eq (M : WeilModule D l T₀)
    (y : {y : Y₀.left // y ∈ closedPoints Y₀.left})
    (iy : Y₀.left.residueField y.val →+* (constantExtensionDatum D m hm).k)
    (hiy : iy.comp (Y₀.hom.residueFieldAlgebraMap y.val) =
      algebraMap (constantExtensionDatum D m hm).k₀ (constantExtensionDatum D m hm).k) :
    closedFiber (constantExtensionDatum D m hm) l Y₀
        ((functor D m hm T₀ Y₀ f₀ l).obj M) y iy hiy =
      (CondensedQbarGeometricEvaluation.fieldFiber D.k l).obj
        ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
          (localClosedPoint (constantExtensionDatum D m hm) Y₀ y iy hiy)).obj
          ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
            (geometricMap D m hm T₀ Y₀ f₀)).obj M.carrier)) := by
  unfold closedFiber
  rw [carrier_eq]
  rfl

/-- The target fibre is its literal field-evaluated point pullback.
Source: latest blueprint, paragraph 3
(blueprint: lem-zl-condensed-pullback-frobenius).
Proof: expand closedFiber; this is its defining formula. -/
theorem targetFibre_eq (M : WeilModule D l T₀)
    (y : {y : Y₀.left // y ∈ closedPoints Y₀.left})
    (ix : T₀.left.residueField (closedImage D m hm T₀ Y₀ f₀ y).val →+* D.k)
    (hix : ix.comp (T₀.hom.residueFieldAlgebraMap
      (closedImage D m hm T₀ Y₀ f₀ y).val) = algebraMap D.k₀ D.k) :
    (CondensedQbarGeometricEvaluation.fieldFiber D.k l).obj
      ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
        (localClosedPoint D T₀ (closedImage D m hm T₀ Y₀ f₀ y) ix hix)).obj M.carrier) =
      closedFiber D l T₀ M (closedImage D m hm T₀ Y₀ f₀ y) ix hix := by
  rfl


omit hTs in
/-- The source geometric point, with its domain explicitly the original closure field.
Source: latest blueprint, compatible geometric points in paragraphs 2--3
(blueprint: lem-zl-condensed-pullback-frobenius).
This is the literal localClosedPoint: constantExtensionDatum has the same closure field.
Writing its domain explicitly keeps specialization of field evaluation from unfolding
coefficient pullback functors merely to compare the two presentations of Spec k. -/
def sourcePointNative
    (y : {y : Y₀.left // y ∈ closedPoints Y₀.left})
    (iy : Y₀.left.residueField y.val →+* (constantExtensionDatum D m hm).k)
    (hiy : iy.comp (Y₀.hom.residueFieldAlgebraMap y.val) =
      algebraMap (constantExtensionDatum D m hm).k₀ (constantExtensionDatum D m hm).k) :
    Spec (.of D.k) ⟶ ((constantExtensionDatum D m hm).geometricFiber Y₀).left :=
  localClosedPoint (constantExtensionDatum D m hm) Y₀ y iy hiy

/-- The literal source scalar fibre using the explicitly typed source point.
Source: latest blueprint, canonical geometric-fibre comparison in paragraphs 2--3
(blueprint: lem-zl-condensed-pullback-frobenius).
Proof: first apply pulledFibre_eq. The two presentations of Spec k are equal by
reflexivity, and sourcePointNative is the same point by heterogeneous reflexivity.
Congruence of coefficient pullback in its scheme and arrow identifies the two
pullback functors. Apply their equality to the pulled-back carrier and then to
field evaluation. This only normalizes the existing literal fibre identity. -/
theorem normalizedPulledFibre_eq (M : WeilModule D l T₀)
    (y : {y : Y₀.left // y ∈ closedPoints Y₀.left})
    (iy : Y₀.left.residueField y.val →+* (constantExtensionDatum D m hm).k)
    (hiy : iy.comp (Y₀.hom.residueFieldAlgebraMap y.val) =
      algebraMap (constantExtensionDatum D m hm).k₀ (constantExtensionDatum D m hm).k) :
    closedFiber (constantExtensionDatum D m hm) l Y₀
        ((functor D m hm T₀ Y₀ f₀ l).obj M) y iy hiy =
      (CondensedQbarGeometricEvaluation.fieldFiber D.k l).obj
        ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
          (sourcePointNative D m hm Y₀ y iy hiy)).obj
          ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
            (geometricMap D m hm T₀ Y₀ f₀)).obj M.carrier)) := by
  apply (pulledFibre_eq D m hm T₀ Y₀ f₀ l M y iy hiy).trans
  have hP : CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
        (localClosedPoint (constantExtensionDatum D m hm) Y₀ y iy hiy) =
      CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
        (sourcePointNative D m hm Y₀ y iy hiy) :=
    eq_of_heq (pullback_heq (Profinite.padicAlgClRingObj l) rfl
      (localClosedPoint (constantExtensionDatum D m hm) Y₀ y iy hiy)
      (sourcePointNative D m hm Y₀ y iy hiy) (HEq.rfl))
  exact congrArg (fun F ↦ (CondensedQbarGeometricEvaluation.fieldFiber D.k l).obj
    (F.obj ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
      (geometricMap D m hm T₀ Y₀ f₀)).obj M.carrier))) hP

/-- The canonical scalar-fibre comparison used by Frobenius and naturality: the explicit
coefficient pullback compositor, evaluated at the geometric field and transported along
the two literal fibre equalities.
Source: latest blueprint, paragraphs 2--3
(blueprint: lem-zl-condensed-pullback-frobenius). -/
def fibreComparison
    (M : WeilModule D l T₀)
    (y : {y : Y₀.left // y ∈ closedPoints Y₀.left})
    (iy : Y₀.left.residueField y.val →+* (constantExtensionDatum D m hm).k)
    (hiy : iy.comp (Y₀.hom.residueFieldAlgebraMap y.val) =
      algebraMap (constantExtensionDatum D m hm).k₀ (constantExtensionDatum D m hm).k)
    (ix : T₀.left.residueField (closedImage D m hm T₀ Y₀ f₀ y).val →+* D.k)
    (hix : ix.comp (T₀.hom.residueFieldAlgebraMap
      (closedImage D m hm T₀ Y₀ f₀ y).val) = algebraMap D.k₀ D.k)
    (hc : localClosedPoint (constantExtensionDatum D m hm) Y₀ y iy hiy ≫
        geometricMap D m hm T₀ Y₀ f₀ =
      localClosedPoint D T₀ (closedImage D m hm T₀ Y₀ f₀ y) ix hix) :
    closedFiber (constantExtensionDatum D m hm) l Y₀
      ((functor D m hm T₀ Y₀ f₀ l).obj M) y iy hiy ≅
      closedFiber D l T₀ M (closedImage D m hm T₀ Y₀ f₀ y) ix hix :=
  transportComparison (normalizedPulledFibre_eq D m hm T₀ Y₀ f₀ l M y iy hiy)
    (transportTarget (targetFibre_eq D m hm T₀ Y₀ f₀ l M y ix hix)
      (evaluatedComparison D.k l (geometricMap D m hm T₀ Y₀ f₀)
        (sourcePointNative D m hm Y₀ y iy hiy)
        (localClosedPoint D T₀ (closedImage D m hm T₀ Y₀ f₀ y) ix hix) hc M.carrier))


omit hTs hYs in
/-- Constructible closed fibres are finite-dimensional over the coefficient field.
Source: latest blueprint, paragraph 3
(blueprint: lem-zl-condensed-pullback-frobenius).
Proof: the geometric fibre is locally Noetherian, being of finite type over the
closure field. The field fibre at any geometric point of a constructible module over
such a scheme is finite-dimensional by the constructible-fibre finiteness proved for
lem-dl-a1-condensed-fibres-exact; apply it at the closed geometric point. -/
theorem closedFiber_finiteDimensional (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [IsSeparated X₀.hom] (M : WeilModule D l X₀)
    (hM : IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
      (D.geometricFiber X₀).left M.carrier)
    (x : {x : X₀.left // x ∈ closedPoints X₀.left})
    (i : X₀.left.residueField x.val →+* D.k)
    (hi : i.comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k) :
    FiniteDimensional (PadicAlgCl l) (closedFiber D l X₀ M x i hi)  := by
  have : IsLocallyNoetherian (D.geometricFiber X₀).left := by
    dsimp [FiniteFieldDatum.geometricFiber]
    infer_instance
  exact DeligneLaumonFibres.constructible_fibre_finite l M.carrier hM
    (localClosedPoint D X₀ x i hi)


/-- The canonical local factor, with its reverse characteristic-polynomial
normalization. Its roots retain all algebraic multiplicities. Source: latest
blueprint, paragraph 3
(blueprint: lem-zl-condensed-pullback-frobenius). -/
def localPolynomial (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [IsSeparated X₀.hom] (M : WeilModule D l X₀)
    (hM : IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
      (D.geometricFiber X₀).left M.carrier)
    (x : {x : X₀.left // x ∈ closedPoints X₀.left})
    (i : X₀.left.residueField x.val →+* D.k)
    (hi : i.comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k) :
    Polynomial (PadicAlgCl l) :=
  letI : FiniteDimensional (PadicAlgCl l) (closedFiber D l X₀ M x i hi) :=
    closedFiber_finiteDimensional (D := D) (l := l) (X₀ := X₀)
      (M := M) (hM := hM) (x := x) (i := i) (hi := hi)
  localFactor D l X₀ M x i hi

private theorem ambient_exact :
    PreservesFiniteLimits (functor D m hm T₀ Y₀ f₀ l) ∧
      PreservesFiniteColimits (functor D m hm T₀ Y₀ f₀ l) := by
  refine fixedMap_exact
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius T₀).hom)
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
      ((constantExtensionDatum D m hm).geometricFrobenius Y₀).hom)
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
      (geometricMap D m hm T₀ Y₀ f₀)) (functor D m hm T₀ Y₀ f₀ l) ?_
  unfold functor
  exact Iso.refl _

private theorem heart_exact :
    PreservesFiniteLimits (heartFunctor D m hm T₀ Y₀ f₀ l) ∧
      PreservesFiniteColimits (heartFunctor D m hm T₀ Y₀ f₀ l) := by
  have : IsLocallyNoetherian (D.geometricFiber T₀).left := by
    dsimp [FiniteFieldDatum.geometricFiber]
    infer_instance
  have he := DeligneLaumonFibres.constructible_inclusion_exact l
    (D.geometricFiber T₀).left
    (IsoAlgebra.forget (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius T₀).hom))
  have : PreservesFiniteLimits (ObjectProperty.ι (fun M : WeilModule D l T₀ ↦
      IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
        (D.geometricFiber T₀).left M.carrier)) := he.1
  have : PreservesFiniteColimits (ObjectProperty.ι (fun M : WeilModule D l T₀ ↦
      IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
        (D.geometricFiber T₀).left M.carrier)) := he.2
  have ha := ambient_exact D m hm T₀ Y₀ f₀ l
  have := ha.1
  have := ha.2
  unfold heartFunctor
  exact restrictedMap_exact _ _ _ _

private theorem lisse_preserved (M : WeilModule D l T₀)
    (hM : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) M.carrier) :
    IsLisseCoefficientModule (Profinite.padicAlgClRingObj l)
      ((functor D m hm T₀ Y₀ f₀ l).obj M).carrier := by
  rw [carrier_eq]
  exact CondensedRing.locFree_pullback _ _ _ hM

/-- Every actual finite filtration pulls back, with its quotient isomorphisms and lisse
terms and quotients. The endpoint isomorphism is in the Weil category.
Source: latest blueprint, paragraphs 2 and 7
(blueprint: lem-zl-condensed-pullback-frobenius). -/
def FiltrationAssertions : Prop :=
  ∀ (M : WeilModule D l T₀) (t : ℕ) (G : Fin (t + 1) → WeilModule D l T₀)
    (a : ∀ i : Fin t, G i.castSucc ⟶ G i.succ),
    (∀ i, IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
      (D.geometricFiber T₀).left (G i).carrier) →
    IsZero (G 0) → Nonempty (G (Fin.last t) ≅ M) → (∀ i, Mono (a i)) →
    IsZero ((functor D m hm T₀ Y₀ f₀ l).obj (G 0)) ∧
    Nonempty ((functor D m hm T₀ Y₀ f₀ l).obj (G (Fin.last t)) ≅
      (functor D m hm T₀ Y₀ f₀ l).obj M) ∧
    (∀ i, Mono ((functor D m hm T₀ Y₀ f₀ l).map (a i))) ∧
    (∀ i, Nonempty (cokernel ((functor D m hm T₀ Y₀ f₀ l).map (a i)) ≅
      (functor D m hm T₀ Y₀ f₀ l).obj (cokernel (a i)))) ∧
    (∀ i, IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) (G i).carrier →
      IsLisseCoefficientModule (Profinite.padicAlgClRingObj l)
        ((functor D m hm T₀ Y₀ f₀ l).obj (G i)).carrier) ∧
    (∀ i, IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) (cokernel (a i)).carrier →
      IsLisseCoefficientModule (Profinite.padicAlgClRingObj l)
        (cokernel ((functor D m hm T₀ Y₀ f₀ l).map (a i))).carrier)

/-- Exactness and local finite freeness, with the original finite rank on every
trivializing cover, and pullback of actual Weil filtrations.
Source: latest blueprint, paragraphs 1--2 and 7
(blueprint: lem-zl-condensed-pullback-frobenius).
Proof: the forgetful functors from Weil pairs to modules preserve and reflect finite
limits and colimits, and the forgetful image of the Weil pullback is the exact module
inverse image along f; hence the Weil pullback is exact. The inclusion of the
constructible heart is exact (lem-dl-a1-condensed-fibres-exact) and the pullback
preserves constructibility, so heartFunctor is exact. Local freeness pulls back by
lem-weil-pbc-finite-etale-locally-free-models. For a finite-free cover of rank r,
the square comparison around each base-change square and the regular-object
comparison identify the pulled-back trivialization with B^r, including r=0.
Exactness preserves zero endpoints, monomorphisms and cokernel quotients of each finite
filtration, and lissity is invariant under isomorphism, giving the lisse terms and
successive quotients. -/
theorem condensed_pullback_frobenius (hl : l ≠ D.p) :
    PreservesFiniteLimits (heartFunctor D m hm T₀ Y₀ f₀ l) ∧
    PreservesFiniteColimits (heartFunctor D m hm T₀ Y₀ f₀ l) ∧
    (∀ M : WeilModule D l T₀,
      IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) M.carrier →
      IsLisseCoefficientModule (Profinite.padicAlgClRingObj l)
        ((functor D m hm T₀ Y₀ f₀ l).obj M).carrier) ∧
    (∀ (M : WeilModule D l T₀) (r : ℕ)
      (U : Scheme.Cover.{u} Scheme.proetalePrecoverage (D.geometricFiber T₀).left),
      (∀ i, Nonempty ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) (U.f i)).obj
        M.carrier ≅ Mod.finiteFree (condensedRingObj (Profinite.padicAlgClRingObj l) (U.X i)) r)) →
      ∀ i, Nonempty ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
          (pullback.fst (geometricMap D m hm T₀ Y₀ f₀) (U.f i))).obj
            ((functor D m hm T₀ Y₀ f₀ l).obj M).carrier ≅
        Mod.finiteFree (condensedRingObj (Profinite.padicAlgClRingObj l)
          (pullback (geometricMap D m hm T₀ Y₀ f₀) (U.f i))) r)) ∧
    FiltrationAssertions D m hm T₀ Y₀ f₀ l  := by
  classical
  have _ := hl
  have ha := ambient_exact D m hm T₀ Y₀ f₀ l
  have := ha.1
  have := ha.2
  let F := functor D m hm T₀ Y₀ f₀ l
  have : PreservesFiniteLimits F := ha.1
  have : PreservesFiniteColimits F := ha.2
  have : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts F
  have : F.Additive := Functor.additive_of_preservesBinaryBiproducts F
  refine ⟨(heart_exact D m hm T₀ Y₀ f₀ l).1,
    (heart_exact D m hm T₀ Y₀ f₀ l).2,
    lisse_preserved D m hm T₀ Y₀ f₀ l, ?_, ?_⟩
  · intro M r U hU i
    rw [carrier_eq]
    exact fixedRank_pullback _ _ M.carrier r U hU i
  · intro M t G a hG hz he hmono
    exact exact_filtration F
      (fun K ↦ IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) K.carrier)
      (fun K ↦ IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) K.carrier)
      (lisse_preserved D m hm T₀ Y₀ f₀ l)
      (fun {K N} e hN ↦ CondensedRing.locFree_iso
        ((IsoAlgebra.forget (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
          ((constantExtensionDatum D m hm).geometricFrobenius Y₀).hom)).mapIso e) hN)
      M t G a hz he hmono

/-- The canonical fibre comparison intertwines F_y with F_x^e and is natural in M.
It also gives the residue cardinality and the full multiset of eigenvalues.
Source: latest blueprint, paragraph 3
(blueprint: lem-zl-condensed-pullback-frobenius).
Proof: write r=[kappa(y):k_m], d=[kappa(x):k₀] and e=[kappa(y):kappa(x)].
The finite-field tower formula gives mr=de and e≥1. An e-element kappa(x)-basis
counts kappa(y) as (#kappa(x))^e. The fibre comparison is module pullback composition,
so is linear and natural in M. The r-fold source Weil return is the ordered mr-fold
target return. Group its de transitions into e blocks of length d, including each
point reparametrization, using lem-weil-pbc-profinite-point-pullback and geometric
field evaluation. Lem-wf-condensed-local-frobenius-powers identifies it with F_x^e.
The power-spectrum theorem gives the roots alpha^e with algebraic multiplicities,
adding multiplicities at collisions. This argument uses no semisimplicity. -/
theorem local_frobenius (hl : l ≠ D.p)
    (y : {y : Y₀.left // y ∈ closedPoints Y₀.left})
    (iy : Y₀.left.residueField y.val →+* (constantExtensionDatum D m hm).k)
    (hiy : iy.comp (Y₀.hom.residueFieldAlgebraMap y.val) =
      algebraMap (constantExtensionDatum D m hm).k₀ (constantExtensionDatum D m hm).k)
    (ix : T₀.left.residueField (closedImage D m hm T₀ Y₀ f₀ y).val →+* D.k)
    (hix : ix.comp (T₀.hom.residueFieldAlgebraMap
        (closedImage D m hm T₀ Y₀ f₀ y).val) = algebraMap D.k₀ D.k)
    (hc : localClosedPoint (constantExtensionDatum D m hm) Y₀ y iy hiy ≫
        geometricMap D m hm T₀ Y₀ f₀ =
      localClosedPoint D T₀ (closedImage D m hm T₀ Y₀ f₀ y) ix hix)
    (M : WeilModule D l T₀)
    (hM : IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
      (D.geometricFiber T₀).left M.carrier) :
    1 ≤ f₀.left.residueDegree y.val ∧
    Nat.card (Y₀.left.residueField y.val) =
      Nat.card (T₀.left.residueField (f₀.left y.val)) ^ f₀.left.residueDegree y.val ∧
    (closedOperator (constantExtensionDatum D m hm) l Y₀
        ((functor D m hm T₀ Y₀ f₀ l).obj M) y iy hiy ≫
      (fibreComparison D m hm T₀ Y₀ f₀ l M y iy hiy ix hix hc).hom =
      (fibreComparison D m hm T₀ Y₀ f₀ l M y iy hiy ix hix hc).hom ≫
        closedOperator D l T₀ M (closedImage D m hm T₀ Y₀ f₀ y) ix hix ^
          f₀.left.residueDegree y.val) ∧
    (∀ (N : WeilModule D l T₀) (a : M ⟶ N),
      (CondensedQbarGeometricEvaluation.fieldFiber D.k l).map
          ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
            (localClosedPoint (constantExtensionDatum D m hm) Y₀ y iy hiy)).map
            (((functor D m hm T₀ Y₀ f₀ l).map a).hom.f)) ≫
        (fibreComparison D m hm T₀ Y₀ f₀ l N y iy hiy ix hix hc).hom =
      (fibreComparison D m hm T₀ Y₀ f₀ l M y iy hiy ix hix hc).hom ≫
        (CondensedQbarGeometricEvaluation.fieldFiber D.k l).map
          ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
            (localClosedPoint D T₀ (closedImage D m hm T₀ Y₀ f₀ y) ix hix)).map a.hom.f)) ∧
    (localPolynomial (constantExtensionDatum D m hm) l Y₀
        ((functor D m hm T₀ Y₀ f₀ l).obj M)
        (constructible D m hm T₀ Y₀ f₀ l M hM) y iy hiy).roots =
      (localPolynomial D l T₀ M hM (closedImage D m hm T₀ Y₀ f₀ y) ix hix).roots.map
        (fun α ↦ α ^ f₀.left.residueDegree y.val) := by
  sorry

/-- Pullback preserves reality, each specified punctual weight, and every mixed upper
bound. This covers restrictions, constant extensions, and their composites.
Source: latest blueprint, paragraphs 1--4 and 7
(blueprint: lem-zl-condensed-pullback-frobenius).
Proof: every closed source point has closed image. The local comparison gives alpha^e
and q_y=q_x^e. Conjugation stability is preserved by powering, so local determinants
remain real. For purity, |iota(alpha^e)|=|iota(alpha)|^e=(q_x^e)^(w/2), by positive-real
power laws, also for negative real w. Pull back the actual finite Weil filtration by
exactness, identify its quotients, and retain their weights and the inequalities v≤w.
For zero quotients the condition is empty; the zero sheaf admits a length-zero filtration.
Locally closed restrictions have m=1, and a constant extension is its usual projection.
For composites the pullback compositors concatenate the ordered Weil blocks and residue
degrees multiply, so the same formulas apply. -/
theorem preserves_weights (hl : l ≠ D.p) (iota : PadicAlgCl l ≃+* ℂ)
    (M : WeilModule D l T₀)
    (hM : IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
      (D.geometricFiber T₀).left M.carrier) :
    (Real D l T₀ M iota.toRingHom →
      Real (constantExtensionDatum D m hm) l Y₀
        ((functor D m hm T₀ Y₀ f₀ l).obj M) iota.toRingHom) ∧
    (∀ w : ℝ, Pure D l T₀ M iota.toRingHom w →
      Pure (constantExtensionDatum D m hm) l Y₀
        ((functor D m hm T₀ Y₀ f₀ l).obj M) iota.toRingHom w) ∧
    (∀ w : ℝ, Mixed D l T₀ M iota.toRingHom w →
      Mixed (constantExtensionDatum D m hm) l Y₀
        ((functor D m hm T₀ Y₀ f₀ l).obj M) iota.toRingHom w) := by
  sorry

end WeilConjectures.CondensedWeil.Pullback
