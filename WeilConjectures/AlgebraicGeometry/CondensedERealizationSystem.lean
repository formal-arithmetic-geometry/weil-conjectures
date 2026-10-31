/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedERealizationDefinitions
import WeilConjectures.AlgebraicGeometry.CondensedFieldLfpLocalTriviality
import WeilConjectures.AlgebraicGeometry.CondensedFieldContinuousRealization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import WeilConjectures.CategoryTheory.Monoidal.Conjugate
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
import Mathlib.Topology.Category.Profinite.EffectiveEpi
import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
import Mathlib.Condensed.TopComparison
import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.Topology.NoetherianSpace
import WeilConjectures.AlgebraicGeometry.ProEtalePointComponentsMaps
import WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Topology.Category.Profinite.AsLimit
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.Topology.Category.Profinite.CofilteredLimit
import Mathlib.Topology.Connected.TotallyDisconnected
import WeilConjectures.Topology.SpectralSpace.ConnectedComponent
import WeilConjectures.AlgebraicGeometry.ProEtaleSheafificationWcontractibleSections
import WeilConjectures.AlgebraicGeometry.PointLanAffineEvaluation
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import Mathlib.CategoryTheory.Whiskering
import Mathlib.Algebra.Category.Ring.Basic
import WeilConjectures.AlgebraicGeometry.PointLanFiniteProducts
import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation
import Mathlib.AlgebraicGeometry.Limits
import WeilConjectures.AlgebraicGeometry.FiniteCoproductLfpQcqs
import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductSections
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.CategoryTheory.Sites.MonObj
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import WeilConjectures.AlgebraicGeometry.LocallyClosedStratification
import WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.CategoryTheory.SiteInverseImageTensor
import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Ring
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationCorank
import WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationMatrix
import Mathlib.LinearAlgebra.Matrix.Rank
import WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationEvaluation
import Mathlib.Algebra.Category.ModuleCat.Basic
import WeilConjectures.AlgebraicGeometry.CondensedFieldRegularModuleScalars
import WeilConjectures.AlgebraicGeometry.CondensedFieldEvaluationFunctors
import WeilConjectures.AlgebraicGeometry.GeometricFieldProEtaleEvaluation
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Reflective
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.AlgebraicGeometry.GeometricFieldProfiniteDenseSubsite
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import WeilConjectures.CategoryTheory.DenseSubsiteModuleRestriction
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
import WeilConjectures.CategoryTheory.RingObjects.Ab
import Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.AlgebraicGeometry.CondensedFieldGeometricRegularCoefficient
import WeilConjectures.AlgebraicGeometry.ContinuousChartSchemeNaturality
import WeilConjectures.AlgebraicGeometry.IntegralMatrixAnalyticData
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientRealizations
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientData
import Mathlib.NumberTheory.Padics.PadicNumbers
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Topology.Algebra.Ring.Ideal
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.NumberTheory.Padics.ProperSpace
import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.CategoryTheory.Abelian.ShortExact
import WeilConjectures.AlgebraicGeometry.IntegralScalarContractive
import Mathlib.Data.Matrix.Basic
import WeilConjectures.AlgebraicGeometry.IntegralRegularCoefficientPullback
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import WeilConjectures.AlgebraicGeometry.CondensedFieldRankDescent
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import WeilConjectures.AlgebraicGeometry.ContinuousFieldCokernelLocalFree
import WeilConjectures.AlgebraicGeometry.ContinuousFieldPresentationNormalForm
import WeilConjectures.AlgebraicGeometry.ContinuousFieldMatrixSheafNormalForm
import WeilConjectures.AlgebraicGeometry.ContinuousFieldMatrixElimination
import Mathlib.Logic.Equiv.Set
import Mathlib.Data.Fintype.Basic
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import WeilConjectures.Mathlib.LinearAlgebra.Matrix.Rank
import WeilConjectures.Mathlib.LinearAlgebra.Matrix.SchurComplement
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.LocallyFree
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.CondensedERealizationLeftSystemExistence
import WeilConjectures.CategoryTheory.MateIsoAlongEquivalences
import WeilConjectures.AlgebraicGeometry.RealizationScalarEquivalence

/-! # Normalized continuous field realization system

Source: Bhatt--Scholze, Proposition 6.8.14(2) and Remark 6.8.15.
(blueprint: lem-weil-pbc-condensed-e-system)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
namespace WeilConjectures

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj TensorProduct

set_option synthInstance.maxSize 4096

private theorem realization_lisse_criterion
    (l : ℕ) [Fact l.Prime] (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (T : Scheme.{u}) [TopologicalSpace.NoetherianSpace T]
    (K : CondensedERealization.Ambient E T) :
    boundedConstructible (CondensedERealization.Coefficient E T) K ↔
      (∃ a b : ℤ, ∀ q : ℤ, q < a ∨ b < q →
        IsZero ((DerivedCategory.homologyFunctor _ q).obj K)) ∧
      ∀ q : ℤ, ∃ S : Scheme.Stratification T, ∀ a : Fin S.n,
        ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage (S.domain a),
        ∀ i : C.I₀,
          Mod.IsFree
            ((upperStar Ab.{u + 1} (C.f i)).obj
              ((upperStar Ab.{u + 1} (S.immersion a)).obj
                (CondensedERealization.Coefficient E T)))
            (((upperStar Ab.{u + 1} (C.f i)).mapMod _).obj
              (((upperStar Ab.{u + 1} (S.immersion a)).mapMod _).obj
                ((DerivedCategory.homologyFunctor _ q).obj K))) := by
  rw [mem_boundedConstructible_iff]
  apply and_congr_right
  intro _
  constructor
  · intro h q
    obtain ⟨S, hS⟩ := h q
    refine ⟨S, fun a ↦ ?_⟩
    exact exists_finiteFree_cover_on_condensedField_strata l E T S
      ((DerivedCategory.homologyFunctor _ q).obj K) hS a
      ((S.immersion a).isEmbedding.isInducing.noetherianSpace)
  · intro h q
    obtain ⟨S, hS⟩ := h q
    refine ⟨S, fun a ↦ ?_⟩
    obtain ⟨C, hC⟩ := hS a
    exact ⟨C, fun i ↦ (hC i).isFinitelyPresented⟩

private theorem realization_prime_unit
    (l : ℕ) [Fact l.Prime] (k : Type u) [Field k] [Fact (ringChar k ≠ l)]
    (T : CondensedERealization.Base k) (x : T.scheme) :
    IsUnit (l : T.scheme.presheaf.stalk x) := by
  have hl : (l : k) ≠ 0 := by
    intro h
    rcases (Nat.dvd_prime (Fact.out : l.Prime)).1 (ringChar.dvd h) with h1 | h1
    · exact CharP.ringChar_ne_one h1
    · exact (Fact.out : ringChar k ≠ l) h1
  let f := T.scheme ↘ Spec (.of k)
  have h : IsUnit (l : (Spec (.of k)).presheaf.stalk (f x)) := by
    simpa using (isUnit_iff_ne_zero.2 hl).map
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (Spec (.of k)).presheaf.germ ⊤ (f x) trivial).hom
  simpa using h.map (f.stalkMap x).hom

private def realizationAtOfScalar
    (l : ℕ) [Fact l.Prime] (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (T : Scheme.{u}) [IsNoetherian T]
    [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
    (s : RealizationScalarFunctorData l E T) [s.J.IsEquivalence] :
    CondensedERealization.At l E T := by
  letI := s.encodingAdditive
  letI := s.encodingInverseAdditive
  let e := s.J.asEquivalence
  refine
    { coefficientIso := s.coefficientIso
      coefficient_normalization := s.coefficient_normalization
      sectionIso := s.sectionIso
      section_normalization := s.section_normalization
      integralIso := s.integralIso
      finiteIso := s.finiteIso
      finite_normalization := s.finite_normalization
      integral_normalization := s.integral_normalization
      inclusion := s.inclusion
      inclusion_normalization := s.inclusion_normalization
      encodingAdditive := s.encodingAdditive
      encodingInverseAdditive := s.encodingInverseAdditive
      realization := e
      scalarExtension := s.integral
      linearity := ?_
      integral_model := ?_
      lisse_criterion := realization_lisse_criterion l E T }
  · intro K L f a
    have h := s.linearity K L f (pbcRationalCoefficientEquiv l E a)
    have hs : (pbcRationalCoefficientEquiv l E a) • f = a • f := by
      change (pbcRationalCoefficientEquiv l E).symm
        (pbcRationalCoefficientEquiv l E a) • f = a • f
      rw [RingEquiv.symm_apply_apply]
    rw [hs] at h
    exact h
  · intro K
    exact ⟨(e.inverse.obj K).obj, ⟨e.counitIso.app K⟩⟩

section TensorAdjunction
universe r a b c d
variable (R : Type r) [CommRing R] (p : R)
  {C : Type a} [Category.{b} C] [Preadditive C] [Linear R C]
  {D : Type c} [Category.{d} D] [Preadditive D] [Linear R D]

private def tensorAdjunction (F : C ⥤ D) [F.Additive] [F.Linear R]
    (G : D ⥤ C) [G.Additive] [G.Linear R] (adj : F ⊣ G) :
    ScalarLocalization.transport R p F ⊣ ScalarLocalization.transport R p G where
  unit :=
    { app X := 1 ⊗ₜ[R] adj.unit.app X.obj
      naturality {X Y} f := by
        dsimp only [ScalarLocalization.transport, ScalarLocalization.transportHom,
          Functor.id_obj, Functor.comp_obj]
        change ScalarLocalization.composition R C p _ _ _
          (1 ⊗ₜ[R] adj.unit.app Y.obj) f =
          ScalarLocalization.composition R C p _ _ _
            ((G.mapLinearMap R).baseChange (Localization.Away p)
              ((F.mapLinearMap R).baseChange (Localization.Away p) f))
            (1 ⊗ₜ[R] adj.unit.app X.obj)
        induction f using TensorProduct.induction_on with
        | zero => simp only [map_zero, LinearMap.zero_apply]
        | tmul a f =>
          simp only [LinearMap.baseChange_tmul, Functor.coe_mapLinearMap,
            ScalarLocalization.composition_tmul, one_mul, mul_one]
          exact congrArg (fun k ↦ a ⊗ₜ[R] k) (adj.unit.naturality f)
        | add f g hf hg => simp only [_root_.map_add, LinearMap.add_apply, hf, hg] }
  counit :=
    { app X := 1 ⊗ₜ[R] adj.counit.app X.obj
      naturality {X Y} f := by
        dsimp only [ScalarLocalization.transport, ScalarLocalization.transportHom,
          Functor.id_obj, Functor.comp_obj]
        change ScalarLocalization.composition R D p _ _ _
          (1 ⊗ₜ[R] adj.counit.app Y.obj)
            ((F.mapLinearMap R).baseChange (Localization.Away p)
              ((G.mapLinearMap R).baseChange (Localization.Away p) f)) =
          ScalarLocalization.composition R D p _ _ _ f (1 ⊗ₜ[R] adj.counit.app X.obj)
        induction f using TensorProduct.induction_on with
        | zero => simp only [map_zero, LinearMap.zero_apply]
        | tmul a f =>
          simp only [LinearMap.baseChange_tmul, Functor.coe_mapLinearMap,
            ScalarLocalization.composition_tmul, one_mul, mul_one]
          exact congrArg (fun k ↦ a ⊗ₜ[R] k) (adj.counit.naturality f)
        | add f g hf hg => simp only [_root_.map_add, LinearMap.add_apply, hf, hg] }
  left_triangle_components X := by
    change ScalarLocalization.composition R D p _ _ _ (1 ⊗ₜ[R] adj.counit.app (F.obj X.obj))
      ((ScalarLocalization.transport R p F).map (1 ⊗ₜ[R] adj.unit.app X.obj)) = _
    simp only [ScalarLocalization.transport, ScalarLocalization.transportHom,
      LinearMap.baseChange_tmul]
    rw [ScalarLocalization.composition_tmul, one_mul]
    exact congrArg (fun k ↦ (1 : Localization.Away p) ⊗ₜ[R] k)
      (adj.left_triangle_components X.obj)
  right_triangle_components X := by
    change ScalarLocalization.composition R C p _ _ _
      ((ScalarLocalization.transport R p G).map (1 ⊗ₜ[R] adj.counit.app X.obj))
      (1 ⊗ₜ[R] adj.unit.app (G.obj X.obj)) = _
    simp only [ScalarLocalization.transport, ScalarLocalization.transportHom,
      LinearMap.baseChange_tmul]
    rw [ScalarLocalization.composition_tmul, one_mul]
    exact congrArg (fun k ↦ (1 : Localization.Away p) ⊗ₜ[R] k)
      (adj.right_triangle_components X.obj)
end TensorAdjunction

private theorem realization_ulift_tmul_heq (A : Type u) [CommRing A]
    (p : ULift.{u + 1} A) {M : Type (u + 2)} [AddCommMonoid M]
    [Module (ULift.{u + 1} A) M] (f : M) :
    HEq (@TensorProduct.tmul (ULift.{u + 1} A) _ (Localization.Away p) M _ _
      OreLocalization.instModuleOfIsScalarTower _ 1 f)
      (@TensorProduct.tmul (ULift.{u + 1} A) _ (Localization.Away p) M _ _
        ULift.module _ 1 f) := by
  have hm : (ULift.module : Module (ULift.{u + 1} A) (Localization.Away p)) =
      OreLocalization.instModuleOfIsScalarTower := by
    apply Module.ext'
    intro a x
    induction x using OreLocalization.ind with
    | _ b s => simp only [ULift.smul_def, OreLocalization.smul_oreDiv]
  rw [hm]

private def realizationAlongOfLeft
    (l : ℕ) [Fact l.Prime] (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
    (T U : CondensedERealization.Base k) (h : T.scheme ⟶ U.scheme)
    [h.IsOver (Spec (.of k))]
    (rT : CondensedERealization.At l E T.scheme)
    (rU : CondensedERealization.At l E U.scheme)
    (a : CondensedERealization.LeftAlong l E k T U h rT rU) :
    CondensedERealization.Along l E k T U h rT rU := by
  let adj := tensorAdjunction (PbcIntegralRing l E) (pbcUniformizer l E)
    a.pull a.push a.integralAdjunction
  let adj' := CondensedERealization.fieldAdjunction l E k T U h
  let beta := (mateEquiv adj adj' a.pullComparison.inv).natTrans
  have : IsIso beta := isIso_mateEquiv_of_isEquivalence_of_fullyFaithful adj adj'
    rU.realization.functor rT.realization.functor a.pullComparison.symm
  refine
    { pull := a.pull
      pullAdditive := a.pullAdditive
      pullLinear := a.pullLinear
      push := a.push
      pushAdditive := a.pushAdditive
      pushLinear := a.pushLinear
      pullAmbient := a.pullAmbient
      pushAmbient := a.pushAmbient
      integralAdjunction := a.integralAdjunction
      integral_unit := a.integral_unit
      integral_counit := a.integral_counit
      rationalAdjunction := adj
      rational_unit := ?_
      rational_counit := ?_
      pullComparison := a.pullComparison
      pushComparison := asIso beta
      unit := ?_
      counit := ?_ }
  · intro K
    exact realization_ulift_tmul_heq _ (pbcUniformizer l E)
      (a.integralAdjunction.unit.app K)
  · intro K
    exact realization_ulift_tmul_heq _ (pbcUniformizer l E)
      (a.integralAdjunction.counit.app K)
  · intro K
    dsimp only [asIso, Iso.mk]
    have hu := unit_mateEquiv adj adj' a.pullComparison.inv K
    change rU.realization.functor.map (adj.unit.app K) ≫ beta.app _ =
      adj'.unit.app (rU.realization.functor.obj K) ≫
        (CondensedERealization.fieldLowerStar l E k T U h).map
          (a.pullComparison.inv.app K) at hu
    change rU.realization.functor.map (adj.unit.app K) ≫ beta.app _ ≫
      (CondensedERealization.fieldLowerStar l E k T U h).map
        (a.pullComparison.hom.app K) = adj'.unit.app _
    rw [← Category.assoc, hu, Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
    exact (congrArg (fun f ↦ adj'.unit.app (rU.realization.functor.obj K) ≫ f)
      ((CondensedERealization.fieldLowerStar l E k T U h).map_id _)).trans
        (Category.comp_id _)
  · intro K
    dsimp only [asIso, Iso.mk]
    have hc := mateEquiv_counit adj adj' a.pullComparison.inv K
    change (AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleUpperStar
      (Profinite.continuousCoefficientRingObj E) l (CondensedERealization.Base.map T U h)).map
        (beta.app K) ≫ adj'.counit.app (rT.realization.functor.obj K) =
      a.pullComparison.inv.app _ ≫ rT.realization.functor.map (adj.counit.app K) at hc
    change rT.realization.functor.map (adj.counit.app K) =
      a.pullComparison.hom.app _ ≫
        (AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleUpperStar
          (Profinite.continuousCoefficientRingObj E) l
          (CondensedERealization.Base.map T U h)).map (beta.app K) ≫ adj'.counit.app _
    rw [hc, ← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]

/-- Existence of the normalized realization system, before any square is considered.
Source: Bhatt--Scholze, Proposition 6.8.14(2), Remark 6.8.15; the archived
local-presentation bridge specified by the realization blueprint.
(blueprint: lem-weil-pbc-condensed-e-system)

Proof. Identify the point-pullback coefficient object with continuous E-valued functions.
The finite quotient comparisons are fixed on constants; taking their inverse limit fixes
the integral coefficient comparison. Localizing gives the rational inclusion. The section
module equivalence identifies the internal action with this coefficient presentation.
The archived finite presentation condition agrees, on strata, with local finite freeness.
Derived scalar extension is fully faithful after rationalization by bounded-below
compactness applied to the uniformizer telescope. Every lisse rational sheaf has an
integral lattice; open-closed induction on a finite stratification and then bounded
truncation triangles give essential surjectivity. Ordinary pullback preserves complete
constructible complexes, and its completion unit supplies the prescribed completed
pullback comparison. Integral direct-image finiteness gives the restricted adjunction.
Tensor localization extends its unit and counit. Transporting through the equivalences
gives the continuous direct-image comparison as the right mate. The triangle equations
prove its unit and counit laws. The coefficient maps are precomposition on functions,
so their composition and identity laws give the normalized integral compositors;
tensoring gives the rational compositors and the two realization coherence equations.
All constructions include zero objects and empty schemes. This statement contains no
square, properness, or exchange comparison. -/
theorem condensedE_realization_system
    (l : ℕ) [Fact l.Prime] (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)] :
    Nonempty (CondensedERealization.Data l E k) := by
  classical
  let atObject (T : CondensedERealization.Base k) : CondensedERealization.At l E T.scheme := by
    letI : IsNoetherian T.scheme :=
      isNoetherian_of_locallyOfFiniteType (T.scheme ↘ Spec (.of k))
    letI : Fact (∃ n : ℕ, topologicalKrullDim T.scheme ≤ n) :=
      ⟨exists_topologicalKrullDim_le (T.scheme ↘ Spec (.of k))⟩
    letI : Fact (∀ t : T.scheme, IsUnit (l : T.scheme.presheaf.stalk t)) :=
      ⟨realization_prime_unit l k T⟩
    let s := Classical.choice (realization_scalar_functor l E T.scheme k)
    letI := realization_scalar_equivalence l E T.scheme s
    exact realizationAtOfScalar l E T.scheme s
  obtain ⟨S⟩ := CondensedERealization.condensedE_left_system l E k atObject
  refine ⟨{
    atObject := atObject
    along := fun T U h ↦ realizationAlongOfLeft l E k T U h _ _ (S.along T U h)
    integralComp := S.integralComp
    integralComp_normalization := S.integralComp_normalization
    rationalComp := S.rationalComp
    rationalComp_normalization := S.rationalComp_normalization
    composition := S.composition
    integralId := S.integralId
    integralId_normalization := S.integralId_normalization
    rationalId := S.rationalId
    rationalId_normalization := S.rationalId_normalization
    condensedId := S.condensedId
    condensedId_normalization := S.condensedId_normalization
    identity := S.identity }⟩

end WeilConjectures
