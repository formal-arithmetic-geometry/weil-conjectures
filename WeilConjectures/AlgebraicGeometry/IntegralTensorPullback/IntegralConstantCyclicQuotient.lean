/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralTensorPullback.IntegralTensorPullbackData

import all WeilConjectures.AlgebraicGeometry.DerivedNakayamaResolution
import all WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import all WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import all Mathlib.RingTheory.Ideal.Quotient.Index
import all WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
import all WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
import all Mathlib.Topology.Category.Profinite.EffectiveEpi
import all WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
import all Mathlib.Condensed.TopComparison
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
import all Mathlib.Topology.Algebra.Ring.Ideal
import all Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import all WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
import all WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntSheafLinear
import all WeilConjectures.CategoryTheory.Sites.MonObj
import all Mathlib.Algebra.Homology.ShortComplex.Ab
import all WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
import all Mathlib.Topology.Bases
import all Mathlib.Topology.MetricSpace.Pseudo.Defs
import all Mathlib.Analysis.SpecificLimits.Basic
import all Mathlib.Topology.LocallyConstant.Basic
import all WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.TensorMappingCone
import all WeilConjectures.CategoryTheory.Monoidal.Closed.UnitEnd
import all Mathlib.CategoryTheory.Center.Linear
import all Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Kernels
import all WeilConjectures.NumberTheory.Padics.ContinuousUniformizerDivision
import all Mathlib.Topology.Algebra.Order.Field
import all WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
import all Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp
import all Mathlib.CategoryTheory.Sites.Sheafification
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import all WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import all WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import all Mathlib.Algebra.Order.AbsoluteValue.Basic
import all Mathlib.LinearAlgebra.FiniteDimensional.Basic
import all Mathlib.NumberTheory.Padics.PadicNumbers
import all Mathlib.RingTheory.DiscreteValuationRing.Basic
import all Mathlib.RingTheory.Localization.FractionRing
import all WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
import all Mathlib.Analysis.Normed.Algebra.Ultra
import all Mathlib.Analysis.Normed.Module.FiniteDimension
import all Mathlib.NumberTheory.Padics.ProperSpace
import all Mathlib.Topology.Algebra.Valued.LocallyCompact
import all WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
import all WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
import all WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import all WeilConjectures.AlgebraicGeometry.FiniteConstantModel.FiniteConstantModelResolutionSupplement
import all WeilConjectures.AlgebraicGeometry.Condensed.CondensedPointDiscreteConstantComparison
import WeilConjectures.CategoryTheory.ModuleObjects.Linear
import Mathlib.Algebra.Category.ModuleCat.Kernels
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsMonoidal
import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.ProEtaleCoefficients.DerivedNakayamaResolution

/-! # The two coefficient units present the same positive cyclic quotient

Source: finite-reduction comparison in `det-lem-int-tensor-pullback.proof.md`.
(blueprint: lem-sfb-integral-constant-cyclic-quotient).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u v w a b c d
open CategoryTheory CategoryTheory.Limits MonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.IntegralTensorPullback
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private theorem adjointSquare
    {A : Type a} [Category.{b} A] {B : Type c} [Category.{d} B]
    {F : A ⥤ B} {G : B ⥤ A} (adj : F ⊣ G)
    {P Q : A} {R S : B} (a : P ⟶ Q) (b : R ⟶ S)
    (σ : P ⟶ G.obj R) (τ : Q ⟶ G.obj S)
    (h : a ≫ τ = σ ≫ G.map b) :
    F.map a ≫ (adj.homEquiv _ _).symm τ = (adj.homEquiv _ _).symm σ ≫ b := by
  exact adj.homEquiv_naturality_right_square a τ σ b h

private theorem scalarAction_eq (d : End (Mod.regular R)) (M : Mod C R) :
    (ρ_ M).inv ≫ (M ◁ d) ≫ (ρ_ M).hom =
      (Mod.smulNatTrans (S := R) (η[R] ≫ d.hom)).app M := by
  let t : 𝟙_ C ⟶ R := η[R] ≫ d.hom
  have hd : d = (Mod.smulNatTrans t).app (Mod.regular R) := by
    calc
      d = Mod.regularLift (Mod.regular R) t :=
        Mod.regular_hom_ext (Mod.one_comp_regularLift _ _).symm
      _ = _ := by
        apply Mod.hom_ext
        change (ρ_ R).inv ≫ R ◁ t ≫ μ[R] = (λ_ R).inv ≫ t ▷ R ≫ μ[R]
        exact Mod.rightUnitor_inv_whiskerLeft_mul_eq t
  change (ρ_ M).inv ≫ (M ◁ d) ≫ (ρ_ M).hom = (Mod.smulNatTrans t).app M
  rw [hd, ← Mod.smulNatTrans_app_tensor]
  change (ρ_ M).inv ≫ (Mod.smulNatTrans t).app (M ⊗ 𝟙_ (Mod C R)) ≫
    (ρ_ M).hom = (Mod.smulNatTrans t).app M
  have hn := (Mod.smulNatTrans t).naturality (ρ_ M).inv
  simp only [Functor.id_map] at hn
  rw [← Category.assoc, hn]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

private theorem scalarAction_comap (φ : R ⟶ S) [IsMonHom φ]
    (dS : End (Mod.regular S)) (dR : End (Mod.regular R))
    (h : dR.hom ≫ φ = φ ≫ dS.hom) (M : Mod C S) :
    (Mod.comap φ).map ((ρ_ M).inv ≫ (M ◁ dS) ≫ (ρ_ M).hom) =
      (ρ_ ((Mod.comap φ).obj M)).inv ≫
        ((Mod.comap φ).obj M ◁ dR) ≫ (ρ_ ((Mod.comap φ).obj M)).hom := by
  rw [scalarAction_eq, scalarAction_eq]
  apply Mod.hom_ext
  change Mod.globalSmul (R := S) (η[S] ≫ dS.hom) M =
    Mod.globalSmul (R := R) (η[R] ≫ dR.hom) ((Mod.comap φ).obj M)
  rw [Mod.globalSmul_comap]
  congr 1
  rw [Category.assoc, h, ← Category.assoc, IsMonHom.one_hom φ]

section ScalarActions
variable {C : Type v} [Category.{w} C] [Abelian C] [MonoidalCategory C]
  [SymmetricCategory C] [MonoidalClosed C]
  {R S : C} [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]

end ScalarActions

private def mapRegularIso
    {C : Type a} [Category.{b} C] [MonoidalCategory C]
    {D : Type c} [Category.{d} D] [MonoidalCategory D]
    (F : C ⥤ D) [F.LaxMonoidal] (R : C) [MonObj R] :
    (F.mapMod R).obj (Mod.regular R) ≅ Mod.regular (F.obj R) :=
  Mod.isoMk (Iso.refl _) (by
    simp only [Iso.refl_hom, Category.comp_id, whiskerLeft_id, Category.id_comp])

private def continuousScalarEnd (X : Scheme.{u}) (n : ℕ) :
    End (𝟙_ (AdicCompletion.Modules l E X)) :=
  (DerivedNakayama.regularPullbackIso l E X).inv ≫
    (DerivedNakayama.pullback l E X).map
      (DerivedNakayama.uniformizerEnd l E ^ (n + 1)) ≫
    (DerivedNakayama.regularPullbackIso l E X).hom

private theorem continuousCyclicQuotient (X : Scheme.{u}) (n : ℕ) :
    ∃ z : continuousScalarEnd l E X n ≫ AdicCompletion.finiteUnit l E X n = 0,
      Nonempty (IsColimit (CokernelCofork.ofπ (AdicCompletion.finiteUnit l E X n) z)) := by
  let F := DerivedNakayama.pullback l E X
  let e := DerivedNakayama.regularPullbackIso l E X
  let d := DerivedNakayama.uniformizerEnd l E ^ (n + 1)
  let r := DerivedNakayama.reductionHom l E (n + 1)
  have hr : r = AdicCompletion.quotientUnit l E n := by
    apply Mod.hom_ext
    rfl
  have hc := (DerivedNakayama.pointResolution l E (n + 1)).map_of_exact F
  have hz : continuousScalarEnd l E X n ≫ AdicCompletion.finiteUnit l E X n = 0 := by
    dsimp only [continuousScalarEnd, AdicCompletion.finiteUnit]
    rw [Category.assoc, Category.assoc, Iso.hom_inv_id_assoc,
      ← CategoryTheory.Functor.map_comp, ← hr]
    exact (congrArg (fun k ↦ e.inv ≫ F.map k)
      (DerivedNakayama.reduction_zero l E (n + 1))).trans (by simp)
  refine ⟨hz, ⟨?_⟩⟩
  exact IsCokernel.ofIso _ hc.gIsCokernel
    (CokernelCofork.ofπ (AdicCompletion.finiteUnit l E X n) hz)
    e e (Iso.refl _)
    (by
      change e.hom ≫ (e.inv ≫ F.map d ≫ e.hom) = F.map d ≫ e.hom
      simp only [Iso.hom_inv_id_assoc])
    (by
      change e.hom ≫ (e.inv ≫ F.map (AdicCompletion.quotientUnit l E n)) = F.map r ≫ 𝟙 _
      simp only [Iso.hom_inv_id_assoc, Category.comp_id, ← hr])

private theorem discreteScalarComparison (A : Type u) [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [DiscreteTopology A] :
    IsIso (FiniteConstantModel.scalarToContinuous A) := by
  let φ := constantToContinuousAb A
  have hφ : (coherentTopology Profinite.{u}).W (A := Ab.{u + 1}) φ :=
    (coherentTopology Profinite.{u}).W_of_isLocallyBijective φ
  have : IsIso ((presheafToSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).map φ) :=
    ((coherentTopology Profinite.{u}).W_iff φ).mp hφ
  change IsIso ((presheafToSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).map φ ≫
    (sheafificationAdjunction (coherentTopology Profinite.{u}) Ab.{u + 1}).counit.app
      (Profinite.continuousCoefficientRingObj A))
  infer_instance

private def scalarQuotient (n : ℕ) :
    ModuleCat.of (Padic.coefficientExtensionIntegers l E)
        (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) ⟶
      ModuleCat.of (Padic.coefficientExtensionIntegers l E)
        (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))) :=
  ModuleCat.ofHom
    { toFun := fun x ↦ ULift.up
        (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)) x.down)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }

private def scalarMultiply (n : ℕ) : End
    (ModuleCat.of (Padic.coefficientExtensionIntegers l E)
      (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))) :=
  ModuleCat.ofHom (LinearMap.lsmul (Padic.coefficientExtensionIntegers l E) _
    (Padic.coefficientExtensionUniformizer l E ^ (n + 1)))

private theorem scalarQuotient_exact (n : ℕ) :
    Function.Exact (scalarMultiply l E n).hom (scalarQuotient l E n).hom := by
  intro x
  constructor
  · intro hx
    have hx' : Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)) x.down = 0 :=
      congrArg ULift.down hx
    rw [Ideal.Quotient.eq_zero_iff_mem, Padic.coefficientExtensionIdeal,
      Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hx'
    obtain ⟨a, ha⟩ := hx'
    refine ⟨ULift.up a, ?_⟩
    apply ULift.ext
    change Padic.coefficientExtensionUniformizer l E ^ (n + 1) * a = x.down
    simpa only [mul_comm] using ha.symm
  · rintro ⟨y, rfl⟩
    apply ULift.ext
    change Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))
      (Padic.coefficientExtensionUniformizer l E ^ (n + 1) * y.down) = 0
    rw [map_mul]
    have hz : Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))
        (Padic.coefficientExtensionUniformizer l E ^ (n + 1)) = 0 := by
      rw [Ideal.Quotient.eq_zero_iff_mem, Padic.coefficientExtensionIdeal,
        Ideal.span_singleton_pow]
      exact Ideal.mem_span_singleton_self _
    rw [hz, zero_mul]

private theorem scalarQuotient_surjective (n : ℕ) :
    Function.Surjective (scalarQuotient l E n).hom := by
  intro x
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective x.down
  exact ⟨ULift.up y, ULift.ext _ _ hy⟩

private abbrev constantModuleFunctor :=
  FiniteConstantModel.scalarModules (Padic.coefficientExtensionIntegers l E) ⋙
    (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).mapMod
      (AddCommGrpCat.of (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)))

private def constantRegularIso :
    (constantModuleFunctor l E).obj
        (ModuleCat.of (Padic.coefficientExtensionIntegers l E)
          (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))) ≅
      Mod.regular (constantRing l E) :=
  ((constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).mapMod _).mapIso
    (FiniteConstantModel.scalarRegularIso (Padic.coefficientExtensionIntegers l E))

private def constantScalarEnd (n : ℕ) : End (Mod.regular (constantRing l E)) :=
  (constantRegularIso l E).inv ≫
    (constantModuleFunctor l E).map (scalarMultiply l E n) ≫
      (constantRegularIso l E).hom

private def constantPointQuotient (n : ℕ) :
    Mod.regular (constantRing l E) ⟶
      (Mod.comap (constantToIntegral l E)).obj
        (DerivedNakayama.quotientModule l E (n + 1)) :=
  Mod.comapUnitHom (constantToIntegral l E) ≫
    (Mod.comap (constantToIntegral l E)).map (AdicCompletion.quotientUnit l E n)

private theorem constantScalarEnd_compatibility (n : ℕ) :
    (constantScalarEnd l E n).hom ≫ constantToIntegral l E =
      constantToIntegral l E ≫ (DerivedNakayama.uniformizerEnd l E ^ (n + 1)).hom := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let a : AddCommGrpCat.of (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) ⟶
      AddCommGrpCat.of (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) :=
    AddCommGrpCat.ofHom (scalarMultiply l E n).hom.toAddMonoidHom
  have he : (constantScalarEnd l E n).hom =
      (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).map a := by
    change (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).map (𝟙 _) ≫
      (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).map a ≫
        (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).map (𝟙 _) = _
    simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  rw [he]
  change (presheafToSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).map
      ((Functor.const Profinite.{u}ᵒᵖ).map a) ≫
        ((sheafificationAdjunction (coherentTopology Profinite.{u}) Ab.{u + 1}).homEquiv
          _ (Profinite.continuousCoefficientRingObj
            (Padic.coefficientExtensionIntegers l E))).symm (FiniteConstantModel.constantFunctions
            (Padic.coefficientExtensionIntegers l E)) =
    ((sheafificationAdjunction (coherentTopology Profinite.{u}) Ab.{u + 1}).homEquiv
      _ (Profinite.continuousCoefficientRingObj
        (Padic.coefficientExtensionIntegers l E))).symm (FiniteConstantModel.constantFunctions
        (Padic.coefficientExtensionIntegers l E)) ≫
      (DerivedNakayama.uniformizerEnd l E ^ (n + 1)).hom
  apply adjointSquare (sheafificationAdjunction (coherentTopology Profinite.{u}) Ab.{u + 1})
  ext S x
  apply ULift.ext
  apply ContinuousMap.ext
  intro t
  change _ = (((DerivedNakayama.uniformizerEnd l E ^ (n + 1)).hom.hom.app S)
    (ULift.up (ContinuousMap.const S.unop x.down))).down t
  rw [DerivedNakayama.uniformizerPower_apply]
  rfl

private theorem constantPointQuotient_square (n : ℕ) :
    letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
    letI : MonObj ((constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)))) :=
      inferInstanceAs (MonObj (constantRing l E))
    (constantRegularIso l E).hom.hom ≫ (constantPointQuotient l E n).hom =
      ((constantModuleFunctor l E).map (scalarQuotient l E n)).hom ≫
        FiniteConstantModel.scalarToContinuous (Padic.coefficientExtensionRing l E (n + 1)) := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let : MonObj ((constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)))) :=
    inferInstanceAs (MonObj (constantRing l E))
  let q : AddCommGrpCat.of (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) ⟶
      AddCommGrpCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))) :=
    AddCommGrpCat.ofHom (scalarQuotient l E n).hom.toAddMonoidHom
  have he : (constantRegularIso l E).hom.hom = 𝟙 _ := by
    change (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).map (𝟙 _) = 𝟙 _
    exact (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).map_id _
  rw [he, Category.id_comp]
  change constantToIntegral l E ≫ DerivedNakayama.reductionRing l E (n + 1) =
    (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).map q ≫
      FiniteConstantModel.scalarToContinuous _
  symm
  change (presheafToSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).map
      ((Functor.const Profinite.{u}ᵒᵖ).map q) ≫
        ((sheafificationAdjunction (coherentTopology Profinite.{u}) Ab.{u + 1}).homEquiv
          _ (Profinite.continuousCoefficientRingObj
            (Padic.coefficientExtensionRing l E (n + 1)))).symm
              (FiniteConstantModel.constantFunctions
                (Padic.coefficientExtensionRing l E (n + 1))) =
    ((sheafificationAdjunction (coherentTopology Profinite.{u}) Ab.{u + 1}).homEquiv
      _ (Profinite.continuousCoefficientRingObj
        (Padic.coefficientExtensionIntegers l E))).symm (FiniteConstantModel.constantFunctions
        (Padic.coefficientExtensionIntegers l E)) ≫ DerivedNakayama.reductionRing l E (n + 1)
  apply adjointSquare (sheafificationAdjunction (coherentTopology Profinite.{u}) Ab.{u + 1})
  ext S x
  rfl

private theorem constantPointCokernel (n : ℕ) :
    ∃ z : constantScalarEnd l E n ≫ constantPointQuotient l E n = 0,
      Nonempty (IsColimit (CokernelCofork.ofπ (constantPointQuotient l E n) z)) := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let : MonObj ((constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)))) :=
    inferInstanceAs (MonObj (constantRing l E))
  let A := Padic.coefficientExtensionIntegers l E
  let B := Padic.coefficientExtensionRing l E (n + 1)
  let : DiscreteTopology B := DerivedNakayama.quotientDiscrete l E (n + 1)
  let : PreservesFiniteColimits (FiniteConstantModel.scalarModules A) :=
    FiniteConstantModel.scalarModules_preservesFiniteColimits A
  let : PreservesFiniteColimits (constantModuleFunctor l E) := by
    dsimp only [constantModuleFunctor]
    infer_instance
  let V : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) (constantRing l E) ⥤
      Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} := Mod.forget (constantRing l E)
  let L : ModuleCat.{u + 1} A ⥤ Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} :=
    constantModuleFunctor l E ⋙ V
  have h0 := ModuleCat.isColimitCokernelCofork (scalarMultiply l E n)
    (scalarQuotient l E n) (scalarQuotient_exact l E n) (scalarQuotient_surjective l E n)
  have hz : constantScalarEnd l E n ≫ constantPointQuotient l E n = 0 := by
    apply Mod.hom_ext
    change (constantScalarEnd l E n).hom ≫
      (constantToIntegral l E ≫ (AdicCompletion.quotientUnit l E n).hom) = 0
    rw [← Category.assoc, constantScalarEnd_compatibility, Category.assoc]
    change constantToIntegral l E ≫
      ((DerivedNakayama.uniformizerEnd l E ^ (n + 1)) ≫
        DerivedNakayama.reductionHom l E (n + 1)).hom = 0
    rw [DerivedNakayama.reduction_zero, Mod.zero_hom, comp_zero]
  refine ⟨hz, ⟨?_⟩⟩
  have : IsIso (FiniteConstantModel.scalarToContinuous B) := discreteScalarComparison B
  let e : L.obj (ModuleCat.of A (ULift.{u + 1} B)) ≅
      V.obj ((Mod.comap (constantToIntegral l E)).obj
        (DerivedNakayama.quotientModule l E (n + 1))) :=
    asIso (FiniteConstantModel.scalarToContinuous B)
  let ec := V.mapIso (constantRegularIso l E)
  have hc := isColimitCoforkMapOfIsColimit' L _ h0
  have hfinal : IsColimit (CokernelCofork.ofπ (V.map (constantPointQuotient l E n))
      (by rw [← V.map_comp, hz, V.map_zero]) :
        CokernelCofork (V.map (constantScalarEnd l E n))) := by
    refine IsCokernel.ofIso _ hc
      (CokernelCofork.ofπ (V.map (constantPointQuotient l E n))
        (by rw [← V.map_comp, hz, V.map_zero])) ec ec e ?_ ?_
    · change ec.hom ≫ (ec.inv ≫ L.map (scalarMultiply l E n) ≫ ec.hom) =
        L.map (scalarMultiply l E n) ≫ ec.hom
      simp only [Iso.hom_inv_id_assoc]
    · exact constantPointQuotient_square l E n
  let : ReflectsColimitsOfShape WalkingParallelPair V :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  exact isColimitOfReflects V ((isColimitMapCoconeCoforkEquiv' V hz).symm hfinal)

/-- The actual finite quotient unit and its constant restriction are cokernels of
compatible scalar endomorphisms of their respective units. Compatibility concerns
the action on every internal module, not just an equality of coefficient objects.

Source: blueprint `det-lem-int-tensor-pullback.proof.md`, positive finite reduction;
Stacks 099N(5), and the uniformizer resolution in the derived Nakayama lemma.
(blueprint: lem-sfb-integral-constant-cyclic-quotient).

Proof: take dR and dC to be multiplication by the (n+1)st power of the fixed
uniformizer on the continuous and constant units. The uniformizer resolution
identifies finiteUnit as the cokernel of dR. For dC, start with the exact sequence
of discrete O_E-modules given by multiplication by that power and reduction to
O_E/pi^(n+1). Its constant sheaf functor is exact. The canonical constant-function
map to the continuous finite quotient is an isomorphism: every continuous map to
the finite discrete ring is constant on the pieces of a finite clopen cover,
and agreement can be checked on that cover, including the empty cover. This map
preserves the quotient unit and the scalar action. Transport the constant cokernel
along it. On any continuous internal module, the two uniformizer scalar maps
agree after restriction: constantToIntegral sends the chosen scalar to its
constant continuous function; associativity of the action and the right unitor
identify the induced endomorphisms. Exact monoidal inverse image from the point
preserves the two cokernels and this scalar equation on X. The comparisons are
normalized by the given coefficient and quotient maps throughout. No module,
resolution or arbitrary coefficient isomorphism is chosen. -/
theorem integral_constant_cyclic_quotient (X : Scheme.{u}) (n : ℕ) :
    ∃ (dR : End (𝟙_ (AdicCompletion.Modules l E X)))
      (dC : End (𝟙_ (ConstantModules l E X))),
      (∃ zR : dR ≫ AdicCompletion.finiteUnit l E X n = 0,
        Nonempty (IsColimit (CokernelCofork.ofπ (AdicCompletion.finiteUnit l E X n) zR))) ∧
      (∃ zC : dC ≫
          (constantUnit l E X ≫
            (restriction l E X).map (AdicCompletion.finiteUnit l E X n)) = 0,
        Nonempty (IsColimit (CokernelCofork.ofπ
          (constantUnit l E X ≫
            (restriction l E X).map (AdicCompletion.finiteUnit l E X n)) zC))) ∧
      ∀ M : AdicCompletion.Modules l E X,
        (restriction l E X).map ((ρ_ M).inv ≫ (M ◁ dR) ≫ (ρ_ M).hom) =
          (ρ_ ((restriction l E X).obj M)).inv ≫
            ((restriction l E X).obj M ◁ dC) ≫
              (ρ_ ((restriction l E X).obj M)).hom := by
  let FC := (upperStarFromPoint X).mapMod (constantRing l E)
  let eC := mapRegularIso (upperStarFromPoint X) (constantRing l E)
  let dc : End (𝟙_ (ConstantModules l E X)) :=
    eC.inv ≫ FC.map (constantScalarEnd l E n) ≫ eC.hom
  let ec : FC.obj ((Mod.comap (constantToIntegral l E)).obj
      (DerivedNakayama.quotientModule l E (n + 1))) ≅
        (restriction l E X).obj (AdicCompletion.finiteModule l E X n) :=
    ((upperStarFromPoint X).mapModComapIso (constantToIntegral l E)).app
      (DerivedNakayama.quotientModule l E (n + 1))
  let rc := constantUnit l E X ≫
    (restriction l E X).map (AdicCompletion.finiteUnit l E X n)
  have hr : eC.inv ≫ FC.map (constantPointQuotient l E n) ≫ ec.hom = rc := by
    apply Mod.hom_ext
    change 𝟙 _ ≫ (upperStarFromPoint X).map
      (constantToIntegral l E ≫ DerivedNakayama.reductionRing l E (n + 1)) ≫ 𝟙 _ =
        (upperStarFromPoint X).map (constantToIntegral l E) ≫
          (𝟙 _ ≫ (upperStarFromPoint X).map (DerivedNakayama.reductionRing l E (n + 1)))
    simp only [CategoryTheory.Functor.map_comp, Category.comp_id, Category.id_comp]
  obtain ⟨z, ⟨hz⟩⟩ := constantPointCokernel l E n
  have zc : dc ≫ rc = 0 := by
    rw [← hr]
    change (eC.inv ≫ FC.map (constantScalarEnd l E n) ≫ eC.hom) ≫
      (eC.inv ≫ FC.map (constantPointQuotient l E n) ≫ ec.hom) = 0
    simp only [Category.assoc, Iso.hom_inv_id_assoc, ← FC.map_comp_assoc,
      z, FC.map_zero, zero_comp, comp_zero]
  have hc : IsColimit (CokernelCofork.ofπ rc zc) := by
    let hc := CokernelCofork.mapIsColimit _ hz FC
    refine IsCokernel.ofIso _ hc _ eC eC ec ?_ ?_
    · change eC.hom ≫ (eC.inv ≫ FC.map (constantScalarEnd l E n) ≫ eC.hom) =
        FC.map (constantScalarEnd l E n) ≫ eC.hom
      simp only [Iso.hom_inv_id_assoc]
    · change eC.hom ≫ rc = FC.map (constantPointQuotient l E n) ≫ ec.hom
      rw [← hr, Iso.hom_inv_id_assoc]
  refine ⟨continuousScalarEnd l E X n, dc,
    continuousCyclicQuotient l E X n, ⟨zc, ⟨hc⟩⟩, ?_⟩
  intro M
  apply scalarAction_comap
  change (𝟙 _ ≫ (upperStarFromPoint X).map (constantScalarEnd l E n).hom ≫ 𝟙 _) ≫
      (upperStarFromPoint X).map (constantToIntegral l E) =
    (upperStarFromPoint X).map (constantToIntegral l E) ≫
      (𝟙 _ ≫
        (upperStarFromPoint X).map (DerivedNakayama.uniformizerEnd l E ^ (n + 1)).hom ≫ 𝟙 _)
  simp only [Category.id_comp, Category.comp_id]
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
    constantScalarEnd_compatibility]

set_option maxHeartbeats 2000000 in
-- Allow the nested coefficient and module-object transports to normalize.
end AlgebraicGeometry.ProEtale.IntegralTensorPullback
