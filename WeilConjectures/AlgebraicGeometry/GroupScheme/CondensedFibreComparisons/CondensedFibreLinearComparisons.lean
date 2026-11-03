/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeCondensedModule.NativeCondensedModuleLocalFrobenius
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import WeilConjectures.CategoryTheory.ModuleObjects.RegularEndBijective
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.PadicAlgClGlobalSections
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.StalkLowerStarProj
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusDetailed
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebra
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
public import WeilConjectures.WeilObject.Sheaf.Stalk
public import WeilConjectures.ZetaSeries
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs
public import WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.CategoryTheory.ModuleObjects.ProEtaleCoefficients.ModuleEqualizerInternalHom
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.ProEtalePullbackInternalHom
import WeilConjectures.ProperBaseChange.CondensedFiniteFreeTensorExact
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.Mathlib.RingTheory.Henselian
import WeilConjectures.RingTheory.ProEtale.WContractible
import WeilConjectures.AlgebraicGeometry.ProEtale.Projective
public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleLocallyFreeModels
public import WeilConjectures.AlgebraicGeometry.GroupScheme.CondensedFibreComparisons.CondensedFibreLocalOperators
public import WeilConjectures.AlgebraicGeometry.GroupScheme.CondensedFibreDerived.LisseSingleDualWeil
public import WeilConjectures.AlgebraicGeometry.ProEtale.SepClosedPointLift
public import WeilConjectures.CategoryTheory.ModuleObjects.FreeMap
public import WeilConjectures.CategoryTheory.ModuleObjects.Linear
public import WeilConjectures.CategoryTheory.ModuleObjects.RegularEnd
public import WeilConjectures.CategoryTheory.Monoidal.Closed.IhomComparison
public import WeilConjectures.CategoryTheory.Monoidal.Closed.IhomComparisonIso
public import WeilConjectures.CategoryTheory.Preadditive.CoyonedaSectionsExtendScalars
public import WeilConjectures.CategoryTheory.Preadditive.NatTransIsIso
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.NaturalTransformationOplax
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LocallyFreeDualizable

/-! # Tensor and dual fibres of condensed Weil sheaves

Source: literature/blueprint/latest/blueprint/part-weights-riemann-hypothesis/
sec-deligne-laumon-a1/sec-purity-of-the-lisse-part-of-the-fourier-transform/
sk-p-dl-a1-some-weight/lem-fd-realified-kernel-real.proof.md, Steps 1--2
(blueprint: lem-fd-condensed-fibre-linear-operations-comparisons).

All modules, point sections and local operators are the recorded condensed constructions
of def-weil-local-frobenius-trace (`WeilConjectures.NativeCondensedModule`), used directly.
The comparison maps are normalized by tensoring sections and evaluating functionals.
Finite direct sums are represented by finite products in the abelian module category.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open CategoryTheory.Endofunctor
open scoped CategoryTheory.Obj TensorProduct

namespace WeilConjectures.CondensedFibreComparisons

open WeilConjectures.NativeCondensedModule

/-- The coefficient inverse image is left exact, as its two sheaf inverse images are.
Source: Cartesian coefficient pullback
(blueprint: lem-fd-condensed-fibre-linear-operations-comparisons). -/
instance coefficientPullbackFiniteLimits (T : Scheme.{u}) :
    PreservesFiniteLimits (upperStarFromPoint T) := by
  unfold upperStarFromPoint pointUpperStar
  infer_instance

/-- The coefficient inverse image is additive by preservation of binary products.
Source: Cartesian coefficient pullback
(blueprint: lem-fd-condensed-fibre-linear-operations-comparisons). -/
instance coefficientPullbackAdditive (T : Scheme.{u}) : (upperStarFromPoint T).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- A strong monoidal functor carries a dual pair to a dual pair. -/
private theorem normalized_dual_isIso
    {C E : Type*} [Category C] [Category E] [MonoidalCategory C] [MonoidalCategory E]
    [MonoidalClosed C] [MonoidalClosed E] [BraidedCategory C]
    (G : C ⥤ E) [G.Monoidal] (A : C) (hA : IsDualizable A) :
    IsIso ((Functor.LaxMonoidal.ihomComparison G A).natTrans.app (𝟙_ C) ≫
      (ihom (G.obj A)).map (Functor.OplaxMonoidal.η G)) := by
  obtain ⟨_⟩ := hA
  let Y := Aᘁ
  let : ExactPairing Y A := BraidedCategory.exactPairing_swap A Y
  let := ExactPairing.map G Y A
  have he :
      G.map (MonoidalClosed.curry (ε_ Y A)) ≫
          (Functor.LaxMonoidal.ihomComparison G A).natTrans.app (𝟙_ C) ≫
          (ihom (G.obj A)).map (Functor.OplaxMonoidal.η G) =
        MonoidalClosed.curry (ε_ (G.obj Y) (G.obj A)) := by
    rw [Functor.LaxMonoidal.ihomComparison_app_eq_curry,
      ← MonoidalClosed.curry_natural_right, ← MonoidalClosed.curry_natural_left]
    congr 1
    simp only [Category.assoc]
    rw [Functor.LaxMonoidal.μ_natural_right_assoc, ← G.map_comp_assoc,
      MonoidalClosed.whiskerLeft_curry_ihom_ev_app]
    rfl
  have : IsIso (G.map (MonoidalClosed.curry (ε_ Y A)) ≫
      (Functor.LaxMonoidal.ihomComparison G A).natTrans.app (𝟙_ C) ≫
      (ihom (G.obj A)).map (Functor.OplaxMonoidal.η G)) := by
    rw [he]
    infer_instance
  exact IsIso.of_isIso_comp_left (G.map (MonoidalClosed.curry (ε_ Y A))) _

/-- Lisse modules are dualizable for the actual relative tensor product. -/
private theorem lisse_isDualizable (l : ℕ) [Fact l.Prime]
    {T : Scheme.{u}} (L : Modules l T)
    (hL : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) L) :
    IsDualizable L := by
  apply AlgebraicGeometry.ProEtale.IsLocallyFree.isDualizable
  obtain ⟨U, hU⟩ := hL
  exact ⟨U, fun i ↦ (CondensedRing.freeAt_iff_standard _ (U.f i) L).mpr (hU i)⟩

/-- A local finite basis pulls back to a global finite basis at a geometric point. -/
private theorem fibre_isFree (l : ℕ) [Fact l.Prime]
    (D : FiniteFieldDatum.{u}) [IsAlgClosed D.k] {T : Scheme.{u}}
    (z : Spec (.of D.k) ⟶ T) (L : Modules l T)
    (hL : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) L) :
    Mod.IsFree (condensedRingObj (Profinite.padicAlgClRingObj l) (Spec (.of D.k)))
      ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z).obj L) := by
  obtain ⟨U, hU⟩ := hL
  obtain ⟨i, a, ha⟩ := U.exists_comp_eq_of_isSepClosed_of_proetale z
  subst z
  have hf := (hU i).map (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a)
    (CondensedRing.upperStarObjRegularIso (Profinite.padicAlgClRingObj l) a)
  exact hf.of_iso
    ((CondensedRing.upperStarComp (Profinite.padicAlgClRingObj l) a (U.f i)).app L).symm

/-- A normalized section tensorator is invertible when its second module is finite free. -/
private theorem pointTensor_isIso (l : ℕ) [Fact l.Prime]
    (D : FiniteFieldDatum.{u}) [IsAlgClosed D.k]
    (M N : Modules l (Spec (.of D.k)))
    (hN : Mod.IsFree (condensedRingObj (Profinite.padicAlgClRingObj l)
      (Spec (.of D.k))) N) :
    let : (pointSections l D.k).LaxMonoidal := sectionsLax (pointScalarsOp l D.k)
    IsIso (Functor.LaxMonoidal.μ (pointSections l D.k) M N) := by
  let G := pointSections l D.k
  have : G.Additive := inferInstanceAs ((preadditiveCoyonedaObj (𝟙_ _)) ⋙
    ModuleCat.restrictScalars (pointScalarsOp l D.k)).Additive
  let : (pointSections l D.k).LaxMonoidal := sectionsLax (pointScalarsOp l D.k)
  have he : IsIso (Functor.LaxMonoidal.ε G) := by
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    exact pointSectionsUnit_bijective l D.k
  let τ : G ⋙ tensorLeft (G.obj M) ⟶ tensorLeft M ⋙ G :=
    { app Q := Functor.LaxMonoidal.μ G M Q
      naturality _ _ f := Functor.LaxMonoidal.μ_natural_right G M f }
  have : IsIso (τ.app (𝟙_ _)) :=
    Functor.LaxMonoidal.isIso_μ_tensorUnit_right G M
  obtain ⟨r, ⟨e⟩⟩ := hN
  have := NatTrans.isIso_app_biproduct_fin τ (𝟙_ _) r
  exact NatTrans.isIso_app_of_iso τ e

/-- Sections preserve internal Homs out of a finite-free module. -/
private theorem pointHom_isIso (l : ℕ) [Fact l.Prime]
    (D : FiniteFieldDatum.{u}) [IsAlgClosed D.k]
    (M N : Modules l (Spec (.of D.k)))
    (hM : Mod.IsFree (condensedRingObj (Profinite.padicAlgClRingObj l)
      (Spec (.of D.k))) M) :
    let : (pointSections l D.k).LaxMonoidal := sectionsLax (pointScalarsOp l D.k)
    IsIso ((Functor.LaxMonoidal.ihomComparison (pointSections l D.k) M).natTrans.app N) := by
  let G := pointSections l D.k
  have : G.Additive := inferInstanceAs ((preadditiveCoyonedaObj (𝟙_ _)) ⋙
    ModuleCat.restrictScalars (pointScalarsOp l D.k)).Additive
  let : G.LaxMonoidal := sectionsLax (pointScalarsOp l D.k)
  have : IsIso (Functor.LaxMonoidal.ε G) := by
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    exact pointSectionsUnit_bijective l D.k
  obtain ⟨r, ⟨e⟩⟩ := hM
  have hu : ∀ _ : Fin r,
      IsIso ((Functor.LaxMonoidal.ihomComparison G (𝟙_ _)).natTrans.app N) :=
    fun _ ↦ Functor.LaxMonoidal.isIso_ihomComparison_app_unit G N
  have hb : IsIso ((Functor.LaxMonoidal.ihomComparison G
      (⨁ fun _ : Fin r ↦ 𝟙_ _)).natTrans.app N) := by
    exact @Functor.LaxMonoidal.isIso_ihomComparison_app_biproduct
      _ _ _ _ _ _ _ _ G _ _ _ _ _ _ (Fin r) _ (fun _ ↦ 𝟙_ _) _ N hu
  exact (Functor.LaxMonoidal.isIso_ihomComparison_app_iff_of_iso_left G e N).mpr hb

/-- The normalized internal-Hom comparison on a geometric fibre is invertible. -/
private theorem fibreHom_isIso (l : ℕ) [Fact l.Prime]
    (D : FiniteFieldDatum.{u}) [IsAlgClosed D.k] {T : Scheme.{u}}
    (z : Spec (.of D.k) ⟶ T) (L : Modules l T)
    (hL : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) L) :
    let : (pointSections l D.k).LaxMonoidal := sectionsLax (pointScalarsOp l D.k)
    IsIso ((Functor.LaxMonoidal.ihomComparison
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z ⋙ pointSections l D.k)
      L).natTrans.app (𝟙_ _)) := by
  let P := CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z
  let G := pointSections l D.k
  have : G.Additive := inferInstanceAs ((preadditiveCoyonedaObj (𝟙_ _)) ⋙
    ModuleCat.restrictScalars (pointScalarsOp l D.k)).Additive
  let : G.LaxMonoidal := sectionsLax (pointScalarsOp l D.k)
  have hn := normalized_dual_isIso P L (lisse_isDualizable l L hL)
  have : IsIso ((Functor.LaxMonoidal.ihomComparison P L).natTrans.app (𝟙_ _)) :=
    IsIso.of_isIso_comp_right _ ((ihom (P.obj L)).map (Functor.OplaxMonoidal.η P))
  have := pointHom_isIso l D (P.obj L) (P.obj (𝟙_ _)) (fibre_isFree l D z L hL)
  change IsIso ((Functor.LaxMonoidal.ihomComparison (P ⋙ G) L).natTrans.app (𝟙_ _))
  rw [Functor.LaxMonoidal.ihomComparison_comp_app]
  infer_instance

/-- The tensor section determines an invertible linear map on the finite-free fibre. -/
private theorem tensor_comparison_exists (l : ℕ) [Fact l.Prime]
    (D : FiniteFieldDatum.{u}) [IsAlgClosed D.k] {T : Scheme.{u}}
    (z : Spec (.of D.k) ⟶ T) (F L : Modules l T)
    (hL : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) L) :
    ∃ e : fibre l D (F ⊗ L) z ≃ₗ[ULift.{u + 1} (PadicAlgCl l)]
        (fibre l D F z ⊗[ULift.{u + 1} (PadicAlgCl l)] fibre l D L z),
      ∀ v w, e (tensorSection l D z F L v w) =
        TensorProduct.tmul (ULift.{u + 1} (PadicAlgCl l)) v w := by
  let P := CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z
  let G := pointSections l D.k
  have : G.Additive := inferInstanceAs ((preadditiveCoyonedaObj (𝟙_ _)) ⋙
    ModuleCat.restrictScalars (pointScalarsOp l D.k)).Additive
  let : (pointSections l D.k).LaxMonoidal := sectionsLax (pointScalarsOp l D.k)
  have := pointTensor_isIso l D (P.obj F) (P.obj L) (fibre_isFree l D z L hL)
  let e : G.obj (P.obj F) ⊗ G.obj (P.obj L) ≅ G.obj (P.obj (F ⊗ L)) :=
    asIso (Functor.LaxMonoidal.μ G (P.obj F) (P.obj L)) ≪≫
      G.mapIso (Functor.Monoidal.μIso P F L)
  refine ⟨e.symm.toLinearEquiv, fun v w ↦ ?_⟩
  have he : e.hom (TensorProduct.tmul (ULift.{u + 1} (PadicAlgCl l)) v w) =
      tensorSection l D z F L v w := by
    rfl
  rw [← he]
  exact e.toLinearEquiv.symm_apply_apply _

/-- Evaluation identifies sections of the ordinary dual with the linear dual. -/
private theorem dual_comparison_of_isIso (l : ℕ) [Fact l.Prime]
    (D : FiniteFieldDatum.{u}) [IsAlgClosed D.k] {T : Scheme.{u}}
    (z : Spec (.of D.k) ⟶ T) (L : Modules l T)
    (hL : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) L) :
    let : (pointSections l D.k).LaxMonoidal := sectionsLax (pointScalarsOp l D.k)
    IsIso ((Functor.LaxMonoidal.ihomComparison
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z ⋙ pointSections l D.k)
      L).natTrans.app (𝟙_ _)) →
    ∃ e : fibre l D ((ihom L).obj (𝟙_ _)) z ≃ₗ[ULift.{u + 1} (PadicAlgCl l)]
        Module.Dual (ULift.{u + 1} (PadicAlgCl l)) (fibre l D L z),
      ∀ f v, pointUnitEndRingHom l D.k (e f v).down = evaluation l D z L f v := by
  dsimp only
  intro hiso
  let P := CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z
  let G := pointSections l D.k
  have : G.Additive := inferInstanceAs ((preadditiveCoyonedaObj (𝟙_ _)) ⋙
    ModuleCat.restrictScalars (pointScalarsOp l D.k)).Additive
  let H := P ⋙ G
  let : G.LaxMonoidal := sectionsLax (pointScalarsOp l D.k)
  letI : IsIso ((Functor.LaxMonoidal.ihomComparison H L).natTrans.app (𝟙_ _)) := by
    exact hiso
  let u : H.obj (𝟙_ _) ≅ 𝟙_ _ :=
    G.mapIso (Functor.Monoidal.εIso P).symm ≪≫ (pointSectionsUnitIso l D.k).symm
  let e : H.obj ((ihom L).obj (𝟙_ _)) ≅ (ihom (H.obj L)).obj (𝟙_ _) :=
    asIso ((Functor.LaxMonoidal.ihomComparison H L).natTrans.app (𝟙_ _)) ≪≫
      (ihom (H.obj L)).mapIso u
  refine ⟨e.toLinearEquiv.trans ModuleCat.homLinearEquiv, ?_⟩
  intro f v
  have he : (e.hom f).hom v =
      (Functor.LaxMonoidal.μ H L ((ihom L).obj (𝟙_ _)) ≫
        H.map ((ihom.ev L).app (𝟙_ _)) ≫ u.hom)
        (TensorProduct.tmul (ULift.{u + 1} (PadicAlgCl l)) v f) := by
    have hm : e.hom = MonoidalClosed.curry
        (Functor.LaxMonoidal.μ H L ((ihom L).obj (𝟙_ _)) ≫
          H.map ((ihom.ev L).app (𝟙_ _)) ≫ u.hom) := by
      dsimp only [e, Iso.trans_hom, Functor.mapIso_hom, asIso_hom]
      rw [Functor.LaxMonoidal.ihomComparison_app_eq_curry,
        ← MonoidalClosed.curry_natural_right, Category.assoc]
    rw [hm]
    exact ModuleCat.monoidalClosed_curry _ v f
  have hunit (a : ULift.{u + 1} (PadicAlgCl l)) :
      (pointSectionsUnitIso l D.k).hom a = pointUnitEndRingHom l D.k a.down := by
    change pointUnitEndRingHom l D.k a.down ≫ 𝟙 _ = _
    exact Category.comp_id _
  change pointUnitEndRingHom l D.k ((e.hom f).hom v).down = _
  rw [← hunit, he]
  simp only [u, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    ModuleCat.comp_apply]
  change (pointSectionsUnitIso l D.k).hom
      ((pointSectionsUnitIso l D.k).inv
        (evaluation l D z L f v)) = evaluation l D z L f v
  exact ConcreteCategory.congr_hom (pointSectionsUnitIso l D.k).inv_hom_id _

/-- Evaluation identifies sections of the ordinary dual with the linear dual. -/
private theorem dual_comparison_exists (l : ℕ) [Fact l.Prime]
    (D : FiniteFieldDatum.{u}) [IsAlgClosed D.k] {T : Scheme.{u}}
    (z : Spec (.of D.k) ⟶ T) (L : Modules l T)
    (hL : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) L) :
    ∃ e : fibre l D ((ihom L).obj (𝟙_ _)) z ≃ₗ[ULift.{u + 1} (PadicAlgCl l)]
        Module.Dual (ULift.{u + 1} (PadicAlgCl l)) (fibre l D L z),
      ∀ f v, pointUnitEndRingHom l D.k (e f v).down = evaluation l D z L f v := by
  apply dual_comparison_of_isIso l D z L hL
  exact fibreHom_isIso l D z L hL

/-- The specified tensor section commutes with both input morphisms. -/
private theorem tensorSection_natural (l : ℕ) [Fact l.Prime]
    (D : FiniteFieldDatum.{u}) [IsAlgClosed D.k] {T : Scheme.{u}}
    (z : Spec (.of D.k) ⟶ T) {F L F' L' : Modules l T}
    (f : F ⟶ F') (a : L ⟶ L') (v : fibre l D F z) (w : fibre l D L z) :
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z ⋙ pointSections l D.k).map
        (f ⊗ₘ a) (tensorSection l D z F L v w) =
      tensorSection l D z F' L'
        ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z ⋙
          pointSections l D.k).map f v)
        ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z ⋙
          pointSections l D.k).map a w) := by
  let P := CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z
  change tensorSection l D z F L v w ≫ P.map (f ⊗ₘ a) =
    tensorSection l D z F' L' (v ≫ P.map f) (w ≫ P.map a)
  simp only [tensorSection, Category.assoc]
  rw [← Functor.LaxMonoidal.μ_natural]
  simp only [← Category.assoc, tensorHom_comp_tensorHom]
  rfl

/-- Evaluation commutes with precomposition in its module argument. -/
private theorem evaluation_pre (l : ℕ) [Fact l.Prime]
    (D : FiniteFieldDatum.{u}) [IsAlgClosed D.k] {T : Scheme.{u}}
    (z : Spec (.of D.k) ⟶ T) {L L' : Modules l T} (f : L ⟶ L')
    (a : fibre l D ((ihom L').obj (𝟙_ (Modules l T))) z) (v : fibre l D L z) :
    evaluation l D z L
        ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z ⋙
          pointSections l D.k).map ((MonoidalClosed.pre f).app (𝟙_ _)) a) v =
      evaluation l D z L' a
        ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z ⋙
          pointSections l D.k).map f v) := by
  let P := CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z
  have hn :
      P.obj L ◁ P.map ((MonoidalClosed.pre f).app (𝟙_ _)) ≫
          Functor.LaxMonoidal.μ P L _ ≫ P.map ((ihom.ev L).app (𝟙_ _)) =
        P.map f ▷ P.obj ((ihom L').obj (𝟙_ _)) ≫
          Functor.LaxMonoidal.μ P L' _ ≫ P.map ((ihom.ev L').app (𝟙_ _)) := by
    rw [Functor.LaxMonoidal.μ_natural_right_assoc, ← P.map_comp,
      MonoidalClosed.id_tensor_pre_app_comp_ev, P.map_comp,
      ← Functor.LaxMonoidal.μ_natural_left_assoc]
  simp only [evaluation, tensorSection, Category.assoc]
  change (λ_ _).inv ≫ (v ⊗ₘ (a ≫ P.map _)) ≫ _ ≫ _ ≫ _ =
    (λ_ _).inv ≫ ((v ≫ P.map f) ⊗ₘ a) ≫ _ ≫ _ ≫ _
  rw [← Category.comp_id v, ← tensorHom_comp_tensorHom, id_tensorHom]
  conv_rhs => rw [← Category.comp_id a, ← tensorHom_comp_tensorHom, tensorHom_id]
  simpa only [Category.assoc, Category.comp_id] using
    congrArg (fun t ↦ (λ_ _).inv ≫ (v ⊗ₘ a) ≫ t ≫
      (Functor.Monoidal.εIso P).inv) hn

/-- The section formula determines the tensor comparison's naturality. -/
private theorem tensor_natural_of_normalized (l : ℕ) [Fact l.Prime]
    (D : FiniteFieldDatum.{u}) [IsAlgClosed D.k] {T : Scheme.{u}}
    (z : Spec (.of D.k) ⟶ T) {F L F' L' : Modules l T}
    (f : F ⟶ F') (a : L ⟶ L')
    (e : fibre l D (F ⊗ L) z ≃ₗ[ULift.{u + 1} (PadicAlgCl l)]
      (fibre l D F z ⊗[ULift.{u + 1} (PadicAlgCl l)] fibre l D L z))
    (e' : fibre l D (F' ⊗ L') z ≃ₗ[ULift.{u + 1} (PadicAlgCl l)]
      (fibre l D F' z ⊗[ULift.{u + 1} (PadicAlgCl l)] fibre l D L' z))
    (he : ∀ v w, e (tensorSection l D z F L v w) =
      TensorProduct.tmul (ULift.{u + 1} (PadicAlgCl l)) v w)
    (he' : ∀ v w, e' (tensorSection l D z F' L' v w) =
      TensorProduct.tmul (ULift.{u + 1} (PadicAlgCl l)) v w)
    (x : fibre l D (F ⊗ L) z) :
    e' ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z ⋙
        pointSections l D.k).map (f ⊗ₘ a) x) =
      TensorProduct.map
        ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z ⋙
          pointSections l D.k).map f).hom
        ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z ⋙
          pointSections l D.k).map a).hom (e x) := by
  obtain ⟨x, rfl⟩ := e.symm.surjective x
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, ConcreteCategory.hom_ofHom, ModuleCat.hom_zero]
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  | tmul v w =>
    have h : e.symm (TensorProduct.tmul (ULift.{u + 1} (PadicAlgCl l)) v w) =
        tensorSection l D z F L v w := (e.symm_apply_eq).mpr (he v w).symm
    rw [h, tensorSection_natural, he', he]
    rfl

/-- Constant scalars identify endomorphisms of the coefficient unit faithfully. -/
private theorem pointScalar_injective (l : ℕ) [Fact l.Prime]
    (D : FiniteFieldDatum.{u}) [IsAlgClosed D.k] :
    Function.Injective (fun a : ULift.{u + 1} (PadicAlgCl l) ↦
      pointUnitEndRingHom l D.k a.down) := by
  convert (pointSectionsUnit_bijective l D.k).1 using 1
  funext a
  change _ = pointUnitEndRingHom l D.k a.down ≫ 𝟙 _
  exact (Category.comp_id _).symm

/-- The ordinary comparisons and their naturality leave only derived coherence. -/
private theorem comparisons_of_derived (l : ℕ) [Fact l.Prime]
    (D : FiniteFieldDatum.{u}) [IsAlgClosed D.k] {T : Scheme.{u}}
    (g : T ≅ T) (z : Spec (.of D.k) ⟶ T)
    (hd : ∀ (L : IsoAlgebra
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g.hom)),
    IsConstantModelConstructible (Profinite.padicAlgClRingObj l) T L.carrier →
    IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) L.carrier →
    let P := CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g.hom
    let S := DerivedCategory.singleFunctor (Modules l T) 0
    letI : P.mapDerivedCategory.Monoidal := Functor.Monoidal.transport
      (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
        (Profinite.padicAlgClRingObj l) g.hom)
    let K := S.obj L.carrier
    let phi := (P.mapDerivedCategorySingleFunctor 0).app L.carrier ≪≫ S.mapIso L.str
    ∃ e : S.obj (dualWeil l g L).carrier ≅ (ihom K).obj (𝟙_ _),
      (P.mapDerivedCategorySingleFunctor 0).app (dualWeil l g L).carrier ≪≫
          S.mapIso (dualWeil l g L).str ≪≫ e =
        P.mapDerivedCategory.mapIso e ≪≫
          Functor.Monoidal.ihomObjIso P.mapDerivedCategory K (𝟙_ _) ≪≫
          (ihom (P.mapDerivedCategory.obj K)).mapIso
            (Functor.Monoidal.εIso P.mapDerivedCategory).symm ≪≫
          (MonoidalClosed.internalHom.mapIso phi.symm.op).app (𝟙_ _)) :
    Nonempty (Comparisons l D g z) := by
  classical
  let et := fun (F L : IsoAlgebra
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g.hom))
      (h : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) L.carrier) ↦
    (tensor_comparison_exists l D z F.carrier L.carrier h).choose
  have ht : ∀ F L h v w, et F L h (tensorSection l D z F.carrier L.carrier v w) =
      TensorProduct.tmul (ULift.{u + 1} (PadicAlgCl l)) v w :=
    fun F L h ↦ (tensor_comparison_exists l D z F.carrier L.carrier h).choose_spec
  let ed := fun (L : IsoAlgebra
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g.hom))
      (h : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) L.carrier) ↦
    (dual_comparison_exists l D z L.carrier h).choose
  have hdv : ∀ L h f v, pointUnitEndRingHom l D.k (ed L h f v).down =
      evaluation l D z L.carrier f v :=
    fun L h ↦ (dual_comparison_exists l D z L.carrier h).choose_spec
  refine ⟨{ tensor := fun F L _ _ h ↦ et F L h
            tensor_sections := fun F L _ _ h ↦ ht F L h
            dual := fun L _ h ↦ ed L h
            dual_evaluation := fun L _ h ↦ hdv L h
            derived_dual := hd
            tensor_natural := ?_
            dual_natural := ?_ }⟩
  · intro F L F' L' hF hL hLis hF' hL' hLis' f a v
    exact tensor_natural_of_normalized l D z f a _ _
      (ht F L hLis) (ht F' L' hLis') v
  · intro L L' hL hLis hL' hLis' f a v
    apply pointScalar_injective l D
    dsimp only
    exact (hdv L hLis _ v).trans
      ((evaluation_pre l D z f a v).trans (hdv L' hLis' a _).symm)

/-- The return equation holds for every compatible lift, by pullback uniqueness. -/
private theorem compatible_point_return
    (D : FiniteFieldDatum.{u}) (T₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom]
    (x : {x : T₀.left // x ∈ closedPoints T₀.left})
    (ι : T₀.left.residueField x.val →+* D.k)
    (hι : ι.comp (T₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k)
    (z : Spec (.of D.k) ⟶ (D.geometricFiber T₀).left)
    (hz₁ : z ≫ pullback.fst T₀.hom
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) =
      Spec.map (CommRingCat.ofHom ι) ≫ T₀.left.fromSpecResidueField x.val)
    (hz₂ : z ≫ pullback.snd T₀.hom
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) = 𝟙 _) :
    letI := (T₀.hom.residueFieldAlgebraMap x.val).toAlgebra
    let n := Module.finrank D.k₀ (T₀.left.residueField x.val) - 1
    z ≫ localPositivePower (D.geometricFrobenius T₀).hom n =
      localPositivePower (frobeniusPointIso D).hom n ≫ z := by
  have hz : z = localClosedPoint D T₀ x ι hι := by
    apply pullback.hom_ext
    · simpa only [localClosedPoint, pullback.lift_fst] using hz₁
    · simpa only [localClosedPoint, pullback.lift_snd] using hz₂
  subst z
  exact localClosedPoint_return D T₀ x ι hι

/-- Tensor the two Weil data using the inverse pullback tensorator.
Source: latest blueprint, realified-kernel proof Step 2
(blueprint: lem-fd-condensed-fibre-linear-operations-comparisons). -/
def tensorWeil (l : ℕ) [Fact l.Prime] {T : Scheme.{u}} (g : T ≅ T)
    (F L : IsoAlgebra
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g.hom)) :
    IsoAlgebra (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g.hom) :=
  IsoAlgebra.mk (F.carrier ⊗ L.carrier)
    ((Functor.Monoidal.μIso
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g.hom) _ _).symm ≪≫
        tensorIso F.str L.str)

/-- The ordinary internal dual, with its evaluation-transpose contragredient datum.
Source: latest blueprint, realified-kernel proof Step 1, and the contragredient composite
of sk-def-sf-weil-complexes (blueprint: lem-fd-condensed-fibre-linear-operations-comparisons). -/
def dualWeil (l : ℕ) [Fact l.Prime] {T : Scheme.{u}} (g : T ≅ T)
    (L : IsoAlgebra
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g.hom)) :
    IsoAlgebra (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g.hom) :=
  IsoAlgebra.mk ((ihom L.carrier).obj (𝟙_ (Modules l T)))
    (Functor.Monoidal.ihomObjIso
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g.hom) L.carrier (𝟙_ _) ≪≫
      (ihom _).mapIso
        (Functor.Monoidal.εIso
          (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g.hom)).symm ≪≫
      (MonoidalClosed.internalHom.mapIso L.str.symm.op).app (𝟙_ _))

/-- A finite direct sum with the direct sum of the Weil data, using the finite product model.
Source: latest blueprint, realified-kernel proof Step 2
(blueprint: lem-fd-condensed-fibre-linear-operations-comparisons). -/
def sumWeil (l : ℕ) [Fact l.Prime] {T : Scheme.{u}} (g : T ≅ T) (I : Type u) [Finite I]
    (F : I → IsoAlgebra (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g.hom)) :
    IsoAlgebra (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g.hom) :=
  IsoAlgebra.mk (∏ᶜ fun i ↦ (F i).carrier)
    (PreservesProduct.iso
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g.hom)
      (fun i ↦ (F i).carrier) ≪≫ Pi.mapIso (fun i ↦ (F i).str))

/-- The section obtained by tensoring two sections and applying the pullback tensorator.
Source: latest blueprint, realified-kernel proof Step 2
(blueprint: lem-fd-condensed-fibre-linear-operations-comparisons). -/
def tensorSection (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u}) [IsAlgClosed D.k]
    {T : Scheme.{u}} (z : Spec (.of D.k) ⟶ T) (F L : Modules l T)
    (v : fibre l D F z) (w : fibre l D L z) : fibre l D (F ⊗ L) z :=
  (λ_ (𝟙_ (Modules l (Spec (.of D.k))))).inv ≫ (v ⊗ₘ w) ≫
    Functor.LaxMonoidal.μ (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z) F L

/-- Evaluation as a section of the coefficient unit. Constants embed by pointUnitEndRingHom.
Source: evaluation normalization
(blueprint: lem-fd-condensed-fibre-linear-operations-comparisons).
-/
def evaluation (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u}) [IsAlgClosed D.k]
    {T : Scheme.{u}} (z : Spec (.of D.k) ⟶ T) (L : Modules l T)
    (f : fibre l D ((ihom L).obj (𝟙_ (Modules l T))) z) (v : fibre l D L z) :
    End (𝟙_ (Modules l (Spec (.of D.k)))) :=
  tensorSection l D z L _ v f ≫
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z).map
      ((ihom.ev L).app (𝟙_ _)) ≫
    (Functor.Monoidal.εIso
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z)).inv

set_option maxHeartbeats 800000 in
-- The dependent fibre tensor-section equation needs this elaboration budget.
/-- Natural fibre comparisons, specified by tensoring sections and by evaluation.
Source: latest blueprint, realified-kernel proof Steps 1--2
(blueprint: lem-fd-condensed-fibre-linear-operations-comparisons). -/
structure Comparisons (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u}) [IsAlgClosed D.k]
    {T : Scheme.{u}} (g : T ≅ T) (z : Spec (.of D.k) ⟶ T) where
  tensor : ∀ (F L : IsoAlgebra
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g.hom)),
    IsConstantModelConstructible (Profinite.padicAlgClRingObj l) T F.carrier →
    IsConstantModelConstructible (Profinite.padicAlgClRingObj l) T L.carrier →
    IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) L.carrier →
    fibre l D (F.carrier ⊗ L.carrier) z ≃ₗ[ULift.{u + 1} (PadicAlgCl l)]
      (fibre l D F.carrier z ⊗[ULift.{u + 1} (PadicAlgCl l)] fibre l D L.carrier z)
  tensor_sections : ∀ (F L : IsoAlgebra
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g.hom)) hF hL hLis
      (v : fibre l D F.carrier z) (w : fibre l D L.carrier z),
    tensor F L hF hL hLis (tensorSection l D z F.carrier L.carrier v w) =
      TensorProduct.tmul (ULift.{u + 1} (PadicAlgCl l)) v w
  dual : ∀ (L : IsoAlgebra
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g.hom)),
    IsConstantModelConstructible (Profinite.padicAlgClRingObj l) T L.carrier →
    IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) L.carrier →
    fibre l D ((ihom L.carrier).obj (𝟙_ (Modules l T))) z ≃ₗ[ULift.{u + 1} (PadicAlgCl l)]
      Module.Dual (ULift.{u + 1} (PadicAlgCl l)) (fibre l D L.carrier z)
  dual_evaluation : ∀ (L : IsoAlgebra
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g.hom))
      hL hLis f v,
    pointUnitEndRingHom l D.k (dual L hL hLis f v).down =
      evaluation l D z L.carrier f v
  derived_dual : ∀ (L : IsoAlgebra
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g.hom)),
    IsConstantModelConstructible (Profinite.padicAlgClRingObj l) T L.carrier →
    IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) L.carrier →
    let P := CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g.hom
    let S := DerivedCategory.singleFunctor (Modules l T) 0
    letI : P.mapDerivedCategory.Monoidal := Functor.Monoidal.transport
      (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
        (Profinite.padicAlgClRingObj l) g.hom)
    let K := S.obj L.carrier
    let phi := (P.mapDerivedCategorySingleFunctor 0).app L.carrier ≪≫ S.mapIso L.str
    ∃ e : S.obj (dualWeil l g L).carrier ≅ (ihom K).obj (𝟙_ _),
      (P.mapDerivedCategorySingleFunctor 0).app (dualWeil l g L).carrier ≪≫
          S.mapIso (dualWeil l g L).str ≪≫ e =
        P.mapDerivedCategory.mapIso e ≪≫
          Functor.Monoidal.ihomObjIso P.mapDerivedCategory K (𝟙_ _) ≪≫
          (ihom (P.mapDerivedCategory.obj K)).mapIso
            (Functor.Monoidal.εIso P.mapDerivedCategory).symm ≪≫
          (MonoidalClosed.internalHom.mapIso phi.symm.op).app (𝟙_ _)
  tensor_natural : ∀ (F L F' L' : IsoAlgebra
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g.hom))
      hF hL hLis hF' hL' hLis'
      (f : F.carrier ⟶ F'.carrier) (a : L.carrier ⟶ L'.carrier)
      (v : fibre l D (F.carrier ⊗ L.carrier) z),
    tensor F' L' hF' hL' hLis'
      ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z ⋙
        pointSections l D.k).map (f ⊗ₘ a) v) =
      TensorProduct.map
        ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z ⋙
          pointSections l D.k).map f).hom
        ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z ⋙
          pointSections l D.k).map a).hom (tensor F L hF hL hLis v)
  dual_natural : ∀ (L L' : IsoAlgebra
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g.hom))
      hL hLis hL' hLis'
      (f : L.carrier ⟶ L'.carrier)
      (a : fibre l D ((ihom L'.carrier).obj (𝟙_ (Modules l T))) z) (v : fibre l D L.carrier z),
    dual L hL hLis
      ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z ⋙
        pointSections l D.k).map ((MonoidalClosed.pre f).app (𝟙_ _)) a) v =
      dual L' hL' hLis' a
        ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z ⋙
          pointSections l D.k).map f v)

/-- Frobenius under the specified comparisons, including the finite-sum projections.
Source: latest blueprint, realified-kernel proof Steps 1--2
(blueprint: lem-fd-condensed-fibre-linear-operations-comparisons). -/
structure WeilCompatibility (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u})
    [IsAlgClosed D.k] {T : Scheme.{u}} (g : T ≅ T) (z : Spec (.of D.k) ⟶ T) (n : ℕ)
    (h : z ≫ localPositivePower g.hom n =
      localPositivePower (frobeniusPointIso D).hom n ≫ z) (c : Comparisons l D g z) : Prop where
  tensor_frobenius : ∀ (F L : IsoAlgebra
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g.hom)) hF hL hLis
      (v : fibre l D (F.carrier ⊗ L.carrier) z),
    c.tensor F L hF hL hLis
      ((operator l D g.hom (F.carrier ⊗ L.carrier)
        (tensorWeil l g F L).str z n h).hom v) =
      TensorProduct.map (operator l D g.hom F.carrier F.str z n h).hom
        (operator l D g.hom L.carrier L.str z n h).hom
        (c.tensor F L hF hL hLis v)
  dual_frobenius : ∀ (L : IsoAlgebra
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g.hom)) hL hLis
      (f : fibre l D ((ihom L.carrier).obj (𝟙_ (Modules l T))) z)
      (v : fibre l D L.carrier z),
    c.dual L hL hLis
      ((operator l D g.hom ((ihom L.carrier).obj (𝟙_ (Modules l T)))
        (dualWeil l g L).str z n h).hom f) v =
      c.dual L hL hLis f
        ((transport l D g.hom L.carrier L.str z z n h).inv.hom v)
  sum_frobenius : ∀ (I : Type u) [Finite I]
      (F : I → IsoAlgebra
        (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g.hom)),
    (∀ i, IsConstantModelConstructible (Profinite.padicAlgClRingObj l) T (F i).carrier) →
    IsIso (piComparison
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z ⋙
        pointSections l D.k) (fun i ↦ (F i).carrier)) ∧
    ∀ i : I,
      operator l D g.hom (∏ᶜ fun i ↦ (F i).carrier)
        (sumWeil l g I F).str z n h ≫
        (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z ⋙
          pointSections l D.k).map (Pi.π (fun j ↦ (F j).carrier) i) =
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z ⋙
          pointSections l D.k).map (Pi.π (fun j ↦ (F j).carrier) i) ≫
        operator l D g.hom (F i).carrier (F i).str z n h

/-- At every geometric point the normalized tensor and dual fibre
comparisons are natural; at compatible closed-point lifts they intertwine local
geometric Frobenius, including finite sums.
Source: literature/blueprint/latest/blueprint/part-weights-riemann-hypothesis/
sec-deligne-laumon-a1/sec-purity-of-the-lisse-part-of-the-fourier-transform/
sk-p-dl-a1-some-weight/lem-fd-realified-kernel-real.proof.md, Steps 1--2
(blueprint: lem-fd-condensed-fibre-linear-operations-comparisons).

Proof (the six DAG steps):
1. Exact module inverse image pulls the finite-free local models of L to the point.
The algebraically closed field is strictly henselian and w-contractible: its maximal
ideal is zero, its residue field is separably closed, and its component space is a point.
The projectivity theorem for a w-contractible affine splits a trivializing cover of the
terminal point. Connectedness selects one member, giving a global finite-free basis.
2. Tensoring sections defines the comparison, which in that basis sends v tensor (a_j)
to (a_j v). Its inverse sends (v_j) to the sum of v_j tensor e_j. This proves invertibility
without making the comparison depend on the basis. Functoriality gives tensor naturality.
3. On each trivializing pro-etale slice, restriction commutes with internal Hom and
pullback preserves the finite products representing the dual. Evaluation therefore
identifies the two dual bases. Sections give the usual perfect pairing over Lambda,
and precomposition commutes with evaluation, giving contravariant naturality.
4. The tensor Weil datum uses the inverse tensorator. The dual datum uses the closed
comparison, coefficient-unit map and inverse input datum, hence preserves evaluation.
Internal Hom from L is locally a finite product, hence exact. Applying it to a K-injective
resolution of the unit shows its derived Hom has only the ordinary dual in degree zero.
The augmentation is a quasi-isomorphism compatible with evaluation and with these three
arrows, giving the derived-dual identification and its Weil equation.
5. Induct on the closed-point degree to tensor the iterated data. The pullback
compositors and the point return preserve tensoring sections; the unit return fixes
scalars. The tensor operator equation holds on pure tensors, which span the tensor product.
6. Iterate the evaluation identity to obtain (Bf)(Av)=f(v); replace v by A inverse v.
This is the inverse-transpose equation. Additive point pullback and sections preserve
finite biproducts and their injections and projections, and the iterates and return
commute with those maps. Thus the direct-sum comparison is invertible and intertwines
the block diagonal operators. The same formulas include rank zero and the empty sum. -/
theorem condensed_fibre_linear_operations_comparisons
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (T₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom]
    [IsSeparated T₀.hom] :
    (letI : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
    (∀ z : Spec (.of D.k) ⟶ pullback T₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))),
      Nonempty (Comparisons l D (D.geometricFrobenius T₀) z)) ∧
    ∀ (x : {x : T₀.left // x ∈ closedPoints T₀.left})
      (ι : T₀.left.residueField x.val →+* D.k)
      (_hι : ι.comp (T₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k)
      (z : Spec (.of D.k) ⟶ (D.geometricFiber T₀).left)
      (_hz₁ : z ≫ pullback.fst T₀.hom
          (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) =
        Spec.map (CommRingCat.ofHom ι) ≫ T₀.left.fromSpecResidueField x.val)
      (_hz₂ : z ≫ pullback.snd T₀.hom
          (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) = 𝟙 _),
      letI := (T₀.hom.residueFieldAlgebraMap x.val).toAlgebra
      let n := Module.finrank D.k₀ (T₀.left.residueField x.val) - 1
      ∃ (h : z ≫ localPositivePower (D.geometricFrobenius T₀).hom n =
          localPositivePower (frobeniusPointIso D).hom n ≫ z)
        (c : Comparisons l D (D.geometricFrobenius T₀) z),
        WeilCompatibility l D (D.geometricFrobenius T₀) z n h c) := by
  classical
  letI : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  have hc (z : Spec (.of D.k) ⟶ (D.geometricFiber T₀).left) :
      Nonempty (Comparisons l D (D.geometricFrobenius T₀) z) := by
    apply comparisons_of_derived
    intro L hL hLis
    exact CondensedFibreDerived.lisse_single_dual_weil l (D.geometricFrobenius T₀) L hL hLis
  refine ⟨hc, ?_⟩
  intro x ι hι z hz₁ hz₂
  letI := (T₀.hom.residueFieldAlgebraMap x.val).toAlgebra
  let n := Module.finrank D.k₀ (T₀.left.residueField x.val) - 1
  have h := compatible_point_return D T₀ x ι hι z hz₁ hz₂
  obtain ⟨c⟩ := hc z
  exact ⟨h, c, local_operator_compatibility l D (D.geometricFrobenius T₀) z n h c⟩

end WeilConjectures.CondensedFibreComparisons
