/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.OrderedExchange.ProEtaleConstantReductionTower
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
import all WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
import all WeilConjectures.AlgebraicGeometry.OrderedExchange.ProEtaleConstantReductionModels
import all WeilConjectures.AlgebraicGeometry.CompletedConstantAlgebraFlatQuotients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.CoverLifting
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.FlatScalarRestrictionKFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import WeilConjectures.Algebra.Homology.SmoothPurity.ChangeOfRingsTensorCancellationIndependentCoefficientsSupplement
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import Mathlib.CategoryTheory.Adjunction.Additive
import all WeilConjectures.AlgebraicGeometry.Strict.Tower.StrictTowerExchangeMateNormalization
import all WeilConjectures.CategoryTheory.FlatScalarTowerLimit.FlatScalarTowerLimitSquare
import all WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedPullbackReflection
import WeilConjectures.AlgebraicGeometry.Stratum.StratumCompletionUnitRestriction
import WeilConjectures.AlgebraicGeometry.BoundedConstructibleTower
import WeilConjectures.SixFunctors.Etale.Derived.CoefficientChangeUnitDerived

/-! # Coefficient normalization of the raw ordered completed exchange

Source: main-20261015 blueprint, proper base change, completed-exchange-coherence,
second proof paragraph; strict coefficient supplement, Stacks Tags 099M, 099N,
0A07 and 0E48 (blueprint: def-weil-pbc-ordered-coefficient-comparison-data).

The maps below retain their ordinary-section, universal-derived-counit and completion-unit
normalizations. The ambient constant and completed module categories remain distinct.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.OrderedExchange

-- Prefer the concrete pro-etale site and module instances to abstract corner projections.
attribute [local instance 0] SheafOfModules.RingedTensorCorner.category
  SheafOfModules.RingedTensorCorner.derived

private theorem orderedAbSheafify (T : Scheme.{t}) :
    HasSheafify (ProEt.topology T) AddCommGrpCat.{t + 1} :=
  WeilConjectures.integralCoefficientAbSheafify.{t, 0} T

private theorem orderedAbLocallyBijective (T : Scheme.{t}) :
    (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{t + 1} :=
  WeilConjectures.integralCoefficientAbLocallyBijective.{t, 0} T

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem orderedRestrictLimits (T : Scheme.{t})
    {R B : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ B) :
    PreservesLimitsOfShape ℕᵒᵖ (reductionRestrict T φ) := by
  let := orderedAbSheafify T
  let := orderedAbLocallyBijective T
  let r := reductionRestrict T φ
  let F := SheafOfModules.forget.{t + 1} (reductionModuleRing T R) ⋙
    PresheafOfModules.toPresheaf (reductionModuleRing T R).obj
  let e : SheafOfModules.forget.{t + 1} (reductionModuleRing T B) ⋙
      PresheafOfModules.toPresheaf (reductionModuleRing T B).obj ≅ r ⋙ F := Iso.refl _
  have : PreservesLimitsOfShape ℕᵒᵖ (r ⋙ F) :=
    preservesLimitsOfShape_of_natIso e
  have : ReflectsLimitsOfShape ℕᵒᵖ F := reflectsLimitsOfShape_of_reflectsIsomorphisms
  exact preservesLimitsOfShape_of_reflects_of_preserves r F

set_option backward.isDefEq.respectTransparency.types true in
private theorem uniqueLimitComparison {C E : Type*} [Category C] [Category E]
    [HasLimitsOfShape ℕᵒᵖ C] [HasLimitsOfShape ℕᵒᵖ E]
    (r : C ⥤ E) [PreservesLimitsOfShape ℕᵒᵖ r] :
    ∃! e : lim ⋙ r ≅ (Functor.whiskeringRight ℕᵒᵖ C E).obj r ⋙ lim,
      ∀ (Z : ℕᵒᵖ ⥤ C) (n : ℕ),
        e.hom.app Z ≫ limit.π (Z ⋙ r) (op n) = r.map (limit.π Z (op n)) := by
  refine ⟨preservesLimitNatIso (J := ℕᵒᵖ) r, ?_, ?_⟩
  · intro Z n
    exact preservesLimitIso_hom_π r Z (op n)
  · intro e he
    apply Iso.ext
    apply NatTrans.ext
    funext Z
    apply limit.hom_ext
    intro n
    exact (he Z n.unop).trans (preservesLimitIso_hom_π r Z n).symm

attribute [local irreducible] completedAdicChangeData completedAdicDerivedChange
  HasDerivedCategory.standard Functor.mapDerivedCategory
  Functor.mapDerivedCategoryFactors Functor.mapDerivedCategoryFactorsh
  completedAdicChange reductionChange reductionDerivedChange reductionHomotopy
  completedReductionTower reduction

attribute [local instance 3000] orderedAbSheafify orderedAbLocallyBijective
  reductionModulesHasDerivedCategory reductionTowerHasDerivedCategory
  reductionRingModulesHasDerivedCategory

-- Normalize the two ordinary presentations of scalar restriction before matching complexes.
set_option allowUnsafeReducibility true in
attribute [local reducible] reductionRestrict completedReductionComplexTowerFunctor

variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)

private theorem orderedScalarFlat (T : Scheme.{t}) :
    SheafOfModules.IsFlatOnSite.{t + 1, t, t + 1, t + 1}
      ((SheafOfModules.restrictScalars ((adicLisseForget T).map (exchangeScalar d T))).obj
        (SheafOfModules.unit ((adicLisseForget T).obj (d.completedRing T)))) := by
  let := d.noetherian
  have hc : ∀ n : ℕ, exchangeScalar d T ≫ (pbcCompletedComparison T d).inv ≫
      limit.π (adicLisseRingSystem T d.ideal) (op n) =
        (constantSheaf (ProEt.topology T) CommRingCat.{t + 1}).map
          (CommRingCat.ofHom (Ideal.Quotient.mk (d.ideal ^ (n + 1)))) := by
    intro n
    dsimp only [exchangeScalar]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    exact (adicDatumScalar_exists T
      { toCompleteCoefficientDatum := d.toCompleteCoefficientDatum,
        quotientFinite := d.quotientFinite }).exists.choose_spec n
  exact (completed_constant_algebra_flat_quotients T d.ideal _
    (pbcCompletedComparison T d) (exchangeScalar d T) hc).1

theorem exchangeScalar_comp_projection (T : Scheme.{t}) (n : ℕ) :
    exchangeScalar d T ≫ (pbcCompletedComparison T d).inv ≫
      limit.π (adicLisseRingSystem T d.ideal) (op n) =
        (constantSheaf (ProEt.topology T) CommRingCat.{t + 1}).map
          (CommRingCat.ofHom (Ideal.Quotient.mk (d.ideal ^ (n + 1)))) := by
  dsimp only [exchangeScalar]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact (adicDatumScalar_exists T
    { toCompleteCoefficientDatum := d.toCompleteCoefficientDatum,
      quotientFinite := d.quotientFinite }).exists.choose_spec n

theorem projection_eq_comparison (T : Scheme.{t}) (n : ℕ) :
    d.projection T n = (pbcCompletedComparison T d).inv ≫
      limit.π (adicLisseRingSystem T d.ideal) (op n) ≫
        (pbcLevelConstantComparison T d n).hom := by
  have h := HasLimit.isoOfNatIso_inv_π (pbcConstantSystemComparison T d) (op n)
  unfold pbcCompletedComparison
  rw [reassoc_of% h]
  simp [pbcConstantSystemComparison, completedReductionProjection, reductionCoefficientSystem]

theorem quotient_eq_constant (T : Scheme.{t}) (n : ℕ) :
    quotient d T n = (constantSheaf (ProEt.topology T) CommRingCat.{t + 1}).map
        (CommRingCat.ofHom (Ideal.Quotient.mk (d.ideal ^ (n + 1)))) ≫
      (pbcLevelConstantComparison T d n).hom := by
  unfold quotient
  rw [projection_eq_comparison, ← exchangeScalar_comp_projection]
  simp only [Category.assoc]

theorem quotient_surjective (T : Scheme.{t}) (n : ℕ) (U : T.ProEtᵒᵖ) :
    Function.Surjective ((quotient d T n).hom.app U) := by
  let := d.noetherian
  rw [quotient_eq_constant]
  let V : (CompletedConstantAlgebra.smallSite T)ᵒᵖ := op (AsSmall.up.obj U.unop)
  have hs := (ConstantCompletion.flat_and_quotients_quotient
    (CompletedConstantAlgebra.smallTopology T) A d.ideal n (AsSmall.up.obj U.unop)).1
  let iA := (CompletedConstantAlgebra.constantsIso T).app (CommRingCat.of A)
  let iQ := (CompletedConstantAlgebra.constantsIso T).app
    (CommRingCat.of (A ⧸ d.ideal ^ (n + 1)))
  have hn := (CompletedConstantAlgebra.constantsIso T).hom.naturality
    (CommRingCat.ofHom (Ideal.Quotient.mk (d.ideal ^ (n + 1))))
  let dd := pbcLevelConstantComparison T d n
  intro y
  obtain ⟨x, hx⟩ := hs (iQ.hom.hom.app V (dd.inv.hom.app U y))
  refine ⟨iA.inv.hom.app V x, ?_⟩
  have h1 := ConcreteCategory.congr_hom (congrArg (fun k ↦ k.hom.app V) hn)
    (iA.inv.hom.app V x)
  have hA : iA.hom.hom.app V (iA.inv.hom.app V x) = x :=
    ConcreteCategory.congr_hom (congrArg (fun k ↦ k.hom.app V) iA.inv_hom_id) x
  have hQ (z : _) : iQ.inv.hom.app V (iQ.hom.hom.app V z) = z :=
    ConcreteCategory.congr_hom (congrArg (fun k ↦ k.hom.app V) iQ.hom_inv_id) z
  have hd : dd.hom.hom.app U (dd.inv.hom.app U y) = y :=
    ConcreteCategory.congr_hom (congrArg (fun k ↦ k.hom.app U) dd.inv_hom_id) y
  change iQ.hom.hom.app V (((constantSheaf (ProEt.topology T) CommRingCat.{t + 1}).map
      (CommRingCat.ofHom (Ideal.Quotient.mk (d.ideal ^ (n + 1))))).hom.app U
        (iA.inv.hom.app V x)) =
    ((ConstantCompletion.quotient (CompletedConstantAlgebra.smallTopology T) A d.ideal n).hom.app V)
      (iA.hom.hom.app V (iA.inv.hom.app V x)) at h1
  rw [hA, hx] at h1
  have h2 := congrArg (iQ.inv.hom.app V) h1
  rw [hQ, hQ] at h2
  change dd.hom.hom.app U _ = y
  exact (congrArg (dd.hom.hom.app U) h2).trans hd

theorem projection_ker_le (T : Scheme.{t}) (n : ℕ) (U : T.ProEtᵒᵖ)
    (b : (d.completedRing T).obj.obj U) (hb : (d.projection T n).hom.app U b = 0) :
    b ∈ Ideal.span (Set.range (fun a : ↥(d.ideal ^ (n + 1)) ↦
      (exchangeScalar d T).hom.app U ((adicLisseConstantUnit T A).app U (a : A)))) := by
  let := d.noetherian
  let J := Ideal.span (Set.range (fun a : ↥(d.ideal ^ (n + 1)) ↦
      (exchangeScalar d T).hom.app U ((adicLisseConstantUnit T A).app U (a : A))))
  have h := (CompletedConstantAlgebra.projection_surjective_and_kernel T d.ideal
    (pbcCompletedComparison T d) (exchangeScalar d T)
    (exchangeScalar_comp_projection d T) n (pbcLevelConstantComparison T d n)
    (d.projection T n) (projection_eq_comparison d T n) U).2
    ((d.completedRing T).obj.obj U ⧸ J) J.mkQ
    (fun a ↦ (Submodule.Quotient.mk_eq_zero J).2 (Ideal.subset_span ⟨a, rfl⟩)) b hb
  exact (Submodule.Quotient.mk_eq_zero J).1 h

theorem quotient_unit_eq_zero (T : Scheme.{t}) (n : ℕ) (U : T.ProEtᵒᵖ) (a : A)
    (ha : a ∈ d.ideal ^ (n + 1)) :
    (quotient d T n).hom.app U ((adicLisseConstantUnit T A).app U a) = 0 := by
  rw [quotient_eq_constant]
  have hn := ConcreteCategory.congr_hom (congrArg (fun k ↦ k.app U)
    (toSheafify_naturality (ProEt.topology T)
      ((Functor.const T.ProEtᵒᵖ).map
        (CommRingCat.ofHom (Ideal.Quotient.mk (d.ideal ^ (n + 1))))))) a
  change (adicLisseConstantUnit T (A ⧸ d.ideal ^ (n + 1))).app U
      (Ideal.Quotient.mk (d.ideal ^ (n + 1)) a) =
    (((constantSheaf (ProEt.topology T) CommRingCat.{t + 1}).map
      (CommRingCat.ofHom (Ideal.Quotient.mk (d.ideal ^ (n + 1))))).hom.app U
        ((adicLisseConstantUnit T A).app U a)) at hn
  change (pbcLevelConstantComparison T d n).hom.hom.app U
    (((constantSheaf (ProEt.topology T) CommRingCat.{t + 1}).map
      (CommRingCat.ofHom (Ideal.Quotient.mk (d.ideal ^ (n + 1))))).hom.app U
        ((adicLisseConstantUnit T A).app U a)) = 0
  rw [← hn, Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero, map_zero]

/-- Maps out of a scalar extension given by an ordinary linear map, with the pure-tensor
formula. -/
theorem changeLift_exists (X : Scheme.{t})
    {R S : Sheaf (ProEt.topology X) CommRingCat.{t + 1}} (φ : R ⟶ S)
    (N : reductionModules X R) (Y : reductionModules X S)
    (v : N ⟶ (reductionRestrict X φ).obj Y) :
    ∃ F : (reductionChange X φ).obj N ⟶ Y, ∀ (U : X.ProEtᵒᵖ) (s : S.obj.obj U)
      (x : N.val.obj U),
      F.val.app U (reductionTensorSection X φ N U s x) =
        s • (show Y.val.obj U from v.val.app U x) := by
  let adj := (ordinaryAdjunction_exists X φ).choose
  let F := (adj.homEquiv N Y).symm v
  refine ⟨F, ?_⟩
  intro U s x
  have hb : F.val.app U (reductionTensorSection X φ N U 1 x) = v.val.app U x := by
    have hh := (ordinaryAdjunction_exists X φ).choose_spec N Y F U x
    rw [Equiv.apply_symm_apply] at hh
    exact (eq_of_heq hh).symm
  have ht := tensorSection_smul X φ N U s 1 x
  rw [mul_one] at ht
  rw [← ht, map_smul, hb]

/-- Maps out of a scalar extension are determined on sheafified pure tensors. -/
theorem change_hom_ext (X : Scheme.{t})
    {R S : Sheaf (ProEt.topology X) CommRingCat.{t + 1}} (φ : R ⟶ S)
    (N : reductionModules X R) (Y : reductionModules X S)
    (f g : (reductionChange X φ).obj N ⟶ Y)
    (h : ∀ (U : X.ProEtᵒᵖ) (s : S.obj.obj U) (x : N.val.obj U),
      f.val.app U (reductionTensorSection X φ N U s x) =
        g.val.app U (reductionTensorSection X φ N U s x)) : f = g := by
  have h' := level_hom_ext X φ N ((reductionRestrict X φ).obj Y)
    ((reductionRestrict X φ).map f) ((reductionRestrict X φ).map g) h
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  exact congrArg (fun k ↦ k.val.app U y) h'

/-- On the constant-coefficient restriction of a completed module, the quotient unit is
linear over the completed ring through its finite projection. -/
theorem quotientUnit_smul (T : Scheme.{t}) (n : ℕ)
    (M : reductionModules T (d.completedRing T)) (U : T.ProEtᵒᵖ)
    (r : (d.completedRing T).obj.obj U) (x : M.val.obj U) :
    reductionTensorSection T (quotient d T n)
        ((reductionRestrict T (exchangeScalar d T)).obj M) U 1 (r • x) =
      reductionTensorSection T (quotient d T n)
        ((reductionRestrict T (exchangeScalar d T)).obj M) U
          ((d.projection T n).hom.app U r) x := by
  let N := (reductionRestrict T (exchangeScalar d T)).obj M
  let q := quotient d T n
  let u := reductionUnit T q N
  have hu (y : M.val.obj U) : u.val.app U y = reductionTensorSection T q N U 1 y :=
    reductionUnit_apply T q N U y
  have hlin (a : (exchangeConstantRing T A).obj.obj U) (y : M.val.obj U) :
      reductionTensorSection T q N U 1 ((exchangeScalar d T).hom.app U a • y) =
        reductionTensorSection T q N U (q.hom.app U a) y := by
    have h := (u.val.app U).hom.map_smul a y
    change u.val.app U ((exchangeScalar d T).hom.app U a • y) =
      q.hom.app U a • (show ((reductionChange T q).obj N).val.obj U from u.val.app U y) at h
    rw [hu, hu, tensorSection_smul, mul_one] at h
    exact h
  have hadd (y z : M.val.obj U) :
      reductionTensorSection T q N U 1 (y + z) =
        reductionTensorSection T q N U 1 y + reductionTensorSection T q N U 1 z := by
    rw [← hu, ← hu, ← hu]
    exact map_add (u.val.app U).hom y z
  have hzero : reductionTensorSection T q N U 1 (0 : M.val.obj U) = 0 := by
    rw [← hu]
    exact map_zero (u.val.app U).hom
  have hspan (b : (d.completedRing T).obj.obj U)
      (hb : b ∈ Ideal.span (Set.range (fun a : ↥(d.ideal ^ (n + 1)) ↦
        (exchangeScalar d T).hom.app U ((adicLisseConstantUnit T A).app U (a : A))))) :
      ∀ y : M.val.obj U, reductionTensorSection T q N U 1 (b • y) = 0 := by
    induction hb using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨a, rfl⟩ := hb
      intro y
      rw [hlin, quotient_unit_eq_zero d T n U a a.property]
      have h0 := tensorSection_smul T q N U 0 1 y
      rw [zero_mul, zero_smul] at h0
      exact h0.symm
    | zero =>
      intro y
      rw [zero_smul, hzero]
    | add b b' _ _ hb hb' =>
      intro y
      rw [add_smul, hadd, hb, hb', add_zero]
    | smul a b _ hb =>
      intro y
      rw [smul_eq_mul, mul_comm, mul_smul, hb]
  obtain ⟨a, ha⟩ := quotient_surjective d T n U ((d.projection T n).hom.app U r)
  have hk : (d.projection T n).hom.app U (r - (exchangeScalar d T).hom.app U a) = 0 := by
    rw [map_sub, ← ha]
    exact sub_self _
  have hr : r • x = (exchangeScalar d T).hom.app U a • x +
      (r - (exchangeScalar d T).hom.app U a) • x := by
    rw [← add_smul, add_sub_cancel]
  rw [hr, hadd, hspan _ (projection_ker_le d T n U _ hk), add_zero, hlin, ← ha]

/-- The finite-level balancing isomorphism `(A/I^{n+1}) ⊗_A M ≅ (Â/I^{n+1}Â) ⊗_Â M`. -/
theorem ordinaryRhoLevel_exists (T : Scheme.{t}) (n : ℕ)
    (M : reductionModules T (d.completedRing T)) :
    ∃ i : (reductionChange T (quotient d T n)).obj
          ((reductionRestrict T (exchangeScalar d T)).obj M) ≅
        (reductionChange T (d.projection T n)).obj M,
      ∀ (U : T.ProEtᵒᵖ) (s : (d.finiteRing T n).obj.obj U) (x : M.val.obj U),
        i.hom.val.app U (reductionTensorSection T (quotient d T n)
          ((reductionRestrict T (exchangeScalar d T)).obj M) U s x) =
            reductionTensorSection T (d.projection T n) M U s x := by
  let N := (reductionRestrict T (exchangeScalar d T)).obj M
  let q := quotient d T n
  let p := d.projection T n
  let v : N ⟶ (reductionRestrict T q).obj ((reductionChange T p).obj M) :=
    (reductionRestrict T (exchangeScalar d T)).map (reductionUnit T p M)
  obtain ⟨F, hF⟩ := changeLift_exists T q N ((reductionChange T p).obj M) v
  let ua := (PresheafOfModules.toPresheaf (reductionModuleRing T
    (exchangeConstantRing T A)).obj).map (reductionUnit T q N).val
  let w : M ⟶ (reductionRestrict T p).obj ((reductionChange T q).obj N) :=
    ⟨PresheafOfModules.homMk ua (by
      intro U r x
      change (reductionUnit T q N).val.app U (r • x) =
        p.hom.app U r •
          (show ((reductionChange T q).obj N).val.obj U from
            (reductionUnit T q N).val.app U x)
      rw [reductionUnit_apply, reductionUnit_apply, tensorSection_smul, mul_one]
      exact quotientUnit_smul d T n M U r x)⟩
  obtain ⟨G, hG⟩ := changeLift_exists T p M ((reductionChange T q).obj N) w
  have hF' (U : T.ProEtᵒᵖ) (s : (d.finiteRing T n).obj.obj U) (x : M.val.obj U) :
      F.val.app U (reductionTensorSection T q N U s x) =
        reductionTensorSection T p M U s x := by
    rw [hF]
    erw [reductionUnit_apply]
    exact (tensorSection_smul T p M U s 1 x).trans (by rw [mul_one])
  have hG' (U : T.ProEtᵒᵖ) (s : (d.finiteRing T n).obj.obj U) (x : M.val.obj U) :
      G.val.app U (reductionTensorSection T p M U s x) =
        reductionTensorSection T q N U s x := by
    rw [hG]
    erw [reductionUnit_apply]
    exact (tensorSection_smul T q N U s 1 x).trans (by rw [mul_one])
  refine ⟨⟨F, G, ?_, ?_⟩, hF'⟩
  · apply change_hom_ext T q N
    intro U s x
    change G.val.app U (F.val.app U _) = _
    rw [hF', hG']
    rfl
  · apply change_hom_ext T p M
    intro U s x
    change F.val.app U (G.val.app U _) = _
    rw [hG', hF']
    rfl

/-- The chosen finite-level balancing isomorphism. -/
def ordinaryRhoLevel (T : Scheme.{t}) (n : ℕ) (M : reductionModules T (d.completedRing T)) :
    (reductionChange T (quotient d T n)).obj
          ((reductionRestrict T (exchangeScalar d T)).obj M) ≅
        (reductionChange T (d.projection T n)).obj M :=
  (ordinaryRhoLevel_exists d T n M).choose

theorem ordinaryRhoLevel_hom_apply (T : Scheme.{t}) (n : ℕ)
    (M : reductionModules T (d.completedRing T)) (U : T.ProEtᵒᵖ)
    (s : (d.finiteRing T n).obj.obj U) (x : M.val.obj U) :
    (ordinaryRhoLevel d T n M).hom.val.app U (reductionTensorSection T (quotient d T n)
      ((reductionRestrict T (exchangeScalar d T)).obj M) U s x) =
        reductionTensorSection T (d.projection T n) M U s x :=
  (ordinaryRhoLevel_exists d T n M).choose_spec U s x

/-- Existence of the normalized ordinary strict balancing comparison.
Source: Stacks 099M (blueprint: lem-weil-pbc-ordered-rho-existence).
The finite quotient tensor comparisons are assembled into a morphism of strict
towers; the section formula is preserved by the quotient transition maps and
the completed coefficient projections. -/
theorem ordinaryRho_exists (T : Scheme.{t}) :
    ∃ e : reductionRestrict T (exchangeScalar d T) ⋙ reductionModule d T ≅
        completedReductionModuleTowerFunctor T d ⋙ exchangeTowerModuleRes d T,
      ∀ (M : reductionModules T (d.completedRing T)) (n : ℕ) (U : T.ProEtᵒᵖ)
        (s : (d.finiteRing T n).obj.obj U) (x : M.val.obj U),
        ((e.hom.app M).app (op n)).val.app U
            (reductionTensorSection T (quotient d T n)
              ((reductionRestrict T (exchangeScalar d T)).obj M) U s x) =
          reductionTensorSection T (d.projection T n) M U s x := by
  let c := exchangeScalar d T
  let r (M : reductionModules T (d.completedRing T)) (n : ℕ) :
      ((reductionRestrict T c ⋙ reductionModule d T).obj M).obj (op n) ⟶
        ((completedReductionModuleTowerFunctor T d ⋙ exchangeTowerModuleRes d T).obj M).obj
          (op n) :=
    (reductionRestrict T (quotient d T n)).map (ordinaryRhoLevel d T n M).hom
  have hr (M : reductionModules T (d.completedRing T)) (n : ℕ) (U : T.ProEtᵒᵖ)
      (s : (d.finiteRing T n).obj.obj U) (x : M.val.obj U) :
      (r M n).val.app U (reductionTensorSection T (quotient d T n)
        ((reductionRestrict T c).obj M) U s x) =
          reductionTensorSection T (d.projection T n) M U s x :=
    ordinaryRhoLevel_hom_apply d T n M U s x
  let φ (M : reductionModules T (d.completedRing T)) :
      (reductionRestrict T c ⋙ reductionModule d T).obj M ⟶
        (completedReductionModuleTowerFunctor T d ⋙ exchangeTowerModuleRes d T).obj M :=
    NatTrans.ofOpSequence (fun n ↦ r M n) (by
      intro n
      have h1 : ((reductionRestrict T c ⋙ reductionModule d T).obj M).map
          (homOfLE (Nat.le_succ n)).op = (step d T n).app ((reductionRestrict T c).obj M) := by
        simp [reductionModule]
      have h2 : ((completedReductionModuleTowerFunctor T d ⋙ exchangeTowerModuleRes d T).obj
          M).map (homOfLE (Nat.le_succ n)).op = (proEtaleRingRestrictScalars c).map
            ((completedReductionTransition T d (n + 1) n (Nat.le_succ n)).app M) := by
        simp [completedReductionModuleTowerFunctor, completedReductionModuleTower]
        rfl
      rw [h1, h2]
      apply level_hom_ext T (quotient d T (n + 1)) ((reductionRestrict T c).obj M)
      intro U s x
      simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ConcreteCategory.comp_apply]
      change (r M n).val.app U (((step d T n).app ((reductionRestrict T c).obj M)).val.app U
          (reductionTensorSection T (quotient d T (n + 1))
            ((reductionRestrict T c).obj M) U s x)) =
        ((completedReductionTransition T d (n + 1) n (Nat.le_succ n)).app M).val.app U
          ((r M (n + 1)).val.app U (reductionTensorSection T (quotient d T (n + 1))
            ((reductionRestrict T c).obj M) U s x))
      have hs : ((step d T n).app ((reductionRestrict T c).obj M)).val.app U
          (reductionTensorSection T (quotient d T (n + 1)) ((reductionRestrict T c).obj M) U s x) =
            reductionTensorSection T (quotient d T n) ((reductionRestrict T c).obj M) U
              ((reductionCoefficientMap T d (n + 1) n (Nat.le_succ n)).hom.app U s) x :=
        (step_existsUnique d T n).exists.choose_spec _ U s x
      rw [hs, hr, hr]
      exact ((completedReductionTransition_exists T d (n + 1) n
        (Nat.le_succ n)).exists.choose_spec M U s x).symm)
  have hφ (M : reductionModules T (d.completedRing T)) : IsIso (φ M) := by
    have (n : ℕᵒᵖ) : IsIso ((φ M).app n) := by
      change IsIso ((reductionRestrict T (quotient d T n.unop)).map
        (ordinaryRhoLevel d T n.unop M).hom)
      infer_instance
    exact NatIso.isIso_of_isIso_app (φ M)
  refine ⟨NatIso.ofComponents (fun M ↦ asIso (φ M)) ?_, ?_⟩
  · intro M M' f
    apply NatTrans.ext
    funext n
    apply level_hom_ext T (quotient d T n.unop) ((reductionRestrict T c).obj M)
    intro U s x
    change (r M' n.unop).val.app U
        (((level d T n.unop).map ((reductionRestrict T c).map f)).val.app U
          (reductionTensorSection T (quotient d T n.unop)
            ((reductionRestrict T c).obj M) U s x)) =
        ((completedReductionLevel T d n.unop).map f).val.app U
          ((r M n.unop).val.app U (reductionTensorSection T (quotient d T n.unop)
            ((reductionRestrict T c).obj M) U s x))
    rw [tensorSection_map, hr, hr]
    exact (reductionTensor_map T (d.projection T n.unop) f U s x).symm
  · intro M n U s x
    exact hr M n U s x


/-- Uniqueness of the normalized ordinary strict balancing comparison.
Source: Stacks 099M (blueprint: lem-weil-pbc-ordered-rho-uniqueness).
The quotient tensor sections generate each finite reduction, so two tower
isomorphisms satisfying the displayed section formula agree at every level and
therefore agree as natural transformations. -/
theorem ordinaryRho_unique (T : Scheme.{t})
    {e₁ e₂ : reductionRestrict T (exchangeScalar d T) ⋙ reductionModule d T ≅
        completedReductionModuleTowerFunctor T d ⋙ exchangeTowerModuleRes d T}
    (h₁ : ∀ (M : reductionModules T (d.completedRing T)) (n : ℕ) (U : T.ProEtᵒᵖ)
      (s : (d.finiteRing T n).obj.obj U) (x : M.val.obj U),
      ((e₁.hom.app M).app (op n)).val.app U
          (reductionTensorSection T (quotient d T n)
            ((reductionRestrict T (exchangeScalar d T)).obj M) U s x) =
        reductionTensorSection T (d.projection T n) M U s x)
    (h₂ : ∀ (M : reductionModules T (d.completedRing T)) (n : ℕ) (U : T.ProEtᵒᵖ)
      (s : (d.finiteRing T n).obj.obj U) (x : M.val.obj U),
      ((e₂.hom.app M).app (op n)).val.app U
          (reductionTensorSection T (quotient d T n)
            ((reductionRestrict T (exchangeScalar d T)).obj M) U s x) =
        reductionTensorSection T (d.projection T n) M U s x) :
    e₁ = e₂ := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply NatTrans.ext
  funext n
  apply level_hom_ext T (quotient d T n.unop)
    ((reductionRestrict T (exchangeScalar d T)).obj M)
  intro U s x
  exact (h₁ M n.unop U s x).trans (h₂ M n.unop U s x).symm

/-- Derived restriction along the existing compatible-residue coefficient map.
Source: Stacks 099M (blueprint: def-weil-pbc-ordered-coefficient-comparison-data). -/
abbrev res (T : Scheme.{t}) := reductionDerivedRestrict T (exchangeScalar d T)

/-- The canonical balancing isomorphism on the single ordinary strict quotient diagram.
Source: Stacks 099M (blueprint: def-weil-pbc-ordered-coefficient-comparison-data).
Proof: flatness of the completed ring over the constant ring identifies its finite
quotients with the specified finite constant sheaves. On pure tensors the comparison
sends s tensor x to s tensor x. Balancing and sheafification make this an isomorphism,
natural in modules and quotient coefficients. The section formulas specify it uniquely
and ensure compatibility with all quotient transitions, including identity transitions. -/
theorem ordinaryRho_existsUnique (T : Scheme.{t}) :
    ∃! e : reductionRestrict T (exchangeScalar d T) ⋙ reductionModule d T ≅
        completedReductionModuleTowerFunctor T d ⋙ exchangeTowerModuleRes d T,
      ∀ (M : reductionModules T (d.completedRing T)) (n : ℕ) (U : T.ProEtᵒᵖ)
        (s : (d.finiteRing T n).obj.obj U) (x : M.val.obj U),
        ((e.hom.app M).app (op n)).val.app U
            (reductionTensorSection T (quotient d T n)
              ((reductionRestrict T (exchangeScalar d T)).obj M) U s x) =
          reductionTensorSection T (d.projection T n) M U s x := by
  obtain ⟨e, he⟩ := ordinaryRho_exists d T
  refine ⟨e, he, ?_⟩
  intro e' he'
  exact (ordinaryRho_unique d T he he').symm

/-- Ordinary strict balancing, with its prescribed tensor normalization.
Source: Stacks 099M (blueprint: def-weil-pbc-ordered-coefficient-comparison-data). -/
def ordinaryRho (T : Scheme.{t}) :
    reductionRestrict T (exchangeScalar d T) ⋙ reductionModule d T ≅
      completedReductionModuleTowerFunctor T d ⋙ exchangeTowerModuleRes d T :=
  (ordinaryRho_existsUnique d T).exists.choose

attribute [local irreducible] ordinaryRho reductionModule completedReductionModuleTowerFunctor
  completedReductionCoefficient constantSheaf AdicCoefficients.coefficientRing
  SheafOfModules.monoidalCategory

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The complex-level normalization of the specified rho comparison.
Source: Stacks 099M, 06YY
(blueprint: def-weil-pbc-ordered-coefficient-comparison-data). -/
def RhoNormalization (T : Scheme.{t})
    (e : completedReductionTower T d ⋙ exchangeTowerRes d T ≅
        res d T ⋙ reduction d T) : Prop :=
  ∀ P : CochainComplex (reductionModules T (d.completedRing T)) ℤ,
        CochainComplex.IsKFlatIndependentCoefficients.{t + 1, t, t + 1}
          (R := d.completedRing T) P →
        (∀ n : ℤ, SheafOfModules.IsFlatOnSite.{t + 1, t, t + 1, t + 1}
          (R := d.completedRing T) (P.X n)) →
        e.hom.app (DerivedCategory.Q.obj P) ≫
            (reduction d T).map
              ((reductionRestrict T (exchangeScalar d T)).mapDerivedCategoryFactors.hom.app P) ≫
            reductionComplexCounit d T
              (((reductionRestrict T (exchangeScalar d T)).mapHomologicalComplex (.up ℤ)).obj P) =
          (exchangeTowerRes d T).map (completedReductionTowerComplexCounit T d P) ≫
            (exchangeTowerModuleRes d T).mapDerivedCategoryFactors.hom.app
              ((completedReductionComplexTowerFunctor T d).obj P) ≫
            DerivedCategory.Q.map
              ((NatIso.mapHomologicalComplex (ordinaryRho d T).symm (.up ℤ)).hom.app P)

attribute [local irreducible] RhoNormalization

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The derived strict-tower comparison is fixed on K-flat representatives before evaluation.
Source: Stacks 099M, 06YY
(blueprint: def-weil-pbc-ordered-coefficient-comparison-data).
Proof: flatness makes restriction preserve flat-term K-flat representatives. Apply
ordinaryRho to one such representative and conjugate by the two universal reduction
counits and exact-restriction factorization maps. The formula descends through resolving
quasi-isomorphisms, giving the isomorphism. Every derived object has a representative
of this kind, so the formula determines the natural isomorphism uniquely. -/
theorem rho_exists_core (T : Scheme.{t}) :
    ∃ e : completedReductionTower T d ⋙ exchangeTowerRes d T ≅
        res d T ⋙ reduction d T, RhoNormalization d T e := by
  sorry

theorem rho_unique_core (T : Scheme.{t})
    {e₁ e₂ : completedReductionTower T d ⋙ exchangeTowerRes d T ≅
        res d T ⋙ reduction d T}
    (h₁ : RhoNormalization d T e₁) (h₂ : RhoNormalization d T e₂) : e₁ = e₂ := by
  have hflat := orderedScalarFlat d T
  apply Iso.ext
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso (reductionModules T (d.completedRing T)) (.up ℤ))
  intro P
  obtain ⟨L, f, ⟨hL, hLf⟩, hf⟩ := flatKFlatResolution T (d.completedRing T) P
  have := hf
  apply (cancel_epi
    ((completedReductionTower T d ⋙ exchangeTowerRes d T).map
      (DerivedCategory.Q.map f))).mp
  rw [e₁.hom.naturality, e₂.hom.naturality]
  suffices e₁.hom.app (DerivedCategory.Q.obj L) =
      e₂.hom.app (DerivedCategory.Q.obj L) by rw [this]
  have hr := SheafOfModules.isKFlat_restrictScalars_of_flat
    (exchangeScalar d T) hflat L hL
  have hi := (reductionData d T).complexCounit_isIso
    (((reductionRestrict T (exchangeScalar d T)).mapHomologicalComplex (.up ℤ)).obj L) hr.1
  have hi' : IsIso (reductionComplexCounit d T
      (((reductionRestrict T (exchangeScalar d T)).mapHomologicalComplex (.up ℤ)).obj L)) := by
    simpa only [reductionComplexCounit, reduction] using hi
  apply (cancel_mono
    ((reduction d T).map
      ((reductionRestrict T (exchangeScalar d T)).mapDerivedCategoryFactors.hom.app L) ≫
      reductionComplexCounit d T
        (((reductionRestrict T (exchangeScalar d T)).mapHomologicalComplex (.up ℤ)).obj L))).mp
  unfold RhoNormalization at h₁ h₂
  exact (h₁ L hL hLf).trans (h₂ L hL hLf).symm

theorem rho_exists (T : Scheme.{t}) :
    ∃ e : completedReductionTower T d ⋙ exchangeTowerRes d T ≅
        res d T ⋙ reduction d T, RhoNormalization d T e := by
  exact rho_exists_core d T

theorem rho_unique (T : Scheme.{t})
    {e₁ e₂ : completedReductionTower T d ⋙ exchangeTowerRes d T ≅
        res d T ⋙ reduction d T}
    (h₁ : RhoNormalization d T e₁) (h₂ : RhoNormalization d T e₂) : e₁ = e₂ := by
  exact rho_unique_core d T h₁ h₂

theorem rho_existsUnique (T : Scheme.{t}) :
    ∃! e : completedReductionTower T d ⋙ exchangeTowerRes d T ≅
        res d T ⋙ reduction d T,
      RhoNormalization d T e := by
  obtain ⟨e, he⟩ := rho_exists d T
  refine ⟨e, he, ?_⟩
  intro e' he'
  exact (rho_unique d T he he').symm

/-- The specified comparison rho, natural on all ambient inputs.
Source: Stacks 099M (blueprint: def-weil-pbc-ordered-coefficient-comparison-data). -/
def rho (T : Scheme.{t}) :
    completedReductionTower T d ⋙ exchangeTowerRes d T ≅ res d T ⋙ reduction d T :=
  (rho_existsUnique d T).exists.choose

/-- The actual ordinary limit/scalar comparison, fixed by all its projections.
Source: Stacks 0A07 (blueprint: def-weil-pbc-ordered-coefficient-comparison-data).
Proof: restriction leaves the underlying additive sheaf unchanged. Its right-adjoint
limit comparison is the identity on compatible families. Every projection commutes
with it, giving its inverse and uniqueness by the limit universal property. -/
theorem ordinaryLambda_existsUnique (T : Scheme.{t}) :
    ∃! e : completedTowerLimit T (d.completedRing T) ⋙
          reductionRestrict T (exchangeScalar d T) ≅
        exchangeTowerModuleRes d T ⋙ completedTowerLimit T (exchangeConstantRing T A),
      ∀ (Z : d.towers T) (n : ℕ),
        e.hom.app Z ≫ limit.π ((exchangeTowerModuleRes d T).obj Z) (op n) =
          (reductionRestrict T (exchangeScalar d T)).map (limit.π Z (op n)) := by
  let := orderedAbSheafify T
  let := orderedAbLocallyBijective T
  have := orderedRestrictLimits T (exchangeScalar d T)
  exact uniqueLimitComparison (reductionRestrict T (exchangeScalar d T))

/-- The identity on compatible families, with its projection equations retained.
Source: Stacks 0A07 (blueprint: def-weil-pbc-ordered-coefficient-comparison-data). -/
def ordinaryLambda (T : Scheme.{t}) :
    completedTowerLimit T (d.completedRing T) ⋙ reductionRestrict T (exchangeScalar d T) ≅
      exchangeTowerModuleRes d T ⋙ completedTowerLimit T (exchangeConstantRing T A) :=
  (ordinaryLambda_existsUnique d T).exists.choose

attribute [local irreducible] ordinaryLambda Functor.rightDerivedFunctor
  Functor.rightDerivedFunctorUnit

/-- The universal right-derived limit unit at a cochain complex.
Source: Stacks 0A07 (blueprint: def-weil-pbc-ordered-coefficient-comparison-data). -/
def limitComplexUnit (T : Scheme.{t})
    (R : Sheaf (ProEt.topology T) CommRingCat.{t + 1})
    (P : CochainComplex (exchangeTowers T R) ℤ) :
    DerivedCategory.Q.obj
        (((completedTowerLimit T R).mapHomologicalComplex (.up ℤ)).obj P) ⟶
      (completedRlim T R).obj (DerivedCategory.Q.obj P) :=
  (DerivedCategory.quotientCompQhIso _).inv.app
      (((completedTowerLimit T R).mapHomologicalComplex (.up ℤ)).obj P) ≫
    DerivedCategory.Qh.map
      (((completedTowerLimit T R).mapHomotopyCategoryFactors (.up ℤ)).inv.app P) ≫
    (completedTowerLimit T R).rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ _).obj P) ≫
    (completedRlim T R).map ((DerivedCategory.quotientCompQhIso _).hom.app P)

attribute [local irreducible] limitComplexUnit

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The complex-level normalization of the specified lambda comparison.
Source: Stacks 0A07
(blueprint: def-weil-pbc-ordered-coefficient-comparison-data). -/
def LambdaNormalization (T : Scheme.{t})
    (e : completedRlim T (d.completedRing T) ⋙ res d T ≅
        exchangeTowerRes d T ⋙ rlim (A := A) T) : Prop :=
  ∀ P : CochainComplex (d.towers T) ℤ,
        (res d T).map (limitComplexUnit T (d.completedRing T) P) ≫
            e.hom.app (DerivedCategory.Q.obj P) ≫
            (rlim (A := A) T).map
              ((exchangeTowerModuleRes d T).mapDerivedCategoryFactors.hom.app P) =
          (reductionRestrict T (exchangeScalar d T)).mapDerivedCategoryFactors.hom.app
              (((completedTowerLimit T (d.completedRing T)).mapHomologicalComplex (.up ℤ)).obj P) ≫
            DerivedCategory.Q.map
              ((NatIso.mapHomologicalComplex (ordinaryLambda d T) (.up ℤ)).hom.app P) ≫
            limitComplexUnit T (exchangeConstantRing T A)
              (((exchangeTowerModuleRes d T).mapHomologicalComplex (.up ℤ)).obj P)

attribute [local irreducible] LambdaNormalization

attribute [local irreducible] SheafOfModules.fullyFaithfulForget
  SheafOfModules.instAddCommGroupHom

private def orderedDerivedComplexUnit
    {C E : Type*} [Category C] [Category E] [Abelian C] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory E]
    [Abelian.HasKInjectiveResolutions C] (F : C ⥤ E) [F.Additive] :
    F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ F.rightDerivedFunctor :=
  Functor.whiskerLeft (F.mapHomologicalComplex (.up ℤ))
      (DerivedCategory.quotientCompQhIso E).inv ≫
    Functor.whiskerRight (F.mapHomotopyCategoryFactors (.up ℤ)).inv DerivedCategory.Qh ≫
    Functor.whiskerLeft (HomotopyCategory.quotient C (.up ℤ)) F.rightDerivedFunctorUnit ≫
    Functor.whiskerRight (DerivedCategory.quotientCompQhIso C).hom F.rightDerivedFunctor

private theorem orderedDerivedComplexUnit_isIso
    {C E : Type*} [Category C] [Category E] [Abelian C] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory E]
    [Abelian.HasKInjectiveResolutions C] (F : C ⥤ E) [F.Additive]
    (P : CochainComplex C ℤ) [P.IsKInjective] :
    IsIso ((orderedDerivedComplexUnit F).app P) := by
  dsimp only [orderedDerivedComplexUnit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app]
  infer_instance

private theorem orderedScalarComparison
    {C E C' E' : Type*}
    [Category C] [Category E] [Category C'] [Category E']
    [Abelian C] [Abelian E] [Abelian C'] [Abelian E']
    [HasDerivedCategory C] [HasDerivedCategory E]
    [HasDerivedCategory C'] [HasDerivedCategory E']
    [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions C']
    (F : C ⥤ E) (F' : C' ⥤ E') (r : C' ⥤ C) (s : E' ⥤ E)
    [F.Additive] [F'.Additive] [r.Additive] [s.Additive]
    [PreservesFiniteLimits r] [PreservesFiniteColimits r]
    [PreservesFiniteLimits s] [PreservesFiniteColimits s]
    [r.PreservesKInjectiveComplexes] (c : F' ⋙ s ≅ r ⋙ F) :
    ∃! e : F'.rightDerivedFunctor ⋙ s.mapDerivedCategory ≅
        r.mapDerivedCategory ⋙ F.rightDerivedFunctor,
      ∀ P : CochainComplex C' ℤ,
        s.mapDerivedCategory.map ((orderedDerivedComplexUnit F').app P) ≫
          e.hom.app (DerivedCategory.Q.obj P) ≫
          F.rightDerivedFunctor.map (r.mapDerivedCategoryFactors.hom.app P) =
        s.mapDerivedCategoryFactors.hom.app
            ((F'.mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex c (.up ℤ)).hom.app P) ≫
          (orderedDerivedComplexUnit F).app
            ((r.mapHomologicalComplex (.up ℤ)).obj P) := by
  let a : (F' ⋙ s).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ (F'.rightDerivedFunctor ⋙ s.mapDerivedCategory) :=
    Functor.whiskerLeft (F'.mapHomologicalComplex (.up ℤ))
        s.mapDerivedCategoryFactors.inv ≫
      Functor.whiskerRight (orderedDerivedComplexUnit F') s.mapDerivedCategory
  let b : (F' ⋙ s).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ (r.mapDerivedCategory ⋙ F.rightDerivedFunctor) :=
    Functor.whiskerRight (NatIso.mapHomologicalComplex c (.up ℤ)).hom DerivedCategory.Q ≫
      Functor.whiskerLeft (r.mapHomologicalComplex (.up ℤ)) (orderedDerivedComplexUnit F) ≫
      Functor.whiskerRight r.mapDerivedCategoryFactors.inv F.rightDerivedFunctor
  obtain ⟨e, he⟩ := CategoryTheory.FlatScalarTowerLimit.normalized_iso _ _ _ a b
    (by
      intro P hP
      have := hP
      have := orderedDerivedComplexUnit_isIso F' P
      dsimp only [a, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
      infer_instance)
    (by
      intro P hP
      have := hP
      have := orderedDerivedComplexUnit_isIso F
        ((r.mapHomologicalComplex (.up ℤ)).obj P)
      dsimp only [b, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
      infer_instance)
  have hn (P : CochainComplex C' ℤ) := he P
  dsimp only [a, b, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app] at hn
  have hn' (P : CochainComplex C' ℤ) :
      s.mapDerivedCategory.map ((orderedDerivedComplexUnit F').app P) ≫
        e.hom.app (DerivedCategory.Q.obj P) ≫
        F.rightDerivedFunctor.map (r.mapDerivedCategoryFactors.hom.app P) =
      s.mapDerivedCategoryFactors.hom.app
          ((F'.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex c (.up ℤ)).hom.app P) ≫
        (orderedDerivedComplexUnit F).app
          ((r.mapHomologicalComplex (.up ℤ)).obj P) := by
    apply (cancel_epi (s.mapDerivedCategoryFactors.inv.app _)).mp
    simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
    have h := congrArg
      (fun k ↦ k ≫ F.rightDerivedFunctor.map (r.mapDerivedCategoryFactors.hom.app P)) (hn P)
    simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app] at h
    erw [F.rightDerivedFunctor.map_id, Category.comp_id] at h
    simp only [Category.assoc]
    exact h
  refine ⟨e, hn', ?_⟩
  intro e' he'
  apply Iso.ext
  apply CategoryTheory.FlatScalarTowerLimit.derived_ext
  intro P hP
  have := hP
  have := orderedDerivedComplexUnit_isIso F' P
  apply (cancel_epi (s.mapDerivedCategory.map ((orderedDerivedComplexUnit F').app P))).mp
  apply (cancel_mono (F.rightDerivedFunctor.map (r.mapDerivedCategoryFactors.hom.app P))).mp
  simpa only [Category.assoc] using (he' P).trans (hn' P).symm

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Restriction commutes with derived strict limit on arbitrary towers, with the
K-injective comparison fixed by its ordinary compatible-family map and universal units.
Source: Stacks 0A07 (blueprint: def-weil-pbc-ordered-coefficient-comparison-data).
Proof: flat scalar extension is an exact left adjoint to restriction. Termwise
restriction therefore preserves K-injectives on the small diagram site. On a
K-injective tower, apply ordinaryLambda and the invertible derived units. This
defines a natural isomorphism. Universality extends its equation to every complex;
K-injective resolutions prove uniqueness. No finite-reduction condition is used. -/
theorem lambda_existsUnique (T : Scheme.{t}) :
    ∃! e : completedRlim T (d.completedRing T) ⋙ res d T ≅
        exchangeTowerRes d T ⋙ rlim (A := A) T,
      LambdaNormalization d T e := by
  have := exchangeTowerModuleRes_kinjective d T
  have h := orderedScalarComparison
    (completedTowerLimit T (exchangeConstantRing T A))
    (completedTowerLimit T (d.completedRing T))
    (exchangeTowerModuleRes d T) (reductionRestrict T (exchangeScalar d T))
    (ordinaryLambda d T)
  unfold LambdaNormalization
  simpa only [orderedDerivedComplexUnit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, limitComplexUnit] using h

/-- The canonical restriction/derived-limit comparison on actual strict towers.
Source: Stacks 0A07 (blueprint: def-weil-pbc-ordered-coefficient-comparison-data). -/
def lambda (T : Scheme.{t}) :
    completedRlim T (d.completedRing T) ⋙ res d T ≅ exchangeTowerRes d T ⋙ rlim (A := A) T :=
  (lambda_existsUnique d T).exists.choose

/-- Ordinary scalar restriction commutes with constant diagrams by identity components.
Source: Stacks 0E48 (blueprint: def-weil-pbc-ordered-coefficient-comparison-data). -/
def ordinaryScalarDiagonal (T : Scheme.{t}) :
    d.constantTower T ⋙ exchangeTowerModuleRes d T ≅
      reductionRestrict T (exchangeScalar d T) ⋙ (Functor.const ℕᵒᵖ) :=
  NatIso.ofComponents
    (fun _ ↦ NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ by simp))
    (fun _ ↦ by ext n; simp)

/-- Exact descent of the identity scalar/diagonal comparison.
Source: Stacks 0E48 (blueprint: def-weil-pbc-ordered-coefficient-comparison-data). -/
def scalarDiagonal (T : Scheme.{t}) :
    d.derivedConstantTower T ⋙ exchangeTowerRes d T ≅ res d T ⋙ diagonal (A := A) T :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (ordinaryScalarDiagonal d T) ≪≫
      Functor.mapDerivedCategoryCompIso _ _

set_option linter.flexible false in
private theorem ordinaryLambda_unit (T : Scheme.{t})
    (N : reductionModules T (d.completedRing T)) :
    (reductionRestrict T (exchangeScalar d T)).map
        ((constLimAdj : (Functor.const ℕᵒᵖ) ⊣
          completedTowerLimit T (d.completedRing T)).unit.app N) ≫
      (ordinaryLambda d T).hom.app ((Functor.const ℕᵒᵖ).obj N) =
    (constLimAdj : (Functor.const ℕᵒᵖ) ⊣
        completedTowerLimit T (exchangeConstantRing T A)).unit.app
        ((reductionRestrict T (exchangeScalar d T)).obj N) ≫
      (completedTowerLimit T (exchangeConstantRing T A)).map
        ((ordinaryScalarDiagonal d T).symm.hom.app N) := by
  apply limit.hom_ext
  intro n
  have hl : (ordinaryLambda d T).hom.app ((Functor.const ℕᵒᵖ).obj N) ≫
      limit.π ((exchangeTowerModuleRes d T).obj ((Functor.const ℕᵒᵖ).obj N)) n =
      (reductionRestrict T (exchangeScalar d T)).map (limit.π ((Functor.const ℕᵒᵖ).obj N) n) := by
    unfold ordinaryLambda
    exact (ordinaryLambda_existsUnique d T).exists.choose_spec ((Functor.const ℕᵒᵖ).obj N) n.unop
  simp only [Category.assoc]
  erw [hl]
  simp [constLimAdj, ordinaryScalarDiagonal]
  rw [← Functor.map_comp, limit.lift_π]
  exact (reductionRestrict T (exchangeScalar d T)).map_id N


private theorem factorsh_hom_quotient {B E : Type*} [Category B] [Category E]
    [Abelian B] [Abelian E] [HasDerivedCategory B] [HasDerivedCategory E]
    (F : B ⥤ E) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (K : CochainComplex B ℤ) :
    F.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.quotient _ _).obj K) =
      F.mapDerivedCategoryFactors.hom.app K := by
  rw [Functor.mapDerivedCategoryFactorsh_hom_app]
  have h1 : (DerivedCategory.quotientCompQhIso B).hom.app K = 𝟙 _ := rfl
  have h2 : (DerivedCategory.quotientCompQhIso E).inv.app
      ((F.mapHomologicalComplex (.up ℤ)).obj K) = 𝟙 _ := rfl
  have h3 : (F.mapHomotopyCategoryFactors (.up ℤ)).inv.app K = 𝟙 _ := rfl
  rw [h1, h2, h3]
  simp

private theorem factorsh_inv_quotient {B E : Type*} [Category B] [Category E]
    [Abelian B] [Abelian E] [HasDerivedCategory B] [HasDerivedCategory E]
    (F : B ⥤ E) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (K : CochainComplex B ℤ) :
    F.mapDerivedCategoryFactorsh.inv.app ((HomotopyCategory.quotient _ _).obj K) =
      F.mapDerivedCategoryFactors.inv.app K := by
  have h := factorsh_hom_quotient F K
  apply (cancel_epi (F.mapDerivedCategoryFactorsh.hom.app
    ((HomotopyCategory.quotient _ _).obj K))).mp
  rw [Iso.hom_inv_id_app]
  erw [h, Iso.hom_inv_id_app]
  rfl

private theorem limitComplexUnit_eq (T : Scheme.{t})
    (R : Sheaf (ProEt.topology T) CommRingCat.{t + 1})
    (P : CochainComplex (exchangeTowers T R) ℤ) :
    limitComplexUnit T R P =
      (completedTowerLimit T R).rightDerivedFunctorUnit.app
        ((HomotopyCategory.quotient _ _).obj P) := by
  unfold limitComplexUnit
  have h1 : (DerivedCategory.quotientCompQhIso (reductionModules T R)).inv.app
      (((completedTowerLimit T R).mapHomologicalComplex (.up ℤ)).obj P) = 𝟙 _ := rfl
  have h2 : ((completedTowerLimit T R).mapHomotopyCategoryFactors (.up ℤ)).inv.app P =
      𝟙 _ := rfl
  have h3 : (DerivedCategory.quotientCompQhIso (exchangeTowers T R)).hom.app P = 𝟙 _ := rfl
  rw [h1, h2, h3]
  simp


private theorem towerRes_unit_isIso (T : Scheme.{t}) :
    ∀ (K : CochainComplex (d.towers T) ℤ) [K.IsKInjective],
      IsIso ((completedTowerLimit T (exchangeConstantRing T A)).rightDerivedFunctorUnit.app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj
          (((exchangeTowerModuleRes d T).mapHomologicalComplex (.up ℤ)).obj K))) := by
  have := exchangeTowerModuleRes_kinjective d T
  intro K _
  infer_instance

/-- The comparison of derived limits induced by the ordinary limit comparison. -/
private def lambdaIso (T : Scheme.{t}) :
    exchangeTowerRes d T ⋙ rlim (A := A) T ≅
      completedRlim T (d.completedRing T) ⋙ res d T :=
  (Functor.mapDerivedCategoryCompRightDerivedFunctorIsoOfIsIso (exchangeTowerModuleRes d T)
      (completedTowerLimit T (exchangeConstantRing T A)) (towerRes_unit_isIso d T)).symm ≪≫
    Functor.rightDerivedFunctorNatIso (ordinaryLambda d T).symm ≪≫
    Functor.rightDerivedFunctorCompMapDerivedCategoryIso (completedTowerLimit T (d.completedRing T))
      (reductionRestrict T (exchangeScalar d T))

private theorem lambdaIso_normalization (T : Scheme.{t}) :
    LambdaNormalization d T (lambdaIso d T).symm := by
  unfold LambdaNormalization
  intro P
  have hR := Functor.map_rightDerivedFunctorUnit_app_comp_restrictIso_inv_app
    (P₁ := reductionRestrict T (exchangeScalar d T)) (P₂ := exchangeTowerModuleRes d T)
    (F := completedTowerLimit T (exchangeConstantRing T A))
    (F' := completedTowerLimit T (d.completedRing T))
    (ordinaryLambda d T) (towerRes_unit_isIso d T) ((HomotopyCategory.quotient _ _).obj P)
  rw [limitComplexUnit_eq, limitComplexUnit_eq]
  simp only [Iso.symm_hom]
  rw [NatTrans.mapHomotopyCategorySquare_app_quotient_obj] at hR
  erw [factorsh_hom_quotient, factorsh_inv_quotient] at hR
  have hR' := congrArg (fun z ↦ z ≫ (rlim (A := A) T).map
    ((exchangeTowerModuleRes d T).mapDerivedCategoryFactors.hom.app P)) hR
  simp only [Category.assoc] at hR'
  erw [hR']
  rw [← Functor.map_comp, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]
  rfl


private theorem lambda_eq_lambdaIso (T : Scheme.{t}) : lambda d T = (lambdaIso d T).symm :=
  (lambda_existsUnique d T).unique (lambda_existsUnique d T).exists.choose_spec
    (lambdaIso_normalization d T)

private theorem lambda_mate (T : Scheme.{t}) :
    mateEquiv (d.constantRlimAdjunction T) (diagonalAdjunction (A := A) T)
        (Functor.mapDerivedCategorySquareIso (ordinaryScalarDiagonal d T).symm).hom =
      (lambda d T).hom := by
  rw [lambda_eq_lambdaIso]
  exact Adjunction.mateEquiv_mapDerivedCategoryRightDerivedAdjunction_restrict
    (constLimAdj : (Functor.const ℕᵒᵖ) ⊣ completedTowerLimit T (exchangeConstantRing T A))
    (constLimAdj : (Functor.const ℕᵒᵖ) ⊣ completedTowerLimit T (d.completedRing T))
    (ordinaryScalarDiagonal d T).symm (ordinaryLambda d T) (ordinaryLambda_unit d T)
    (towerRes_unit_isIso d T)

/-- Restriction carries the completed constant-tower adjunction unit to the constant one. -/
private theorem lambda_unit (T : Scheme.{t}) (K : d.derived T) :
    (res d T).map ((d.constantRlimAdjunction T).unit.app K) ≫
        (lambda d T).hom.app ((d.derivedConstantTower T).obj K) ≫
        (rlim (A := A) T).map ((scalarDiagonal d T).hom.app K) =
      (diagonalAdjunction (A := A) T).unit.app ((res d T).obj K) := by
  rw [← lambda_mate]
  have h := unit_mateEquiv (d.constantRlimAdjunction T) (diagonalAdjunction (A := A) T)
    (Functor.mapDerivedCategorySquareIso (ordinaryScalarDiagonal d T).symm).hom K
  rw [← Category.assoc]
  erw [h]
  rw [Category.assoc, ← Functor.map_comp]
  have hs : (Functor.mapDerivedCategorySquareIso (ordinaryScalarDiagonal d T).symm).hom.app K ≫
      (scalarDiagonal d T).hom.app K = 𝟙 _ := by
    have hsy := Functor.mapDerivedCategoryNatIso_symm (ordinaryScalarDiagonal d T)
    simp only [Functor.mapDerivedCategorySquareIso, scalarDiagonal, Iso.trans_hom, Iso.symm_hom,
      NatTrans.comp_app, Category.assoc, Iso.hom_inv_id_app_assoc]
    rw [hsy]
    simp
  erw [hs, CategoryTheory.Functor.map_id, Category.comp_id]
  rfl


/-- Restriction respects the strict quotient unit, not just its evaluations.
Source: Stacks 099M (blueprint: def-weil-pbc-ordered-coefficient-comparison-data).
Proof: on an ordinary flat-term K-flat model both augmentations send x to 1 tensor x
in the same strict quotient diagram. ordinaryRho preserves this formula. Descent by
the universal counits gives the first equality before derived limit. Apply lambda,
its diagonal normalization and the diagonal adjunction unit to obtain the second. -/
theorem rho_unit_first (T : Scheme.{t}) (K : d.derived T) :
    (exchangeTowerRes d T).map ((completedReductionAugmentation d T).app K) ≫
        (rho d T).hom.app K =
      (scalarDiagonal d T).hom.app K ≫ (augmentation d T).app ((res d T).obj K) := by
  sorry

/-- The normalized strict-tower comparison preserves the actual completion units.
Source: Stacks Tags 099M, 0941 and 0A07
(blueprint: lem-weil-pbc-ordered-rho-unit-second).
Proof: write the two completion units as the diagonal/limit adjunction unit followed
by derived limit of the quotient augmentation. The normalized limit/scalar comparison
is the mate of the identity comparison on constant diagrams, so it preserves the
adjunction units, with inverse scalarDiagonal on the constant side. Naturality of
lambda moves the completed quotient augmentation through it. The first rho unit
identity then replaces the restricted augmentation followed by rho by scalarDiagonal
followed by the constant augmentation. Derived limit of scalarDiagonal cancels its
inverse, leaving exactly the constant completion unit. -/
theorem rho_unit_second (T : Scheme.{t}) (K : d.derived T) :
    (res d T).map (d.completionUnit T K) ≫
        (lambda d T).hom.app ((completedReductionTower T d).obj K) ≫
        (rlim (A := A) T).map ((rho d T).hom.app K) =
      (unit d T).app ((res d T).obj K) := by
  have hn := (lambda d T).hom.naturality ((completedReductionAugmentation d T).app K)
  have h1 := rho_unit_first d T K
  have h2 := lambda_unit d T K
  simp only [Functor.comp_map] at hn
  have key : (res d T).map ((d.constantRlimAdjunction T).unit.app K) ≫
      (res d T).map ((completedRlim T (d.completedRing T)).map
        ((completedReductionAugmentation d T).app K)) ≫
      (lambda d T).hom.app ((completedReductionTower T d).obj K) ≫
      (rlim (A := A) T).map ((rho d T).hom.app K) =
      (diagonalAdjunction (A := A) T).unit.app ((res d T).obj K) ≫
        (rlim (A := A) T).map ((augmentation d T).app ((res d T).obj K)) := by
    rw [reassoc_of% hn, ← Functor.map_comp, h1, Functor.map_comp, ← h2]
    simp only [Category.assoc]
  unfold AdicCoefficientDatum.completionUnit
  erw [Functor.map_comp, Category.assoc]
  exact key

theorem rho_unit (T : Scheme.{t}) (K : d.derived T) :
    (exchangeTowerRes d T).map ((completedReductionAugmentation d T).app K) ≫
        (rho d T).hom.app K =
      (scalarDiagonal d T).hom.app K ≫ (augmentation d T).app ((res d T).obj K) ∧
    (res d T).map (d.completionUnit T K) ≫
        (lambda d T).hom.app ((completedReductionTower T d).obj K) ≫
        (rlim (A := A) T).map ((rho d T).hom.app K) =
      (unit d T).app ((res d T).obj K) := by
  exact ⟨rho_unit_first d T K, rho_unit_second d T K⟩

variable {U V : Scheme.{t}} (u : U ⟶ V)

/-- The ambient direct-image/scalar comparison, with its universal unit normalization.
Source: Stacks 0E48 (blueprint: def-weil-pbc-ordered-coefficient-comparison-data). -/
def chi : d.push u ⋙ res d V ≅ res d U ⋙ push (A := A) u :=
  proEtaleRingRestrictionDerivedDirectImage u
    (exchangeConstantRing V A) (d.completedRing V)
    (exchangeConstantRing U A) (d.completedRing U)
    (exchangeScalar d V) (exchangeScalar d U) (exchangeConstantIso u A)
    (d.integralRingIso u) (exchangeScalar_comm d u)

/-- The ambient pullback/scalar comparison is exact descent of the ordinary normalized mate.
Source: Stacks 0D6D (blueprint: def-weil-pbc-ordered-coefficient-comparison-data). -/
def alpha : d.pull u ⋙ res d U ≅ res d V ⋙ pull (A := A) u :=
  proEtaleRingRestrictionDerivedPullback u
    (exchangeConstantRing V A) (d.completedRing V)
    (exchangeConstantRing U A) (d.completedRing U)
    (exchangeScalar d V) (exchangeScalar d U) (exchangeConstantIso u A)
    (d.integralRingIso u) (exchangeScalar_comm d u)

/-- The quotient-tower complete category over completed coefficients.
Source: Stacks 099M (blueprint: def-weil-pbc-ordered-coefficient-comparison-data). -/
abbrev AComplete (T : Scheme.{t}) := ObjectProperty.FullSubcategory (d.TowerComplete T)

/-- The inclusion of the full completed-coefficient complete category.
Source: Stacks 099M (blueprint: def-weil-pbc-ordered-coefficient-comparison-data). -/
abbrev inclusion (T : Scheme.{t}) := ObjectProperty.ι (d.TowerComplete T)

/-- Restriction identifies the two complete predicates and is an equivalence on the full
complete categories; it does not assert an ambient equivalence.
Source: Stacks 099M, 099I
(blueprint: def-weil-pbc-ordered-coefficient-comparison-data).
Proof: on the small site apply the flat ringed-ideal complete equivalence. Its finite
reduction comparison identifies the strict quotient diagrams by rho. The specified
limit comparison lambda respects quotient units. The Koszul reconstruction identifies
unit-invertibility with local derived completeness on both sides. Consequently the
ambient restriction functor, restricted to these full subcategories, is an equivalence. -/
theorem restriction_complete_iff (T : Scheme.{t}) :
    ∀ K : d.derived T, d.TowerComplete T K ↔ IsComplete d T ((res d T).obj K) := by
  have hr : (res d T).ReflectsIsomorphisms :=
    (proEtaleRingSheafChangeAdjunction (𝟙 T)
      (exchangeConstantRing T A) (d.completedRing T)
      (exchangeConstantRing T A) (d.completedRing T)
      (exchangeScalar d T) (exchangeScalar d T) (exchangeConstantIso (𝟙 T) A)
      (d.integralRingIso (𝟙 T)) (exchangeScalar_comm d (𝟙 T))).1
  intro K
  let q := (lambda d T).app ((completedReductionTower T d).obj K) ≪≫
    (rlim (A := A) T).mapIso ((rho d T).app K)
  have hq : (res d T).map (d.completionUnit T K) ≫ q.hom =
      (unit d T).app ((res d T).obj K) := rho_unit_second d T K
  change IsIso (d.completionUnit T K) ↔ IsIso ((unit d T).app ((res d T).obj K))
  rw [← hq]
  constructor
  · intro h
    have := h
    infer_instance
  · intro h
    have := h
    have : IsIso ((res d T).map (d.completionUnit T K)) :=
      IsIso.of_isIso_comp_right _ q.hom
    exact isIso_of_reflects_iso (d.completionUnit T K) (res d T)

/-- The completed quotient completion followed by restriction is the constant quotient
completion of the restriction, through the specified comparisons lambda and rho. -/
def completedComparison (T : Scheme.{t}) :
    (completedReductionTower T d ⋙ completedRlim T (d.completedRing T)) ⋙ res d T ≅
      res d T ⋙ completion d T :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (completedReductionTower T d) (lambda d T) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (rho d T) (rlim (A := A) T) ≪≫ Functor.associator _ _ _

theorem completedComparison_hom_app (T : Scheme.{t}) (K : d.derived T) :
    (completedComparison d T).hom.app K =
      (lambda d T).hom.app ((completedReductionTower T d).obj K) ≫
        (rlim (A := A) T).map ((rho d T).hom.app K) := by
  simp only [completedComparison, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.id_comp, Category.comp_id]

/-- Restriction carries the completed completion unit to the constant completion unit. -/
theorem completedComparison_unit (T : Scheme.{t}) (K : d.derived T) :
    (res d T).map (d.completionUnit T K) ≫ (completedComparison d T).hom.app K =
      (unit d T).app ((res d T).obj K) := by
  rw [completedComparison_hom_app]
  exact rho_unit_second d T K

/-- The completed completion unit as a natural transformation. -/
def completedUnitNatTrans (T : Scheme.{t}) :
    𝟭 (d.derived T) ⟶ completedReductionTower T d ⋙ completedRlim T (d.completedRing T) :=
  (d.constantRlimAdjunction T).unit ≫
    Functor.whiskerRight (completedReductionAugmentation d T)
      (completedRlim T (d.completedRing T))

theorem completedUnitNatTrans_app (T : Scheme.{t}) (K : d.derived T) :
    (completedUnitNatTrans d T).app K = d.completionUnit T K := rfl

/-- The completed quotient completion inverts its own unit. -/
theorem completion_map_completionUnit_isIso (T : Scheme.{t}) (K : d.derived T) :
    IsIso ((completedReductionTower T d ⋙ completedRlim T (d.completedRing T)).map
      (d.completionUnit T K)) := by
  let C := completedReductionTower T d ⋙ completedRlim T (d.completedRing T)
  have hr := quotient_reflection d T
  have heq : C.map (d.completionUnit T K) = d.completionUnit T (C.obj K) := by
    apply (hr.2 K (C.obj (C.obj K)) (hr.1 (C.obj K))).1
    have hn := (completedUnitNatTrans d T).naturality (d.completionUnit T K)
    simp only [Functor.id_map, completedUnitNatTrans_app] at hn
    exact hn.symm
  rw [heq]
  exact hr.1 K

/-- The constant completion of a restricted object is complete. -/
theorem unit_completion_res_isIso (T : Scheme.{t}) (K : d.derived T) :
    IsIso ((unit d T).app ((completion d T).obj ((res d T).obj K))) := by
  let C := completedReductionTower T d ⋙ completedRlim T (d.completedRing T)
  have : IsIso (d.completionUnit T (C.obj K)) := (quotient_reflection d T).1 K
  have : IsIso ((unit d T).app ((res d T).obj (C.obj K))) := by
    rw [← completedComparison_unit]
    infer_instance
  exact @unit_isIso_of_iso _ _ (completion d T) (unit d T) _ _
    ((completedComparison d T).app K).symm this

/-- The constant completion inverts the unit at a restricted object. -/
theorem completion_map_unit_res_isIso (T : Scheme.{t}) (K : d.derived T) :
    IsIso ((completion d T).map ((unit d T).app ((res d T).obj K))) := by
  let C := completedReductionTower T d ⋙ completedRlim T (d.completedRing T)
  have := completion_map_completionUnit_isIso d T K
  rw [← completedComparison_unit, Functor.map_comp]
  have hn := (completedComparison d T).hom.naturality (d.completionUnit T K)
  have : IsIso ((C ⋙ res d T).map (d.completionUnit T K)) := by
    rw [Functor.comp_map]
    infer_instance
  have : IsIso ((completedComparison d T).hom.app K ≫
      (res d T ⋙ completion d T).map (d.completionUnit T K)) := by
    rw [← hn]
    infer_instance
  have : IsIso ((res d T ⋙ completion d T).map (d.completionUnit T K)) :=
    IsIso.of_isIso_comp_left ((completedComparison d T).hom.app K) _
  have : IsIso ((completion d T).map ((res d T).map (d.completionUnit T K))) := by
    rwa [Functor.comp_map] at this
  infer_instance

/-- Precomposition with a unit is injective into objects with invertible unit, once the
endofunctor inverts the given unit. -/
theorem precomp_unit_injective {C : Type*} [Category C] {G : C ⥤ C} (η : 𝟭 C ⟶ G)
    {X Y : C} (hX : IsIso (G.map (η.app X))) (hY : IsIso (η.app Y))
    {g₁ g₂ : G.obj X ⟶ Y} (h : η.app X ≫ g₁ = η.app X ≫ g₂) : g₁ = g₂ := by
  have hG : G.map g₁ = G.map g₂ := by
    apply (cancel_epi (G.map (η.app X))).mp
    rw [← G.map_comp, ← G.map_comp, h]
  apply (cancel_mono (η.app Y)).mp
  have h₁ := η.naturality g₁
  have h₂ := η.naturality g₂
  simp only [Functor.id_map, Functor.id_obj] at h₁ h₂
  rw [h₁, h₂, hG]

/-- Precomposition with a map inverted by a reflection-type endofunctor is bijective into
every object of the reflecting class. -/
theorem precomp_bijective_of_isIso_map {C : Type*} [Category C] (G : C ⥤ C) (η : 𝟭 C ⟶ G)
    (S : C → Prop)
    (hb : ∀ X Z, S Z → Function.Bijective (fun a : G.obj X ⟶ Z ↦ η.app X ≫ a))
    {X Y : C} (f : X ⟶ Y) (hf : IsIso (G.map f)) (Z : C) (hZ : S Z) :
    Function.Bijective (fun a : Y ⟶ Z ↦ f ≫ a) := by
  have := hf
  have hn (a : G.obj Y ⟶ Z) : f ≫ η.app Y ≫ a = η.app X ≫ G.map f ≫ a := by
    rw [← Category.assoc, ← Category.assoc]
    congr 1
    exact η.naturality f
  constructor
  · intro a b hab
    obtain ⟨a', rfl⟩ := (hb Y Z hZ).2 a
    obtain ⟨b', rfl⟩ := (hb Y Z hZ).2 b
    simp only at hab ⊢
    rw [hn, hn] at hab
    rw [(cancel_epi (G.map f)).mp ((hb X Z hZ).1 hab)]
  · intro c
    obtain ⟨c', rfl⟩ := (hb X Z hZ).2 c
    refine ⟨η.app Y ≫ inv (G.map f) ≫ c', ?_⟩
    simp only
    rw [hn, IsIso.hom_inv_id_assoc]

section CompleteEquivalence

set_option allowUnsafeReducibility true in
attribute [local semireducible] reductionModule completedReductionModuleTowerFunctor reduction

/-- Derived scalar extension along the constant-to-completed coefficient map, as a left
adjoint of the derived restriction `res`. -/
def resAdjunction (T : Scheme.{t}) : pbcDerivedExtend (exchangeScalar d T) ⊣ res d T :=
  pbcDerivedScalarAdjunction (exchangeScalar d T)

set_option backward.isDefEq.respectTransparency true in
/-- At every finite quotient level the ordinary scalar-extension unit becomes invertible:
the balancing map identifies `F_n ⊗ (B ⊗ M)` with `F_n ⊗ M`, and the strict balancing
comparison `ordinaryRho` identifies the two finite reductions. -/
theorem level_map_scalarUnit_isIso (T : Scheme.{t}) (n : ℕ)
    (P : CochainComplex (reductionModules T (exchangeConstantRing T A)) ℤ) (i : ℤ) :
    IsIso ((level d T n).map
      ((pbcScalarAdjunction (exchangeScalar d T)).unit.app (P.X i))) := by
  let φ := exchangeScalar d T
  let M := P.X i
  let β := (HomologicalComplex.eval _ _ i).mapIso
    (asIso (reductionBalance T φ (d.projection T n) (quotient d T n) rfl P))
  let e : (level d T n).obj ((pbcExtend φ ⋙ pbcRestrict φ).obj M) ≅ (level d T n).obj M :=
    ((ordinaryRho_existsUnique d T).exists.choose.app
      ((reductionChange T φ).obj M)).app (op n) ≪≫ (reductionRestrict T (quotient d T n)).mapIso β
  have hc : (level d T n).map ((pbcScalarAdjunction φ).unit.app M) ≫ e.hom = 𝟙 _ := by
    apply level_hom_ext T (quotient d T n) M
    intro U s x
    have h₁ := tensorSection_map d T n ((pbcScalarAdjunction φ).unit.app M) U s x
    have h₂ : ((pbcScalarAdjunction φ).unit.app M).val.app U x =
        reductionTensorSection T φ M U 1 x := by
      unfold pbcScalarAdjunction
      exact (pbcScalarAdjunction_exists φ).exists.choose_spec M U x
    have h₃ := (ordinaryRho_existsUnique d T).exists.choose_spec
      ((reductionChange T φ).obj M) n U s (reductionTensorSection T φ M U 1 x)
    have h₄ := reductionBalance_tmul T φ (d.projection T n) (quotient d T n) rfl P i U s 1 x
    simp only [map_one, mul_one] at h₄
    rw [h₂] at h₁
    with_unfolding_all
      exact (congrArg (fun w ↦ e.hom.val.app U w) h₁).trans
        ((congrArg (fun w ↦ β.hom.val.app U w) h₃).trans h₄)
  have hc' : e.hom ≫ (level d T n).map ((pbcScalarAdjunction φ).unit.app M) = 𝟙 _ := by
    rw [(Iso.comp_hom_eq_id e).1 hc, Iso.hom_inv_id]
  exact ⟨⟨e.hom, hc, hc'⟩⟩

/-- The strict quotient diagram inverts the ordinary scalar-extension unit on complexes. -/
theorem reductionModule_map_scalarUnit_isIso (T : Scheme.{t})
    (P : CochainComplex (reductionModules T (exchangeConstantRing T A)) ℤ) :
    IsIso (((reductionModule d T).mapHomologicalComplex (.up ℤ)).map
      ((NatTrans.mapHomologicalComplex (pbcScalarAdjunction (exchangeScalar d T)).unit
        (.up ℤ)).app P)) := by
  have (i : ℤ) : IsIso ((((reductionModule d T).mapHomologicalComplex (.up ℤ)).map
      ((NatTrans.mapHomologicalComplex (pbcScalarAdjunction (exchangeScalar d T)).unit
        (.up ℤ)).app P)).f i) := by
    have (n : ℕᵒᵖ) : IsIso (((reductionModule d T).map
        ((pbcScalarAdjunction (exchangeScalar d T)).unit.app (P.X i))).app n) :=
      level_map_scalarUnit_isIso d T n.unop P i
    have h : IsIso ((reductionModule d T).map
        ((pbcScalarAdjunction (exchangeScalar d T)).unit.app (P.X i))) :=
      NatIso.isIso_of_isIso_app _
    exact h
  exact HomologicalComplex.Hom.isIso_of_components _

/-- The derived quotient reduction inverts the localization of a chain map between K-flat
complexes once the strict quotient diagram inverts it. -/
theorem reduction_map_Q_isIso (T : Scheme.{t})
    {P P' : CochainComplex (reductionModules T (exchangeConstantRing T A)) ℤ} (g : P ⟶ P')
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := exchangeConstantRing T A) P)
    (hP' : CochainComplex.IsKFlatIndependentCoefficients (R := exchangeConstantRing T A) P')
    (hg : IsIso (((reductionModule d T).mapHomologicalComplex (.up ℤ)).map g)) :
    IsIso ((reduction d T).map (DerivedCategory.Q.map g)) := by
  let N := complexCounitNat (reductionModule d T) (reductionData d T).reduction
    (reductionData d T).counit
  have : IsIso (N.app P) := by
    rw [complexCounitNat_app]
    exact (reductionData d T).complexCounit_isIso P hP
  have : IsIso (N.app P') := by
    rw [complexCounitNat_app]
    exact (reductionData d T).complexCounit_isIso P' hP'
  have : IsIso (((reductionModule d T).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q).map g) := by
    rw [Functor.comp_map]
    infer_instance
  have : IsIso ((DerivedCategory.Q ⋙ (reductionData d T).reduction).map g ≫ N.app P') := by
    rw [N.naturality g]
    infer_instance
  have : IsIso ((DerivedCategory.Q ⋙ (reductionData d T).reduction).map g) :=
    IsIso.of_isIso_comp_right _ (N.app P')
  rw [Functor.comp_map] at this
  exact this

/-- The quotient reduction inverts the unit of derived scalar extension. -/
theorem reduction_map_resAdjunction_unit_isIso (T : Scheme.{t}) (X : D (A := A) T) :
    IsIso ((reduction d T).map ((resAdjunction d T).unit.app X)) := by
  let φ := exchangeScalar d T
  let adj := resAdjunction d T
  let Q : CochainComplex (reductionModules T (exchangeConstantRing T A)) ℤ ⥤ D (A := A) T :=
    DerivedCategory.Q
  obtain ⟨L, s, hL, hflat, hs, -⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (Q.objPreimage X)
  have := hs
  let e : Q.obj L ≅ X := asIso (Q.map s) ≪≫ Q.objObjPreimageIso X
  have hX : adj.unit.app X = e.inv ≫ adj.unit.app (Q.obj L) ≫
      (pbcDerivedExtend φ ⋙ res d T).map e.hom := by
    rw [← adj.unit.naturality e.hom, Functor.id_map, Iso.inv_hom_id_assoc]
  let g := (NatTrans.mapHomologicalComplex (pbcScalarAdjunction φ).unit (.up ℤ)).app L
  have hsp : adj.unit.app (Q.obj L) ≫ (res d T).map (pbcComplexCounit φ L) ≫
      (pbcRestrict φ).mapDerivedCategoryFactors.hom.app
        (((pbcExtend φ).mapHomologicalComplex (.up ℤ)).obj L) = Q.map g := by
    with_unfolding_all exact (pbcDerivedScalarAdjunction_exists φ).exists.choose_spec L hL
  have : IsIso (pbcComplexCounit φ L) := by
    have := pbcExtensionCounit_isIso φ L hL
    unfold pbcComplexCounit
    infer_instance
  have hU : adj.unit.app (Q.obj L) = Q.map g ≫ inv ((res d T).map (pbcComplexCounit φ L) ≫
      (pbcRestrict φ).mapDerivedCategoryFactors.hom.app
        (((pbcExtend φ).mapHomologicalComplex (.up ℤ)).obj L)) := by
    rw [← hsp, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have hP' : CochainComplex.IsKFlatIndependentCoefficients (R := exchangeConstantRing T A)
      (((pbcExtend φ ⋙ pbcRestrict φ).mapHomologicalComplex (.up ℤ)).obj L) :=
    (SheafOfModules.isKFlat_restrictScalars_of_flat φ (orderedScalarFlat d T) _
      (reductionChange_isKFlat T φ L hL hflat)).1
  have : IsIso ((reduction d T).map (Q.map g)) :=
    reduction_map_Q_isIso d T g hL hP' (reductionModule_map_scalarUnit_isIso d T L)
  rw [hX, hU]
  simp only [Functor.map_comp]
  infer_instance

/-- Derived scalar extension followed by restriction has the same quotient completion: the
completion of the counit of `resAdjunction` is invertible. -/
theorem completion_map_resAdjunction_counit_isIso (T : Scheme.{t}) (K : d.derived T) :
    IsIso ((completedReductionTower T d ⋙ completedRlim T (d.completedRing T)).map
      ((resAdjunction d T).counit.app K)) := by
  let adj := resAdjunction d T
  let C := completedReductionTower T d ⋙ completedRlim T (d.completedRing T)
  have hr : (res d T).ReflectsIsomorphisms :=
    (proEtaleRingSheafChangeAdjunction (𝟙 T)
      (exchangeConstantRing T A) (d.completedRing T)
      (exchangeConstantRing T A) (d.completedRing T)
      (exchangeScalar d T) (exchangeScalar d T) (exchangeConstantIso (𝟙 T) A)
      (d.integralRingIso (𝟙 T)) (exchangeScalar_comm d (𝟙 T))).1
  have := reduction_map_resAdjunction_unit_isIso d T ((res d T).obj K)
  have ht : (reduction d T).map (adj.unit.app ((res d T).obj K)) ≫
      (reduction d T).map ((res d T).map (adj.counit.app K)) = 𝟙 _ := by
    rw [← CategoryTheory.Functor.map_comp, adj.right_triangle_components]
    exact (reduction d T).map_id _
  have : IsIso ((reduction d T).map ((res d T).map (adj.counit.app K))) := by
    rw [IsIso.eq_inv_of_hom_inv_id ht]
    infer_instance
  have : IsIso ((res d T ⋙ completion d T).map (adj.counit.app K)) := by
    rw [Functor.comp_map]
    unfold completion
    rw [Functor.comp_map]
    infer_instance
  have : IsIso ((C ⋙ res d T).map (adj.counit.app K)) :=
    (NatIso.isIso_map_iff (completedComparison d T) _).2 this
  rw [Functor.comp_map] at this
  exact isIso_of_reflects_iso _ (res d T)

/-- Restriction is bijective on morphisms into a quotient-complete object. -/
theorem res_map_bijective (T : Scheme.{t}) (K K' : d.derived T)
    (hK' : d.TowerComplete T K') :
    Function.Bijective (fun f : K ⟶ K' ↦ (res d T).map f) := by
  let adj := resAdjunction d T
  have hb := precomp_bijective_of_isIso_map
    (completedReductionTower T d ⋙ completedRlim T (d.completedRing T))
    (completedUnitNatTrans d T) (d.TowerComplete T)
    (fun X Z hZ ↦ (quotient_reflection d T).2 X Z hZ) (adj.counit.app K)
    (completion_map_resAdjunction_counit_isIso d T K) K' hK'
  have he : (fun f : K ⟶ K' ↦ (res d T).map f) =
      (adj.homEquiv _ _) ∘ (fun f : K ⟶ K' ↦ adj.counit.app K ≫ f) := by
    funext f
    simp only [Function.comp_apply, Adjunction.homEquiv_unit, Functor.map_comp,
      Adjunction.right_triangle_components_assoc]
  rw [he]
  exact (adj.homEquiv _ _).bijective.comp hb

/-- Every constant-coefficient complete object is the restriction of a quotient-complete
completed-coefficient object: the completion of its derived scalar extension. -/
theorem res_essSurj (T : Scheme.{t}) (X : D (A := A) T) (hX : IsComplete d T X) :
    ∃ K : d.derived T, d.TowerComplete T K ∧ Nonempty ((res d T).obj K ≅ X) := by
  let adj := resAdjunction d T
  let C := completedReductionTower T d ⋙ completedRlim T (d.completedRing T)
  let K₀ := (pbcDerivedExtend (exchangeScalar d T)).obj X
  have : IsIso ((completion d T).map (adj.unit.app X)) := by
    have := reduction_map_resAdjunction_unit_isIso d T X
    unfold completion
    rw [Functor.comp_map]
    infer_instance
  have : IsIso ((unit d T).app X) := hX
  exact ⟨C.obj K₀, (quotient_reflection d T).1 K₀, ⟨(completedComparison d T).app K₀ ≪≫
    (asIso ((completion d T).map (adj.unit.app X))).symm ≪≫ (asIso ((unit d T).app X)).symm⟩⟩

end CompleteEquivalence

/-- Restriction gives an equivalence on the two full complete subcategories.
Source: Stacks Tags 099C, 099I and 099M
(blueprint: lem-weil-pbc-ordered-complete-equivalence).
Proof: transport to the coefficient-sized equivalent small site. The unit-preserving
Koszul comparison identifies the constant quotient-completion predicate with local
derived ideal-completeness. Restriction reflects local ideal-completeness, and
restriction_complete_iff therefore identifies the completed quotient-completion
predicate with local completeness over the completed algebra. The flat ringed-ideal
complete equivalence gives full faithfulness and essential surjectivity of restriction
on these full subcategories. Build its equivalence with this restriction functor;
the comparison with the ambient inclusions has identity components. -/
theorem restriction_complete_equiv (T : Scheme.{t}) :
    ∃ e : AComplete d T ≌ Complete d T,
      Nonempty (e.functor ⋙ ObjectProperty.ι (IsComplete d T) ≅
        inclusion d T ⋙ res d T) := by
  let F : AComplete d T ⥤ D (A := A) T := inclusion d T ⋙ res d T
  have : F.Faithful := ⟨fun {K K'} f g h ↦ ObjectProperty.hom_ext _
    ((res_map_bijective d T K.obj K'.obj K'.property).1 h)⟩
  have : F.Full := ⟨fun {K K'} g ↦ by
    obtain ⟨f, hf⟩ := (res_map_bijective d T K.obj K'.obj K'.property).2 g
    exact ⟨ObjectProperty.homMk f, hf⟩⟩
  let G := ObjectProperty.lift (IsComplete d T) F
    (fun K ↦ (restriction_complete_iff d T K.obj).mp K.property)
  have : G.EssSurj := ⟨fun Y ↦ by
    obtain ⟨K, hK, ⟨e⟩⟩ := res_essSurj d T Y.obj Y.property
    exact ⟨⟨K, hK⟩, ⟨ObjectProperty.isoMk _ e⟩⟩⟩
  have : G.IsEquivalence := {}
  exact ⟨G.asEquivalence, ⟨ObjectProperty.liftCompιIso _ _ _⟩⟩

theorem restriction_complete (T : Scheme.{t}) :
    (∀ K : d.derived T, d.TowerComplete T K ↔ IsComplete d T ((res d T).obj K)) ∧
      ∃ e : AComplete d T ≌ Complete d T,
        Nonempty (e.functor ⋙ ObjectProperty.ι (IsComplete d T) ≅
          inclusion d T ⋙ res d T) := by
  exact ⟨restriction_complete_iff d T, restriction_complete_equiv d T⟩

/-- The ordinary-to-completed comparison is the completed completion unit of the ordinary
pullback, through the canonical reduction-tower pullback comparison. -/
theorem ordinaryToCompleted_stratum (K : d.derived V) :
    d.ordinaryToCompleted u K ≫
        (completedRlim U (d.completedRing U)).map ((stratumReductionIso d u).hom.app K) =
      d.completionUnit U ((d.pull u).obj K) := by
  let R := completedRlim U (d.completedRing U)
  unfold AdicCoefficientDatum.ordinaryToCompleted AdicCoefficientDatum.completionUnit
  rw [Category.assoc, ← R.map_comp, Category.assoc, stratumReduction_augmentation d u K]
  rw [← Category.assoc, Iso.inv_hom_id_app]
  simp only [Functor.comp_obj, Category.id_comp]
  rfl

/-- The scalar comparison for completed pullback is fixed by the actual completion units.
Source: Stacks 099M, 099N
(blueprint: def-weil-pbc-ordered-coefficient-comparison-data).
Proof: completed pullback is the reflection of ordinary pullback. Restriction identifies
the complete categories and their units by rho and lambda. The ordinary comparison
alpha therefore extends uniquely across the completed pullback unit. The two hom-set
bijections give inverse extensions, so this is an isomorphism. Naturality and uniqueness
hold on the full complete category, not only on constructible or bounded objects. -/
theorem phi_exists :
    ∃ e : inclusion d V ⋙ d.completedPull u ⋙ res d U ≅
        inclusion d V ⋙ res d V ⋙ completePull d u,
      ∀ K : AComplete d V,
        (res d U).map (d.ordinaryToCompleted u K.obj) ≫ e.hom.app K =
          (alpha d u).hom.app K.obj ≫
            (unit d U).app ((pull (A := A) u).obj ((res d V).obj K.obj)) := by
  let R := completedRlim U (d.completedRing U)
  let e : inclusion d V ⋙ d.completedPull u ⋙ res d U ≅
      inclusion d V ⋙ res d V ⋙ completePull d u :=
    Functor.isoWhiskerLeft (inclusion d V)
      (Functor.isoWhiskerRight (Functor.isoWhiskerRight (stratumReductionIso d u) R)
          (res d U) ≪≫
        Functor.isoWhiskerLeft (d.pull u) (completedComparison d U) ≪≫
        Functor.isoWhiskerRight (alpha d u) (completion d U))
  refine ⟨e, fun K ↦ ?_⟩
  simp only [e, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    ObjectProperty.ι_obj]
  rw [← Category.assoc, ← Functor.map_comp, ordinaryToCompleted_stratum,
    ← Category.assoc, completedComparison_unit]
  exact ((unit d U).naturality ((alpha d u).hom.app K.obj)).symm

/-- The completed pullback/scalar comparison is determined by its unit equation.
Source: Stacks Tags 099M and 099N
(blueprint: lem-weil-pbc-ordered-phi-uniqueness).
Proof: for a complete input K, put P equal to its ordinary completed-coefficient
pullback. Restriction of its completion is the constant completion of res(P), by the
unit-preserving quotient and limit comparisons. Under this identification the map
res(ordinaryToCompleted) is the constant completion unit. The common target of the
two components is complete. The completion reflection's Hom bijection says that
precomposition by this unit is injective into that target. The displayed hypotheses
therefore force equality of the two components. Extensionality of natural
transformations and uniqueness of inverses give equality of the isomorphisms. -/
theorem phi_unique
    {e₁ e₂ : inclusion d V ⋙ d.completedPull u ⋙ res d U ≅
        inclusion d V ⋙ res d V ⋙ completePull d u}
    (h₁ : ∀ K : AComplete d V,
      (res d U).map (d.ordinaryToCompleted u K.obj) ≫ e₁.hom.app K =
        (alpha d u).hom.app K.obj ≫
          (unit d U).app ((pull (A := A) u).obj ((res d V).obj K.obj)))
    (h₂ : ∀ K : AComplete d V,
      (res d U).map (d.ordinaryToCompleted u K.obj) ≫ e₂.hom.app K =
        (alpha d u).hom.app K.obj ≫
          (unit d U).app ((pull (A := A) u).obj ((res d V).obj K.obj))) :
    e₁ = e₂ := by
  apply Iso.ext
  apply NatTrans.ext
  funext K
  let j : (res d U).obj ((d.completedPull u).obj K.obj) ≅
      (completion d U).obj ((res d U).obj ((d.pull u).obj K.obj)) :=
    (res d U).mapIso ((completedRlim U (d.completedRing U)).mapIso
      ((stratumReductionIso d u).app K.obj)) ≪≫
      (completedComparison d U).app ((d.pull u).obj K.obj)
  have hj : (res d U).map (d.ordinaryToCompleted u K.obj) ≫ j.hom =
      (unit d U).app ((res d U).obj ((d.pull u).obj K.obj)) := by
    rw [← completedComparison_unit, ← ordinaryToCompleted_stratum d u K.obj, Functor.map_comp]
    simp only [j, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Category.assoc]
  have hY : IsIso ((unit d U).app ((completePull d u).obj ((res d V).obj K.obj))) := by
    have := unit_completion_res_isIso d U ((d.pull u).obj K.obj)
    exact @unit_isIso_of_iso _ _ (completion d U) (unit d U) _ _
      ((completion d U).mapIso ((alpha d u).app K.obj)).symm this
  have key : j.inv ≫ e₁.hom.app K = j.inv ≫ e₂.hom.app K := by
    apply precomp_unit_injective (unit d U)
      (completion_map_unit_res_isIso d U ((d.pull u).obj K.obj)) hY
    rw [← hj]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    exact (h₁ K).trans (h₂ K).symm
  exact (cancel_epi j.inv).mp key

theorem phi_existsUnique :
    ∃! e : inclusion d V ⋙ d.completedPull u ⋙ res d U ≅
        inclusion d V ⋙ res d V ⋙ completePull d u,
      ∀ K : AComplete d V,
        (res d U).map (d.ordinaryToCompleted u K.obj) ≫ e.hom.app K =
          (alpha d u).hom.app K.obj ≫
            (unit d U).app ((pull (A := A) u).obj ((res d V).obj K.obj)) := by
  obtain ⟨e, he⟩ := phi_exists d u
  refine ⟨e, he, ?_⟩
  intro e' he'
  exact (phi_unique d u he he').symm

/-- The completed pullback/scalar isomorphism, retaining its completion-unit equation.
Source: Stacks 099N (blueprint: def-weil-pbc-ordered-coefficient-comparison-data). -/
def phi : inclusion d V ⋙ d.completedPull u ⋙ res d U ≅
    inclusion d V ⋙ res d V ⋙ completePull d u := (phi_existsUnique d u).exists.choose

variable {X' X Y' Y : Scheme.{t}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- The specified completed-coefficient source reconstruction.
Source: Stacks 099M (blueprint: def-weil-pbc-ordered-coefficient-comparison-data). -/
def sourceReconstruction (K : d.derived X) :=
  (completedRlim Y' (d.completedRing Y')).mapIso
    ((d.reductionTowerPullbackIso g).app ((d.push f).obj K))

/-- The source comparison s a is exactly the ordered projection-formula comparison.
Source: blueprint completed-exchange-coherence, paragraph 2
(blueprint: def-weil-pbc-ordered-coefficient-comparison-data). -/
def sourceA (K : d.derived X) :=
  (completedRlim Y' (d.completedRing Y')).mapIso
    (d.towerH (f := f) (f' := f') (g := g) (g' := g') K)

/-- The specified direct-image/limit comparison c a.
Source: Stacks 0A07 (blueprint: def-weil-pbc-ordered-coefficient-comparison-data). -/
def targetA (K : d.derived X) :=
  (d.directImageRlimIso f').app
    ((d.towerPull g').obj ((completedReductionTower X d).obj K))

/-- The left corner comparison includes the image of the same strict reduction rho.
Source: Stacks 0E48 (blueprint: def-weil-pbc-ordered-coefficient-comparison-data). -/
def beta (K : d.derived X) :=
  (exchangeCornerB d f g).app ((completedReductionTower X d).obj K) ≪≫
    (exchangeConstantPull (A := A) g).mapIso
      ((exchangeConstantPush (A := A) f).mapIso ((rho d X).app K))

/-- The right corner comparison includes the image of that same strict reduction rho.
Source: Stacks 0E48 (blueprint: def-weil-pbc-ordered-coefficient-comparison-data). -/
def delta (K : d.derived X) :=
  (exchangeCornerD d g' f').app ((completedReductionTower X d).obj K) ≪≫
    (exchangeConstantPush (A := A) f').mapIso
      ((exchangeConstantPull (A := A) g').mapIso ((rho d X).app K))

/-- The scalar comparison at M uses finite reduction, ordinary pullback and chi f.
Source: Stacks 099M, 0E48
(blueprint: def-weil-pbc-ordered-coefficient-comparison-data). -/
def rhoM (K : d.derived X) :=
  (rho d Y').app ((d.pull g).obj ((d.push f).obj K)) ≪≫
    (reduction d Y').mapIso ((alpha d g).app ((d.push f).obj K)) ≪≫
    (reduction d Y').mapIso ((pull (A := A) g).mapIso ((chi d f).app K))

/-- The pulled-back strict reduction comparison retains its full diagram, not just levels.
Source: Stacks 099M, 0E48
(blueprint: def-weil-pbc-ordered-coefficient-comparison-data). -/
def rhoPull (K : d.derived X) :=
  (exchangeResPull d g').app ((completedReductionTower X d).obj K) ≪≫
    (exchangeConstantPull (A := A) g').mapIso ((rho d X).app K)

/-- The source scalar identification, with phi evaluated at the complete direct image.
Source: Stacks 099N (blueprint: def-weil-pbc-ordered-coefficient-comparison-data). -/
def iotaS (K : d.derived X) (hK : d.TowerComplete X K) :=
  (phi d g).app ⟨(d.push f).obj K, d.push_complete f K hK⟩ ≪≫
    (completePull d g).mapIso ((chi d f).app K)

/-- The target scalar identification is chi followed by direct image of phi.
Source: Stacks 099N (blueprint: def-weil-pbc-ordered-coefficient-comparison-data). -/
def iotaT (K : d.derived X) (hK : d.TowerComplete X K) :=
  (chi d f').app ((d.completedPull g').obj K) ≪≫
    (push (A := A) f').mapIso ((phi d g').app ⟨K, hK⟩)

/-- Source functor for the normalized equation, on the full derived-complete category.
Source: blueprint completed-exchange-coherence, paragraph 2
(blueprint: def-weil-pbc-ordered-coefficient-comparison-data). -/
def normalizedSource := inclusion d X ⋙ d.push f ⋙ d.completedPull g ⋙ res d Y'

/-- Target functor for the normalized equation in constant coefficients.
Source: blueprint completed-exchange-coherence, paragraph 2
(blueprint: def-weil-pbc-ordered-coefficient-comparison-data). -/
def normalizedTarget := inclusion d X ⋙ res d X ⋙ completePull d g' ⋙ push (A := A) f'

/-- The restricted raw ordered construction followed by the specified target comparison.
Source: blueprint completed-exchange-coherence, paragraph 2
(blueprint: def-weil-pbc-ordered-coefficient-comparison-data). -/
def rawComponent (sq : ChosenCartesianSquare g' f' f g) (K : AComplete d X) :
    (normalizedSource (f := f) (g := g) d).obj K ⟶
      (normalizedTarget (g' := g') (f' := f') d).obj K :=
  (res d Y').map (d.completedExchange sq K.obj) ≫
    (iotaT (g' := g') (f' := f') d K.obj K.property).hom

/-- The specified constant strict mate, conjugated by s, t and the source scalar map.
Source: Stacks 099M, 0E48
(blueprint: def-weil-pbc-ordered-coefficient-comparison-data). -/
def constantComponent (sq : ChosenCartesianSquare g' f' f g) (K : AComplete d X) :
    (normalizedSource (f := f) (g := g) d).obj K ⟶
      (normalizedTarget (g' := g') (f' := f') d).obj K :=
  (iotaS (f := f) (g := g) d K.obj K.property).hom ≫
    (S (f := f) (g := g) d ((res d X).obj K.obj)).hom ≫
    (rlim (A := A) Y').map ((exchangeConstantSquare (A := A) sq).exchangeTowerMate.app
      ((reduction d X).obj ((res d X).obj K.obj))) ≫
    (T (f' := f') (g' := g') d ((res d X).obj K.obj)).inv

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Both displayed composites are natural for every morphism of complete inputs.
Source: Stacks 0E48 (blueprint: def-weil-pbc-ordered-coefficient-comparison-data).
Proof: the raw strict exchange is the composite H inverse, reduction of the ambient
mate, H prime. All its terms are natural in the ambient input. The scalar comparisons
are natural isomorphisms defined by ordinary sections or universal model comparisons.
Their completed extensions are natural by uniqueness under the completion unit. The
constant mate and its reconstruction and direct-limit comparisons are natural as well.
Compose these naturality equations. Fullness allows every morphism between complete
objects, with no boundedness or finite-origin restriction. -/
theorem normalized_naturality (sq : ChosenCartesianSquare g' f' f g)
    (K L : AComplete d X) (a : K ⟶ L) :
    (normalizedSource (f := f) (g := g) d).map a ≫ rawComponent d sq L =
      rawComponent d sq K ≫ (normalizedTarget (g' := g') (f' := f') d).map a ∧
    (normalizedSource (f := f) (g := g) d).map a ≫ constantComponent d sq L =
      constantComponent d sq K ≫ (normalizedTarget (g' := g') (f' := f') d).map a := by
  let piA (U V : Scheme.{t}) (u : U ⟶ V) :
      d.push u ⋙ completedReductionTower V d ≅
        completedReductionTower U d ⋙ d.towerPush u :=
    NatIso.ofComponents (fun K ↦ asIso (d.towerProjection u K))
      (fun {K L} a ↦ (d.towerProjection_properties u K).2.1 L a)
  let e : d.push f ⋙ d.completedPull g ⟶ d.completedPull g' ⋙ d.push f' :=
    Functor.whiskerRight (Functor.isoWhiskerRight (piA X Y f) (d.towerPull g)).hom
        (completedRlim Y' (d.completedRing Y')) ≫
      Functor.whiskerRight (exchangeStrictNatTrans d sq)
        (completedRlim Y' (d.completedRing Y')) ≫
      Functor.whiskerLeft (completedReductionTower X d ⋙ d.towerPull g')
        (d.directImageRlimIso f').inv
  let it : inclusion d X ⋙ d.completedPull g' ⋙ d.push f' ⋙ res d Y' ≅
      normalizedTarget (g' := g') (f' := f') d :=
    Functor.isoWhiskerLeft (inclusion d X ⋙ d.completedPull g') (chi d f') ≪≫
      Functor.isoWhiskerRight (phi d g') (push (A := A) f')
  constructor
  · exact (Functor.whiskerLeft (inclusion d X)
      (Functor.whiskerRight e (res d Y')) ≫ it.hom).naturality a
  · let aj := exchangeTowerAdjunction f (exchangeConstantRing Y A)
      (exchangeConstantRing X A) (exchangeConstantIso f A)
    let ar := proEtaleRingDerivedAdjunction f (exchangeConstantRing Y A)
      (exchangeConstantRing X A) (exchangeConstantIso f A)
    let pi0 := (mateEquiv ar aj
      (TwoSquare.mk _ _ _ _ (reductionPullIso d f).hom)).natTrans
    have hpi (M : D (A := A) X) : pi0.app M = projection d f M := by
      apply (aj.homEquiv _ _).symm.injective
      change (aj.homEquiv _ _).symm (pi0.app M) =
        (aj.homEquiv _ _).symm ((aj.homEquiv _ _)
          ((reductionPullIso d f).hom.app ((push (A := A) f).obj M) ≫
            (reduction d X).map (ar.counit.app M)))
      rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit]
      exact mateEquiv_counit ar aj
        (TwoSquare.mk _ _ _ _ (reductionPullIso d f).hom) M
    let p0 : push (A := A) f ⋙ reduction d Y ≅
        reduction d X ⋙ exchangeConstantPush (A := A) f :=
      NatIso.ofComponents (fun M ↦ asIso (projection d f M)) (by
        intro M N b
        simpa only [asIso_hom, ← hpi] using pi0.naturality b)
    let h0 := Functor.isoWhiskerLeft (push (A := A) f) (reductionPullIso d g).symm ≪≫
      Functor.isoWhiskerRight p0 (exchangeConstantPull (A := A) g)
    let s0 := Functor.isoWhiskerRight h0 (rlim (A := A) Y')
    let t0 := Functor.isoWhiskerLeft (reduction d X)
      (Functor.isoWhiskerLeft (exchangeConstantPull (A := A) g')
        (directLimitIso (A := A) f'))
    let rec0 : completePull d g' ≅
        reduction d X ⋙ exchangeConstantPull (A := A) g' ⋙ rlim (A := A) X' :=
      Functor.isoWhiskerRight (reductionPullIso d g').symm (rlim (A := A) X')
    let tt := Functor.isoWhiskerRight rec0 (push (A := A) f') ≪≫ t0
    let pushed : AComplete d X ⥤ AComplete d Y :=
      ObjectProperty.lift (d.TowerComplete Y) (inclusion d X ⋙ d.push f)
        (fun M ↦ d.push_complete f M.obj M.property)
    let src : normalizedSource (f := f) (g := g) d ≅
        inclusion d X ⋙ res d X ⋙ push (A := A) f ⋙ completePull d g :=
      Functor.isoWhiskerLeft pushed (phi d g) ≪≫
        Functor.isoWhiskerRight (Functor.isoWhiskerLeft (inclusion d X) (chi d f))
          (completePull d g)
    let cc := src.hom ≫
      Functor.whiskerLeft (inclusion d X ⋙ res d X) s0.hom ≫
      Functor.whiskerLeft (inclusion d X ⋙ res d X ⋙ reduction d X)
        (Functor.whiskerRight
          (exchangeConstantSquare (A := A) sq).exchangeTowerMate (rlim (A := A) Y')) ≫
      Functor.whiskerLeft (inclusion d X ⋙ res d X) tt.inv
    exact cc.naturality a

/-- The raw ordered exchange as an actual natural transformation after scalar restriction.
Source: blueprint completed-exchange-coherence, paragraph 2
(blueprint: def-weil-pbc-ordered-coefficient-comparison-data). -/
def rawNormalized (sq : ChosenCartesianSquare g' f' f g) :
    normalizedSource (f := f) (g := g) d ⟶ normalizedTarget (g' := g') (f' := f') d where
  app K := rawComponent d sq K
  naturality K L a := (normalized_naturality d sq K L a).1

/-- The specified constant-coefficient ordered expression as a natural transformation.
Source: Stacks 099M, 0E48
(blueprint: def-weil-pbc-ordered-coefficient-comparison-data). -/
def constantNormalized (sq : ChosenCartesianSquare g' f' f g) :
    normalizedSource (f := f) (g := g) d ⟶ normalizedTarget (g' := g') (f' := f') d where
  app K := constantComponent d sq K
  naturality K L a := (normalized_naturality d sq K L a).2

end AlgebraicGeometry.Scheme.OrderedExchange
