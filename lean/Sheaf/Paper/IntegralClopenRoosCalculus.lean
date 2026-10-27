/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X6
-/
module

public import Sheaf.Paper.ClopenIntegralRestriction
import Sheaf.AlgebraicGeometry.ProEtaleClopenRingedModuleGluing
import all Sheaf.AlgebraicGeometry.ProEtaleFiniteClopenTensorCalculus
import all Sheaf.AlgebraicGeometry.ClopenStrictTowerRoosEquivalence
import all Sheaf.AlgebraicGeometry.ProEtaleOperations
import WeilConjectures.CategoryTheory.Triangulated.DerivedCountableProductsExistence

/-! # Integral finite-clopen Roos calculus

The existing proved integral Roos calculation is extracted from augmented descent
so each proof module elaborates within the per-file limit. No comparison is changed.
Source: Stacks 04TS, 07KC and 08TC
(blueprint: lem-pur-integral-clopen-roos-calculus).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.ClopenMonoidalDescent.modulesAbelian
  AlgebraicGeometry.Scheme.ProEt.ClopenLocalization.modulesAbelian
attribute [local irreducible] HasDerivedCategory.standard
  WeilConjectures.completedIntegralCoefficientSheafUnrestricted
  WeilConjectures.scalarReductionExistence WeilConjectures.scalarReductionDerivedExistence
  WeilConjectures.unrestrictedIntegralReductionExistence

universe u w

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme

namespace WeilConjectures.PurityFiniteSetting

variable (P : PurityFiniteSetting.{u})
  (X : Over (Spec (CommRingCat.of P.field.k)))
  [hft : LocallyOfFiniteType X.hom] [hqc : QuasiCompact X.hom]
  {I : Type w} [hfinite : Finite I]
  (Xi : I → Over (Spec (CommRingCat.of P.field.k))) (j : ∀ i, Xi i ⟶ X)
  [∀ i, IsOpenImmersion (j i).left] [hclosed : ∀ i, IsClosedImmersion (j i).left]
  (hdisjoint : ∀ i i', i ≠ i' →
    Disjoint (Set.range (j i).left) (Set.range (j i').left))
  (hcover : (⋃ i, Set.range (j i).left) = Set.univ)

include hfinite hclosed hdisjoint hcover

attribute [-instance] AlgebraicGeometry.Scheme.ProEt.ClopenRoos.modulesAbelian
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived in
omit hft hqc in
/-- Apply finite-clopen module gluing, normalized coefficient transport and exact
countable products before descending to derived categories. Source: Stacks 04TS,
07KC and 08TC (blueprint: lem-pur-integral-clopen-roos-calculus). -/
theorem integralClopenRoosCalculus :
    Nonempty (HasCountableProducts
      (DerivedCategory (scalarReductionSource P.coefficients.l P.extension X.left))) ∧
    (∀ i, Nonempty (HasCountableProducts
      (DerivedCategory (scalarReductionSource P.coefficients.l P.extension (Xi i).left)))) ∧
    (Functor.pi' (fun i ↦
      clopenIntegralDerivedRestriction P.coefficients.l P.extension (j i).left)).IsEquivalence ∧
    ∀ (K : ℕ → DerivedCategory (scalarReductionSource P.coefficients.l P.extension X.left))
      [HasProduct K]
      [∀ i, HasProduct (fun n ↦ (clopenIntegralDerivedRestriction P.coefficients.l
        P.extension (j i).left).obj (K n))],
      ∃ φ : ∀ i, (clopenIntegralDerivedRestriction P.coefficients.l P.extension
          (j i).left).obj (∏ᶜ K) ≅
        ∏ᶜ (fun n ↦ (clopenIntegralDerivedRestriction P.coefficients.l P.extension
          (j i).left).obj (K n)),
        (∀ i, (φ i).hom = piComparison
          (clopenIntegralDerivedRestriction P.coefficients.l P.extension (j i).left) K) ∧
        ∀ (t : ∀ n, K (n + 1) ⟶ K n)
          (M : DerivedCategory (scalarReductionSource P.coefficients.l P.extension X.left))
          (c : M ⟶ ∏ᶜ K) (δ : ∏ᶜ K ⟶ M⟦(1 : ℤ)⟧),
          IsDerivedLimitTriangle t M c δ ↔ ∀ i,
            IsDerivedLimitTriangle
              (fun n ↦ (clopenIntegralDerivedRestriction P.coefficients.l P.extension
                (j i).left).map (t n))
              ((clopenIntegralDerivedRestriction P.coefficients.l P.extension (j i).left).obj M)
              ((clopenIntegralDerivedRestriction P.coefficients.l P.extension (j i).left).map c ≫
                (φ i).hom)
              ((φ i).inv ≫
                (clopenIntegralDerivedRestriction P.coefficients.l P.extension (j i).left).map δ ≫
                ((clopenIntegralDerivedRestriction P.coefficients.l P.extension
                  (j i).left).commShiftIso (1 : ℤ)).hom.app M) := by
  classical
  let R : Sheaf (ProEt.topology X.left) CommRingCat.{u + 1} :=
    completedIntegralCommRingSheafUnrestricted P.coefficients.l P.extension X.left
  let S := completedIntegralCoefficientSheafUnrestricted.{u, u}
    P.coefficients.l P.extension X.left
  let r (i : I) : scalarReductionSource.{u, u} P.coefficients.l P.extension X.left ⥤
      scalarReductionSource.{u, u} P.coefficients.l P.extension (Xi i).left :=
    clopenIntegralModuleRestriction P.coefficients.l P.extension (j i).left
  let D (i : I) := scalarReductionSource.{u, u} P.coefficients.l P.extension (Xi i).left
  obtain ⟨E₀, hE₀⟩ := ProEt.FiniteClopenTensor.moduleGluing.{u, u, w}
    X.left I (fun i ↦ (Xi i).left) (fun i ↦ (j i).left) hdisjoint
    (fun x ↦ Set.mem_iUnion.mp (hcover.symm ▸ Set.mem_univ x)) R
  let e (i : I) := proEtaleScalarEquivalence (Xi i).left
    ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso
      (asIso (clopenCompletionMap P.coefficients.l P.extension (j i).left)))
  let E := E₀.trans (CategoryTheory.Equivalence.pi e)
  have hE : E.functor = Functor.pi' r := by
    change E₀.functor ⋙ Functor.pi (fun i ↦ (e i).functor) = _
    rw [hE₀]
    rfl
  let := ProEt.FiniteClopenTensor.piPreadditive D
  have hAdd : E.functor.Additive := by
    constructor
    intro M N f g
    rw [hE]
    funext i
    exact (r i).map_add
  have hr : JointlyReflectIsomorphisms r := by
    constructor
    intro M N f hf
    have : IsIso (E.functor.map f) := by
      rw [hE]
      exact (isIso_pi_iff _).mpr hf
    exact isIso_of_reflects_iso f E.functor
  have hD := ProEt.FiniteClopenTensor.derivedPi_isEquivalence r E.inverse
    (fun M N ↦ E.inverse.map_zero M N)
    (by simpa only [hE] using E.unitIso)
    (by simpa only [hE] using E.counitIso) hr
  have hX : CountableAB4Star (scalarReductionSource
      P.coefficients.l P.extension X.left) :=
    ProEt.ClopenRoos.module_countable_exact.{u, u + 1, u} X.left S
  have hY (i : I) : CountableAB4Star (D i) :=
    ProEt.ClopenRoos.module_countable_exact.{u, u + 1, u}
    (Xi i).left
    (completedIntegralCoefficientSheafUnrestricted P.coefficients.l P.extension (Xi i).left)
  refine ⟨⟨derivedCategory_hasCountableProducts (scalarReductionSource
      P.coefficients.l P.extension X.left)⟩,
    (fun i ↦ ⟨derivedCategory_hasCountableProducts (D i)⟩), hD, ?_⟩
  have hp (i : I) : PreservesLimitsOfShape (Discrete ℕ) (r i) := by
    let Si := completedIntegralCoefficientSheafUnrestricted
      P.coefficients.l P.extension (Xi i).left
    let V := SheafOfModules.forget.{u + 1} Si ⋙ PresheafOfModules.toPresheaf Si.obj
    have : PreservesLimitsOfShape (Discrete ℕ) (r i ⋙ V) := by
      change PreservesLimitsOfShape (Discrete ℕ)
        ((SheafOfModules.forget.{u + 1} S ⋙ PresheafOfModules.toPresheaf S.obj) ⋙
          (Functor.whiskeringLeft (Xi i).left.ProEtᵒᵖ X.left.ProEtᵒᵖ
            AddCommGrpCat.{u + 1}).obj (clopenSiteInclusion (j i).left).op)
      infer_instance
    have : ReflectsLimitsOfShape (Discrete ℕ) V :=
      reflectsLimitsOfShape_of_reflectsIsomorphisms
    exact preservesLimitsOfShape_of_reflects_of_preserves _ V
  have hpD (i : I) : PreservesLimitsOfShape (Discrete ℕ) (r i).mapDerivedCategory :=
    ProEt.ClopenRoos.derived_product_preservation (r i)
  exact ProEt.ClopenRoos.limit_triangle_descent
    (fun i ↦ DerivedCategory (D i)) (fun i ↦ (r i).mapDerivedCategory)

end WeilConjectures.PurityFiniteSetting
