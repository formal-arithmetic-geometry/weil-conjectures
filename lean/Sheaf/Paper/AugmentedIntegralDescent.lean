/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q136
-/
module

public import Sheaf.Paper.ClopenIntegralRestriction
public import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.AlgebraicGeometry.ProEtaleTorAmplitudePresentations
import Sheaf.AlgebraicGeometry.ProEtaleClopenRingedModuleGluing
import all Sheaf.AlgebraicGeometry.ProEtaleFiniteClopenTensorCalculus
import all Sheaf.AlgebraicGeometry.ClopenStrictTowerRoosEquivalence
import all Sheaf.AlgebraicGeometry.ProEtaleOperations
import WeilConjectures.CategoryTheory.Triangulated.DerivedCountableProductsExistence
import Sheaf.Paper.IntegralReductionTowerWellDefinedUnrestricted
import Sheaf.Paper.IntegralReductionFiniteClopenBounds
import Sheaf.Paper.SfDerivedCompleteLegacyComparison
import Mathlib.Data.Fintype.Lattice

/-! # Augmented integral reductions and clopen descent

Source: Bhatt--Scholze, Proposition 3.5.1(1) and Definition 3.5.2, p. 24
(blueprint: lem-pur-clopen-augmented-integral-descent).

The natural-number index n denotes exponent n+1. Restriction is ordinary restriction,
with the canonical coefficient transport; it performs no derived completion.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

attribute [local irreducible] HasDerivedCategory.standard
  WeilConjectures.completedIntegralCoefficientSheafUnrestricted
  WeilConjectures.scalarReductionExistence WeilConjectures.scalarReductionDerivedExistence
  WeilConjectures.unrestrictedIntegralReductionExistence

universe u w

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme

private def productIso {C : Type*} [Category C] {A B : ℕ → C}
    [HasProduct A] [HasProduct B] (e : ∀ n, A n ≅ B n) : ∏ᶜ A ≅ ∏ᶜ B where
  hom := Limits.Pi.map (fun n ↦ (e n).hom)
  inv := Limits.Pi.map (fun n ↦ (e n).inv)
  hom_inv_id := by ext n; simp [Pi.map_π]
  inv_hom_id := by ext n; simp [Pi.map_π]

private theorem roosTransport {C : Type*} [Category C] [HasZeroObject C]
    [HasShift C ℤ] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] {A B : ℕ → C} [HasProduct A] [HasProduct B]
    (f : ∀ n, A (n + 1) ⟶ A n) (g : ∀ n, B (n + 1) ⟶ B n)
    (e : ∀ n, A n ≅ B n)
    (he : ∀ n, (e (n + 1)).hom ≫ g n = f n ≫ (e n).hom)
    (M : C) (c : M ⟶ ∏ᶜ A) (δ : ∏ᶜ A ⟶ M⟦(1 : ℤ)⟧) :
    IsDerivedLimitTriangle f M c δ ↔
      IsDerivedLimitTriangle g M (c ≫ (productIso e).hom) ((productIso e).inv ≫ δ) := by
  have ht := towerTransitionEndomorphism_natural_backward f g (fun n ↦ (e n).hom) he
  apply Pretriangulated.distinguished_iff_of_iso
  refine Pretriangulated.Triangle.isoMk _ _ (Iso.refl _) (productIso e) (productIso e)
    (by simp) ht.symm ?_
  simp

namespace WeilConjectures.PurityFiniteSetting

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Ordinary finite-coefficient restriction, with the coefficient map fixed by constant
sections. This is precomposition, followed by scalar transport, not completion.
Source: Bhatt--Scholze, Definition 3.5.2, p. 24; Stacks 03CO and 04TS
(blueprint: lem-pur-clopen-augmented-integral-descent). -/
def augmentedFiniteRestriction {Y X : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    (n : ℕ) : scalarReductionTarget l E X n ⥤ scalarReductionTarget l E Y n :=
  clopenRestriction j (integralCoefficientCommRingSheaf l E X n) ⋙
    SheafOfModules.restrictScalars
      ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (clopenConstantMap j (CommRingCat.of
          (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))))

/-- Exactness of ordinary finite-coefficient restriction.
Source: Stacks 04TS and 015F; Bhatt--Scholze, Definition 3.5.2, p. 24
(blueprint: lem-pur-clopen-augmented-integral-descent).
Proof (node step 1): restriction to an open is restriction to a localized site, hence
preserves kernels and sheafified cokernels. The constant-section coefficient comparison
is an isomorphism, so its scalar transport is an additive exact equivalence. Compose
these functors. This also covers the empty site and every positive quotient exponent. -/
theorem augmentedFiniteRestriction_exact {Y X : Scheme.{u}} (j : Y ⟶ X)
    [IsOpenImmersion j] (n : ℕ) :
    (augmentedFiniteRestriction l E j n).Additive ∧
      PreservesFiniteLimits (augmentedFiniteRestriction l E j n) ∧
      PreservesFiniteColimits (augmentedFiniteRestriction l E j n) := by
  let R := integralCoefficientCommRingSheaf l E X n
  let S := integralCoefficientSheaf l E Y n
  let V := SheafOfModules.toSheaf S
  have : PreservesFiniteLimits (augmentedFiniteRestriction l E j n ⋙ V) := by
    change PreservesFiniteLimits (clopenRestriction j R ⋙ SheafOfModules.toSheaf _)
    infer_instance
  have : PreservesFiniteColimits (augmentedFiniteRestriction l E j n ⋙ V) := by
    change PreservesFiniteColimits (clopenRestriction j R ⋙ SheafOfModules.toSheaf _)
    infer_instance
  refine ⟨?_, preservesFiniteLimits_of_reflects_of_preserves _ V,
    preservesFiniteColimits_of_reflects_of_preserves _ V⟩
  constructor
  intro M N f g
  ext U x
  rfl

/-- Additivity extracted from the exactness assertion. Source: Stacks 04TS
(blueprint: lem-pur-clopen-augmented-integral-descent). -/
instance augmentedFiniteRestrictionAdditive {Y X : Scheme.{u}} (j : Y ⟶ X)
    [IsOpenImmersion j] (n : ℕ) : (augmentedFiniteRestriction l E j n).Additive :=
  (augmentedFiniteRestriction_exact l E j n).1

/-- Left exactness extracted from the same assertion. Source: Stacks 04TS
(blueprint: lem-pur-clopen-augmented-integral-descent). -/
instance augmentedFiniteRestrictionLimits {Y X : Scheme.{u}} (j : Y ⟶ X)
    [IsOpenImmersion j] (n : ℕ) :
    PreservesFiniteLimits (augmentedFiniteRestriction l E j n) :=
  (augmentedFiniteRestriction_exact l E j n).2.1

/-- Right exactness extracted from the same assertion. Source: Stacks 04TS
(blueprint: lem-pur-clopen-augmented-integral-descent). -/
instance augmentedFiniteRestrictionColimits {Y X : Scheme.{u}} (j : Y ⟶ X)
    [IsOpenImmersion j] (n : ℕ) :
    PreservesFiniteColimits (augmentedFiniteRestriction l E j n) :=
  (augmentedFiniteRestriction_exact l E j n).2.2

/-- Ordinary finite restriction on unbounded derived categories. Source: Stacks 015F
(blueprint: lem-pur-clopen-augmented-integral-descent). -/
def augmentedFiniteDerivedRestriction {Y X : Scheme.{u}} (j : Y ⟶ X)
    [IsOpenImmersion j] (n : ℕ) :=
  (augmentedFiniteRestriction l E j n).mapDerivedCategory

attribute [-instance] AlgebraicGeometry.Scheme.ProEt.ClopenRoos.modulesAbelian
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived in
private theorem intrinsicComplete_iff (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (Y : Scheme.{u}) (K : DerivedCategory (scalarReductionSource l E Y)) :
    IsSfDerivedComplete l E Y K ↔ IntegralOnSlice.IsComplete l E Y none K := by
  change IsSfDerivedComplete l E Y K ↔ IsDerivedCompleteUnrestricted l E Y K
  constructor
  · intro hK
    let p := D.p
    let : Fact p.Prime := ⟨D.prime⟩
    let D₀ : FiniteFieldDatum.{0} :=
      { p := p
        a := 1
        q := p
        prime := D.prime
        exponent_pos := by decide
        cardinality_eq := by simp
        k₀ := ZMod p
        card_base := by simp [Nat.card_eq_fintype_card]
        k := AlgebraicClosure (ZMod p) }
    exact ⟨D₀, hl, (sfDerivedComplete_iff_legacy l E Y D₀ hl K).mp hK⟩
  · rintro ⟨D', hl', hK⟩
    exact (sfDerivedComplete_iff_legacy l E Y D' hl' K).mpr hK

private theorem torBounds_mono (Y : Scheme.{u}) (A : Type u) [CommRing A]
    (K : proEtaleDerivedCategory Y A) {a b c d : ℤ}
    (hab : HasProEtaleTorAmplitude Y A K a b) (hcd : c ≤ d)
    (hca : c ≤ a) (hbd : b ≤ d) : HasProEtaleTorAmplitude Y A K c d := by
  refine ⟨hcd, ?_⟩
  intro L Q e f hf hQ M m hm
  exact hab.2 L Q e f hf hQ M m (by rcases hm with h | h <;> omega)

attribute [-instance] AlgebraicGeometry.Scheme.ProEt.ClopenRoos.modulesAbelian
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived in
private theorem emptyIntegral_zero (Y : Scheme.{u}) [IsEmpty Y]
    (K : DerivedCategory (scalarReductionSource l E Y)) : IsZero K := by
  apply (DerivedCategory.isZero_iff K).mpr
  intro n
  exact ProEt.ClopenRoos.empty_modules_zero.{u, u + 1, u} Y
    (completedIntegralCoefficientSheafUnrestricted l E Y) _

variable (P : PurityFiniteSetting.{u})
  (X : Over (Spec (CommRingCat.of P.field.k)))
  [hft : LocallyOfFiniteType X.hom] [hqc : QuasiCompact X.hom]
  {I : Type w} [hfinite : Finite I]
  (Xi : I → Over (Spec (CommRingCat.of P.field.k))) (j : ∀ i, Xi i ⟶ X)
  [∀ i, IsOpenImmersion (j i).left] [hclosed : ∀ i, IsClosedImmersion (j i).left]
  (hdisjoint : ∀ i i', i ≠ i' →
    Disjoint (Set.range (j i).left) (Set.range (j i').left))
  (hcover : (⋃ i, Set.range (j i).left) = Set.univ)

include hft hqc hfinite hclosed hdisjoint hcover

set_option maxHeartbeats 800000 in
-- Elaborating the normalized scalar and localization comparisons requires extra heartbeats.
/-- Restriction preserves the chosen admissible resolution and the actual augmented
chain and derived reduction towers. The isomorphism of functors into the tower category
includes every transition equation and naturality on all derived morphisms.
Source: Bhatt--Scholze, Proposition 3.5.1(1) and Definition 3.5.2, p. 24
(blueprint: lem-pur-clopen-augmented-integral-descent).

Proof (node steps 1-2): the coefficient comparisons of
lem-pur-clopen-ringed-module-gluing preserve quotient projections, reductions and 1.
The exact tensor restriction of lem-pur-finite-product-derived-tensor-calculus preserves
quasi-isomorphisms, flat terms and K-flatness. Its sheafified tensor comparison sends
s tensor x to restricted s tensor restricted x. Taking s=1 proves the unit equation;
reducing s proves the transition equation. Localization and inversion of the image of
q give the equation for c_n. The derived scalar compositor descends this same chain
comparison to every derived morphism; lem-weil-integral-reduction-tower-well-defined
identifies both augmentation and transitions independently of the resolution. -/
theorem augmentedIntegralReductionComparison (i : I) :
    (∀ (T L : CochainComplex (scalarReductionSource P.coefficients.l
        P.extension X.left) ℤ) (q : T ⟶ L)
      (hq : CochainComplex.IsKFlatResolutionIndependentCoefficients
        (J := ProEt.topology X.left)
        (R := completedIntegralCommRingSheafUnrestricted P.coefficients.l P.extension X.left) q)
      (_hflat : ∀ m : ℤ, SheafOfModules.IsFlatOnSite
        (J := ProEt.topology X.left)
        (R := completedIntegralCommRingSheafUnrestricted P.coefficients.l P.extension X.left)
        (T.X m)),
      ∃ (hqr : CochainComplex.IsKFlatResolutionIndependentCoefficients
          (J := ProEt.topology (Xi i).left)
          (R := completedIntegralCommRingSheafUnrestricted
            P.coefficients.l P.extension (Xi i).left)
          ((clopenIntegralComplexRestriction P.coefficients.l P.extension (j i).left).map q))
        (β : ∀ n : ℕ,
          (clopenIntegralComplexRestriction P.coefficients.l P.extension (j i).left).obj
              (unrestrictedTowerComplex P.coefficients.l P.extension X.left n T) ≅
            unrestrictedTowerComplex P.coefficients.l P.extension (Xi i).left n
              ((clopenIntegralComplexRestriction P.coefficients.l P.extension (j i).left).obj T))
        (d : canonicalIntegralReductionTower P.coefficients.l P.extension X.left T ⋙
            clopenIntegralDerivedRestriction P.coefficients.l P.extension (j i).left ≅
          canonicalIntegralReductionTower P.coefficients.l P.extension (Xi i).left
            ((clopenIntegralComplexRestriction P.coefficients.l P.extension (j i).left).obj T)),
        (∀ m : ℤ, SheafOfModules.IsFlatOnSite
          (J := ProEt.topology (Xi i).left)
          (R := completedIntegralCommRingSheafUnrestricted
            P.coefficients.l P.extension (Xi i).left)
          (((clopenIntegralComplexRestriction P.coefficients.l P.extension
            (j i).left).obj T).X m)) ∧
        (∀ (n : ℕ) (m : ℤ) (U : (Xi i).left.ProEtᵒᵖ)
          (s : (integralCoefficientCommRingSheaf P.coefficients.l P.extension
            (Xi i).left n).obj.obj U)
          (x : (T.X m).val.obj ((clopenSiteInclusion (j i).left).op.obj U)),
          (((β n).hom.f m).val.app U)
            (unrestrictedTowerTensorSection P.coefficients.l P.extension X.left n
              (T.X m) ((clopenSiteInclusion (j i).left).op.obj U)
              ((clopenConstantMap (j i).left (CommRingCat.of
                (ULift.{u + 1} (Padic.coefficientExtensionRing P.coefficients.l
                  P.extension (n + 1))))).hom.app U s) x) =
          unrestrictedTowerTensorSection P.coefficients.l P.extension (Xi i).left n
            ((clopenIntegralModuleRestriction P.coefficients.l P.extension (j i).left).obj (T.X m))
            U s x) ∧
        (∀ n : ℕ,
          (clopenIntegralComplexRestriction P.coefficients.l P.extension (j i).left).map
              (unrestrictedTowerUnit P.coefficients.l P.extension X.left T n) ≫
            (β n).hom =
          unrestrictedTowerUnit P.coefficients.l P.extension (Xi i).left
            ((clopenIntegralComplexRestriction P.coefficients.l P.extension (j i).left).obj T)
            n) ∧
        (∀ n : ℕ,
          (clopenIntegralComplexRestriction P.coefficients.l P.extension (j i).left).map
              (unrestrictedTowerTransition P.coefficients.l P.extension X.left T n) ≫
            (β n).hom =
          (β (n + 1)).hom ≫ unrestrictedTowerTransition P.coefficients.l P.extension
            (Xi i).left
            ((clopenIntegralComplexRestriction P.coefficients.l P.extension (j i).left).obj T) n) ∧
        (∀ n : ℕ,
          d.hom.app (op n) =
            (clopenIntegralModuleRestriction P.coefficients.l P.extension
              (j i).left).mapDerivedCategoryFactors.hom.app
                (unrestrictedTowerComplex P.coefficients.l P.extension X.left n T) ≫
              DerivedCategory.Q.map ((β n).hom)) ∧
        (∀ n : ℕ,
          (clopenIntegralDerivedRestriction P.coefficients.l P.extension (j i).left).map
              (canonicalIntegralReductionTowerMap P.coefficients.l P.extension X.left q hq n) ≫
            d.hom.app (op n) =
          (clopenIntegralModuleRestriction P.coefficients.l P.extension
            (j i).left).mapDerivedCategoryFactors.hom.app L ≫
              canonicalIntegralReductionTowerMap P.coefficients.l P.extension (Xi i).left
                ((clopenIntegralComplexRestriction P.coefficients.l P.extension
                  (j i).left).map q) hqr n)) ∧
    (∃ β : clopenDerivedReductionFunctor P.coefficients.l P.extension X.left ⋙
          (Functor.whiskeringRight ℕᵒᵖ _ _).obj
            (clopenIntegralDerivedRestriction P.coefficients.l P.extension (j i).left) ≅
        clopenIntegralDerivedRestriction P.coefficients.l P.extension (j i).left ⋙
          clopenDerivedReductionFunctor P.coefficients.l P.extension (Xi i).left,
      ∀ (K : DerivedCategory (scalarReductionSource P.coefficients.l P.extension X.left))
        (n : ℕ),
        (clopenIntegralDerivedRestriction P.coefficients.l P.extension (j i).left).map
            ((sfDerivedReductionUnit P.coefficients.l P.extension X.left n).app K) ≫
          (β.hom.app K).app (op n) =
        (sfDerivedReductionUnit P.coefficients.l P.extension (Xi i).left n).app
          ((clopenIntegralDerivedRestriction P.coefficients.l P.extension (j i).left).obj K)) ∧
    (∀ n : ℕ, ∃
      (α : (scalarReductionExtension P.coefficients.l P.extension X.left n).mapHomologicalComplex
              (.up ℤ) ⋙
            (augmentedFiniteRestriction P.coefficients.l P.extension
              (j i).left n).mapHomologicalComplex (.up ℤ) ≅
          clopenIntegralComplexRestriction P.coefficients.l P.extension (j i).left ⋙
            (scalarReductionExtension P.coefficients.l P.extension
              (Xi i).left n).mapHomologicalComplex (.up ℤ))
      (δ : scalarReductionDerivedExtension P.coefficients.l P.extension X.left n ⋙
            augmentedFiniteDerivedRestriction P.coefficients.l P.extension (j i).left n ≅
          clopenIntegralDerivedRestriction P.coefficients.l P.extension (j i).left ⋙
            scalarReductionDerivedExtension P.coefficients.l P.extension (Xi i).left n),
      (∀ (T : CochainComplex (scalarReductionSource P.coefficients.l P.extension X.left) ℤ)
        (m : ℤ) (U : (Xi i).left.ProEtᵒᵖ)
        (s : (integralCoefficientCommRingSheaf P.coefficients.l P.extension
          (Xi i).left n).obj.obj U)
        (x : (T.X m).val.obj ((clopenSiteInclusion (j i).left).op.obj U)),
        (((α.hom.app T).f m).val.app U)
          (unrestrictedTowerTensorSection P.coefficients.l P.extension X.left n
            (T.X m) ((clopenSiteInclusion (j i).left).op.obj U)
            ((clopenConstantMap (j i).left (CommRingCat.of
              (ULift.{u + 1} (Padic.coefficientExtensionRing P.coefficients.l
                P.extension (n + 1))))).hom.app U s) x) =
        unrestrictedTowerTensorSection P.coefficients.l P.extension (Xi i).left n
          ((clopenIntegralModuleRestriction P.coefficients.l P.extension (j i).left).obj (T.X m))
          U s x) ∧
      ∀ (T L : CochainComplex (scalarReductionSource P.coefficients.l P.extension X.left) ℤ)
        (q : T ⟶ L)
        (hq : CochainComplex.IsKFlatResolutionIndependentCoefficients
          (J := ProEt.topology X.left)
          (R := completedIntegralCommRingSheafUnrestricted
            P.coefficients.l P.extension X.left) q)
        (_hflat : ∀ m : ℤ, SheafOfModules.IsFlatOnSite
          (J := ProEt.topology X.left)
          (R := completedIntegralCommRingSheafUnrestricted
            P.coefficients.l P.extension X.left) (T.X m))
        (hqr : CochainComplex.IsKFlatResolutionIndependentCoefficients
          (J := ProEt.topology (Xi i).left)
          (R := completedIntegralCommRingSheafUnrestricted
            P.coefficients.l P.extension (Xi i).left)
          ((clopenIntegralComplexRestriction P.coefficients.l P.extension (j i).left).map q)),
        (augmentedFiniteDerivedRestriction P.coefficients.l P.extension (j i).left n).map
            (unrestrictedTowerResolutionIso P.coefficients.l P.extension X.left n q hq).hom ≫
          (augmentedFiniteRestriction P.coefficients.l P.extension
            (j i).left n).mapDerivedCategoryFactors.hom.app
              (unrestrictedTowerFiniteComplex P.coefficients.l P.extension X.left n T) ≫
          DerivedCategory.Q.map (α.hom.app T) =
        δ.hom.app (DerivedCategory.Q.obj L) ≫
          (scalarReductionDerivedExtension P.coefficients.l P.extension (Xi i).left n).map
            ((clopenIntegralModuleRestriction P.coefficients.l P.extension
              (j i).left).mapDerivedCategoryFactors.hom.app L) ≫
          (unrestrictedTowerResolutionIso P.coefficients.l P.extension (Xi i).left n
            ((clopenIntegralComplexRestriction P.coefficients.l P.extension
              (j i).left).map q) hqr).hom) := by
  sorry

attribute [-instance] AlgebraicGeometry.Scheme.ProEt.ClopenRoos.modulesAbelian
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived in
omit hft hqc in
/-- Apply finite-clopen module gluing, normalized coefficient transport and exact
countable products before descending to derived categories. Source: Stacks 04TS,
07KC and 08TC (blueprint: lem-pur-clopen-augmented-integral-descent). -/
private theorem integralRoosCalculus :
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

attribute [local irreducible] clopenIntegralModuleRestriction clopenIntegralDerivedRestriction
  scalarReductionDerivedExtension completedIntegralCommRingSheafUnrestricted

set_option maxHeartbeats 800000 in
-- Elaborating the normalized scalar and localization comparisons requires extra heartbeats.
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.ClopenRoos.modulesAbelian
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived in
/-- Product and shift comparisons give a bijection on the connecting maps, and detect
the distinguishedness of the triangle whose first map is the actual quotient unit.
The product comparisons are normalized on every projection; β is a natural tower
isomorphism normalized on the augmentation, so no arbitrary replacement of c occurs.
Source: Bhatt--Scholze, Definition 3.5.2, p. 24; Stacks 08TC
(blueprint: lem-pur-clopen-augmented-integral-descent).

Proof (node step 3): apply lem-pur-clopen-strict-tower-roos-equivalence to the actual
quotient tower. The exact restriction equivalence preserves products and identifies
1-s coordinatewise. The fully faithful equivalence of
lem-pur-clopen-unbounded-derived-localization gives precisely the displayed Hom
bijection, conjugated by the product and shift isomorphisms. It preserves and reflects
distinguished triangles. Step 2 identifies the first arrow with the component unit.
For empty components every map is unique; the same argument includes an empty product
of component categories. No unique or canonical connecting map is asserted. -/
theorem augmentedIntegralRoosDescent
    (K : DerivedCategory (scalarReductionSource P.coefficients.l P.extension X.left)) :
    Nonempty (HasCountableProducts
      (DerivedCategory (scalarReductionSource P.coefficients.l P.extension X.left))) ∧
    (∀ i, Nonempty (HasCountableProducts
      (DerivedCategory (scalarReductionSource P.coefficients.l P.extension (Xi i).left)))) ∧
    ∀ [HasProduct (fun n : ℕ ↦
        (sfDerivedReductionRestricted P.coefficients.l P.extension X.left n).obj K)]
      [∀ i, HasProduct (fun n : ℕ ↦
        (sfDerivedReductionRestricted P.coefficients.l P.extension (Xi i).left n).obj
          ((clopenIntegralDerivedRestriction P.coefficients.l P.extension (j i).left).obj K))],
      ∃ α : ∀ i,
        (clopenIntegralDerivedRestriction P.coefficients.l P.extension (j i).left).obj
            (∏ᶜ fun n : ℕ ↦
              (sfDerivedReductionRestricted P.coefficients.l P.extension X.left n).obj K) ≅
          ∏ᶜ fun n : ℕ ↦
            (sfDerivedReductionRestricted P.coefficients.l P.extension (Xi i).left n).obj
              ((clopenIntegralDerivedRestriction P.coefficients.l P.extension (j i).left).obj K),
        (∃ β : ∀ i,
            clopenDerivedReductionFunctor P.coefficients.l P.extension X.left ⋙
                (Functor.whiskeringRight ℕᵒᵖ _ _).obj
                  (clopenIntegralDerivedRestriction P.coefficients.l P.extension (j i).left) ≅
              clopenIntegralDerivedRestriction P.coefficients.l P.extension (j i).left ⋙
                clopenDerivedReductionFunctor P.coefficients.l P.extension (Xi i).left,
          (∀ i (L : DerivedCategory (scalarReductionSource P.coefficients.l P.extension X.left))
            (n : ℕ),
            (clopenIntegralDerivedRestriction P.coefficients.l P.extension (j i).left).map
                ((sfDerivedReductionUnit P.coefficients.l P.extension X.left n).app L) ≫
              ((β i).hom.app L).app (op n) =
            (sfDerivedReductionUnit P.coefficients.l P.extension (Xi i).left n).app
              ((clopenIntegralDerivedRestriction P.coefficients.l P.extension (j i).left).obj L)) ∧
          ∀ i (n : ℕ),
            (α i).hom ≫ Pi.π _ n =
              (clopenIntegralDerivedRestriction P.coefficients.l P.extension (j i).left).map
                  (Pi.π _ n) ≫ ((β i).hom.app K).app (op n)) ∧
        Function.Bijective
          (fun δ : (∏ᶜ fun n : ℕ ↦
              (sfDerivedReductionRestricted P.coefficients.l P.extension X.left n).obj K) ⟶
                K⟦(1 : ℤ)⟧ ↦
            fun i ↦ (α i).inv ≫
              (clopenIntegralDerivedRestriction P.coefficients.l P.extension (j i).left).map δ ≫
              ((clopenIntegralDerivedRestriction P.coefficients.l P.extension
                (j i).left).commShiftIso (1 : ℤ)).hom.app K) ∧
        ∀ δ : (∏ᶜ fun n : ℕ ↦
            (sfDerivedReductionRestricted P.coefficients.l P.extension X.left n).obj K) ⟶
              K⟦(1 : ℤ)⟧,
          IsDerivedLimitTriangle
              (fun n ↦ (sfDerivedReductionTransition P.coefficients.l P.extension X.left n).app K)
              K (Pi.lift (fun n ↦
                (sfDerivedReductionUnit P.coefficients.l P.extension X.left n).app K)) δ ↔
            ∀ i, IsDerivedLimitTriangle
              (fun n ↦ (sfDerivedReductionTransition P.coefficients.l P.extension
                (Xi i).left n).app
                  ((clopenIntegralDerivedRestriction P.coefficients.l P.extension
                    (j i).left).obj K))
              ((clopenIntegralDerivedRestriction P.coefficients.l P.extension (j i).left).obj K)
              (Pi.lift (fun n ↦ (sfDerivedReductionUnit P.coefficients.l P.extension
                (Xi i).left n).app
                  ((clopenIntegralDerivedRestriction P.coefficients.l P.extension
                    (j i).left).obj K)))
              ((α i).inv ≫
                (clopenIntegralDerivedRestriction P.coefficients.l P.extension (j i).left).map δ ≫
                ((clopenIntegralDerivedRestriction P.coefficients.l P.extension
                  (j i).left).commShiftIso (1 : ℤ)).hom.app K) := by
  classical
  obtain ⟨hp, hpi, hEq, hd⟩ :=
    integralRoosCalculus P X Xi j hdisjoint hcover
  refine ⟨hp, hpi, ?_⟩
  intro _ _
  let r (i : I) := clopenIntegralDerivedRestriction.{u} P.coefficients.l P.extension (j i).left
  let F := Functor.pi' r
  let : F.IsEquivalence := hEq
  have hb (i : I) :=
    (augmentedIntegralReductionComparison P X Xi j hdisjoint hcover i).2.1
  choose β hβ using hb
  let A (n : ℕ) := (sfDerivedReductionRestricted P.coefficients.l P.extension X.left n).obj K
  let B (i : I) (n : ℕ) :=
    (sfDerivedReductionRestricted P.coefficients.l P.extension (Xi i).left n).obj ((r i).obj K)
  let e (i : I) (n : ℕ) : (r i).obj (A n) ≅ B i n := (β i).app K |>.app (op n)
  have (i : I) : HasProduct (fun n ↦ (r i).obj (A n)) :=
    hasLimit_of_iso (F := Discrete.functor (B i))
      (Discrete.natIso (fun n ↦ (e i n.as).symm))
  obtain ⟨φ, hφ, hdesc⟩ := hd A
  let α (i : I) := φ i ≪≫ productIso (e i)
  have hα (i : I) (n : ℕ) : (α i).hom ≫ Pi.π (B i) n =
      (r i).map (Pi.π A n) ≫ (e i n).hom := by
    simp only [α, Iso.trans_hom, Category.assoc, productIso, Pi.map_π]
    rw [← Category.assoc, hφ i, piComparison_comp_π]
  refine ⟨α, ⟨β, hβ, hα⟩, ?_, ?_⟩
  · constructor
    · intro δ ε h
      apply F.map_injective
      funext i
      have hi := congrFun h i
      apply (cancel_epi (α i).inv).mp
      apply (cancel_mono (((r i).commShiftIso (1 : ℤ)).hom.app K)).mp
      simpa only [r, F, Functor.pi'_map, Category.assoc] using hi
    · intro d
      let a : F.obj (∏ᶜ A) ⟶ F.obj (K⟦(1 : ℤ)⟧) :=
        fun i ↦ (α i).hom ≫ d i ≫ ((r i).commShiftIso (1 : ℤ)).inv.app K
      refine ⟨F.preimage a, ?_⟩
      funext i
      have h := congrFun (F.map_preimage a) i
      change (r i).map (F.preimage a) = a i at h
      change (α i).inv ≫ (r i).map (F.preimage a) ≫
        ((r i).commShiftIso (1 : ℤ)).hom.app K = d i
      rw [h]
      dsimp only [a]
      simp only [Category.assoc, Iso.inv_hom_id_app,
        Iso.inv_hom_id_assoc]
      exact Category.comp_id _
  · intro δ
    rw [hdesc]
    apply forall_congr'
    intro i
    let f (n : ℕ) := (r i).map
      ((sfDerivedReductionTransition P.coefficients.l P.extension X.left n).app K)
    let g (n : ℕ) :=
      (sfDerivedReductionTransition P.coefficients.l P.extension (Xi i).left n).app
        ((r i).obj K)
    have he (n : ℕ) : (e i (n + 1)).hom ≫ g n = f n ≫ (e i n).hom := by
      simpa only [clopenDerivedReductionFunctor, Functor.comp_obj,
        Functor.ofOpSequence_obj, Functor.flip_obj_map, Functor.ofOpSequence_map_homOfLE_succ,
        Functor.whiskeringRight_obj_obj, Functor.comp_map, Functor.flip_obj_obj,
        e, Iso.app_hom, f, g, r, A, B] using
        (((β i).hom.app K).naturality (homOfLE n.le_succ).op).symm
    have hc : (r i).map (Pi.lift (fun n ↦
          (sfDerivedReductionUnit P.coefficients.l P.extension X.left n).app K)) ≫
        (α i).hom = Pi.lift (fun n ↦
          (sfDerivedReductionUnit P.coefficients.l P.extension (Xi i).left n).app
            ((r i).obj K)) := by
      apply Pi.hom_ext
      intro n
      rw [Category.assoc, hα, ← Category.assoc, ← Functor.map_comp, Pi.lift_π,
        Pi.lift_π]
      exact hβ i K n
    have htrans := roosTransport (A := fun n ↦ (r i).obj (A n)) (B := B i)
      f g (e i) he ((r i).obj K)
      ((r i).map (Pi.lift (fun n ↦
        (sfDerivedReductionUnit P.coefficients.l P.extension X.left n).app K)) ≫ (φ i).hom)
      ((φ i).inv ≫ (r i).map δ ≫ ((r i).commShiftIso (1 : ℤ)).hom.app K)
    dsimp only [r] at hc
    have hc' : ((r i).map (Pi.lift (fun n ↦
        (sfDerivedReductionUnit P.coefficients.l P.extension X.left n).app K)) ≫
        (φ i).hom) ≫ (productIso (e i)).hom =
        Pi.lift (fun n ↦ (sfDerivedReductionUnit P.coefficients.l P.extension
          (Xi i).left n).app ((r i).obj K)) := by
      simpa only [α, Iso.trans_hom, Category.assoc] using hc
    have hc'' := congrArg (fun c ↦ IsDerivedLimitTriangle g ((r i).obj K) c
      ((productIso (e i)).inv ≫ (φ i).inv ≫ (r i).map δ ≫
        ((r i).commShiftIso (1 : ℤ)).hom.app K)) hc'
    have ht := htrans.trans (Iff.of_eq hc'')
    set_option backward.isDefEq.respectTransparency true in
    set_option backward.isDefEq.respectTransparency.types true in
    simp only [α, Iso.trans_inv, Category.assoc, f, g, r] at ht ⊢
    refine ht.trans ?_
    apply Iff.of_eq
    congr 1


set_option maxHeartbeats 800000 in
-- Elaborating the normalized scalar and localization comparisons requires extra heartbeats.
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.ClopenRoos.modulesAbelian
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived in
/-- Completeness, integral membership, and intervals uniform over every positive
reduction are detected on the components. Finite extrema give common intervals;
the same assertion allows every common larger interval. Empty components are zero,
and the empty partition has all three membership properties with interval [0,0].
Source: Bhatt--Scholze, Definition 3.5.2 and Proposition 3.5.1(1), p. 24
(blueprint: lem-pur-clopen-augmented-integral-descent).

Proof (node steps 4-7): a completing connecting map restricts to completing maps.
Conversely the Hom bijection in step 3 lifts any tuple of completing maps, and
reflection of distinguishedness gives completeness with the actual augmentation.
At each positive level apply lem-pur-clopen-finite-constructibility-bounds to the
reduction comparison: constructibility, support in a fixed interval and Tor amplitude
in a fixed interval are detected componentwise. Quantify over every level without
changing the interval. For a finite nonempty partition take the minimum of lower
bounds and maximum of upper bounds; containment of intervals preserves both vanishing
conditions. Combine completeness and the uniform bounds to obtain both integral
membership equivalences. On an empty component the derived category is zero. If the
partition is empty, covering forces X empty, and its zero objects meet completeness,
constructibility and every ordered support and Tor interval, in particular [0,0]. -/
theorem augmentedIntegralMembershipBounds
    (K : DerivedCategory (scalarReductionSource P.coefficients.l P.extension X.left)) :
    (IntegralOnSlice.IsComplete P.coefficients.l P.extension X.left none K ↔
      ∀ i, IntegralOnSlice.IsComplete P.coefficients.l P.extension (Xi i).left none
        ((clopenIntegralDerivedRestriction P.coefficients.l P.extension (j i).left).obj K)) ∧
    (sfIntegralConstructible P.coefficients.l P.extension X.left K ↔
      ∀ i, sfIntegralConstructible P.coefficients.l P.extension (Xi i).left
        ((clopenIntegralDerivedRestriction P.coefficients.l P.extension (j i).left).obj K)) ∧
    (finiteTorConstructibleIntegral P.coefficients.l P.extension X.left K ↔
      ∀ i, finiteTorConstructibleIntegral P.coefficients.l P.extension (Xi i).left
        ((clopenIntegralDerivedRestriction P.coefficients.l P.extension (j i).left).obj K)) ∧
    (∀ a b : ℤ, a ≤ b →
      ((∀ n : ℕ, Scheme.proEtaleCohomologicalSupport
          ((scalarReductionDerivedExtension P.coefficients.l P.extension X.left n).obj K) ⊆
            Set.Icc a b) ↔
        ∀ (i : I) (n : ℕ), Scheme.proEtaleCohomologicalSupport
          ((scalarReductionDerivedExtension P.coefficients.l P.extension (Xi i).left n).obj
            ((clopenIntegralDerivedRestriction P.coefficients.l P.extension (j i).left).obj K)) ⊆
              Set.Icc a b)) ∧
    (∀ a b : ℤ, a ≤ b →
      ((∀ n : ℕ, Scheme.HasProEtaleTorAmplitude X.left
          (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))
          ((scalarReductionDerivedExtension P.coefficients.l P.extension X.left n).obj K) a b) ↔
        ∀ (i : I) (n : ℕ), Scheme.HasProEtaleTorAmplitude (Xi i).left
          (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))
          ((scalarReductionDerivedExtension P.coefficients.l P.extension (Xi i).left n).obj
            ((clopenIntegralDerivedRestriction P.coefficients.l P.extension (j i).left).obj K))
          a b)) ∧
    (∀ a b : I → ℤ, (∀ i, a i ≤ b i) →
      (Nonempty I → ∃ A B : ℤ,
        (∃ i, A = a i) ∧ (∀ i, A ≤ a i) ∧
        (∃ i, B = b i) ∧ (∀ i, b i ≤ B) ∧ A ≤ B ∧
        ((∀ (i : I) (n : ℕ), proEtaleCohomologicalSupport
            ((scalarReductionDerivedExtension P.coefficients.l P.extension (Xi i).left n).obj
              ((clopenIntegralDerivedRestriction P.coefficients.l P.extension
                (j i).left).obj K)) ⊆ Set.Icc (a i) (b i)) →
          ∀ n : ℕ, proEtaleCohomologicalSupport
            ((scalarReductionDerivedExtension P.coefficients.l P.extension X.left n).obj K) ⊆
              Set.Icc A B) ∧
        ((∀ (i : I) (n : ℕ), HasProEtaleTorAmplitude (Xi i).left
            (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))
            ((scalarReductionDerivedExtension P.coefficients.l P.extension (Xi i).left n).obj
              ((clopenIntegralDerivedRestriction P.coefficients.l P.extension
                (j i).left).obj K)) (a i) (b i)) →
          ∀ n : ℕ, HasProEtaleTorAmplitude X.left
            (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))
            ((scalarReductionDerivedExtension P.coefficients.l P.extension X.left n).obj K) A B)) ∧
      ∀ A B : ℤ, A ≤ B → (∀ i, A ≤ a i) → (∀ i, b i ≤ B) →
        ((∀ (i : I) (n : ℕ), proEtaleCohomologicalSupport
            ((scalarReductionDerivedExtension P.coefficients.l P.extension (Xi i).left n).obj
              ((clopenIntegralDerivedRestriction P.coefficients.l P.extension
                (j i).left).obj K)) ⊆ Set.Icc (a i) (b i)) →
          ∀ n : ℕ, proEtaleCohomologicalSupport
            ((scalarReductionDerivedExtension P.coefficients.l P.extension X.left n).obj K) ⊆
              Set.Icc A B) ∧
        ((∀ (i : I) (n : ℕ), HasProEtaleTorAmplitude (Xi i).left
            (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))
            ((scalarReductionDerivedExtension P.coefficients.l P.extension (Xi i).left n).obj
              ((clopenIntegralDerivedRestriction P.coefficients.l P.extension
                (j i).left).obj K)) (a i) (b i)) →
          ∀ n : ℕ, HasProEtaleTorAmplitude X.left
            (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))
            ((scalarReductionDerivedExtension P.coefficients.l P.extension X.left n).obj K) A B)) ∧
    (∀ i, IsEmpty (Xi i).left → ∀ L : DerivedCategory
        (scalarReductionSource P.coefficients.l P.extension (Xi i).left), IsZero L) ∧
    (IsEmpty I → IsEmpty X.left ∧
      (∀ L : DerivedCategory (scalarReductionSource P.coefficients.l P.extension X.left),
        IsZero L) ∧
      IntegralOnSlice.IsComplete P.coefficients.l P.extension X.left none K ∧
      sfIntegralConstructible P.coefficients.l P.extension X.left K ∧
      finiteTorConstructibleIntegral P.coefficients.l P.extension X.left K ∧
      (∀ n : ℕ, proEtaleCohomologicalSupport
        ((scalarReductionDerivedExtension P.coefficients.l P.extension X.left n).obj K) ⊆
          Set.Icc 0 0) ∧
      (∀ n : ℕ, HasProEtaleTorAmplitude X.left
        (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))
        ((scalarReductionDerivedExtension P.coefficients.l P.extension X.left n).obj K) 0 0)) := by
  classical
  let r (i : I) := clopenIntegralDerivedRestriction P.coefficients.l P.extension (j i).left
  have hlevel (n : ℕ) :=
    integralReductionFiniteClopenBounds P X Xi j hdisjoint hcover K n
  have hs (a b : ℤ) (hab : a ≤ b) :
      (∀ n : ℕ, proEtaleCohomologicalSupport
        ((scalarReductionDerivedExtension P.coefficients.l P.extension X.left n).obj K) ⊆
          Set.Icc a b) ↔
      ∀ (i : I) (n : ℕ), proEtaleCohomologicalSupport
        ((scalarReductionDerivedExtension P.coefficients.l P.extension (Xi i).left n).obj
          ((r i).obj K)) ⊆ Set.Icc a b := by
    constructor
    · intro h i n
      exact ((hlevel n).2.1 a b hab).mp (h n) i
    · intro h n
      exact ((hlevel n).2.1 a b hab).mpr (fun i ↦ h i n)
  have ht (a b : ℤ) (hab : a ≤ b) :
      (∀ n : ℕ, HasProEtaleTorAmplitude X.left
        (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))
        ((scalarReductionDerivedExtension P.coefficients.l P.extension X.left n).obj K) a b) ↔
      ∀ (i : I) (n : ℕ), HasProEtaleTorAmplitude (Xi i).left
        (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))
        ((scalarReductionDerivedExtension P.coefficients.l P.extension (Xi i).left n).obj
          ((r i).obj K)) a b := by
    constructor
    · intro h i n
      exact ((hlevel n).2.2 a b hab).mp (h n) i
    · intro h n
      exact ((hlevel n).2.2 a b hab).mpr (fun i ↦ h i n)
  have hc : IsSfDerivedComplete P.coefficients.l P.extension X.left K ↔
      ∀ i, IsSfDerivedComplete P.coefficients.l P.extension (Xi i).left ((r i).obj K) := by
    obtain ⟨⟨hp⟩, hpi, hd⟩ := augmentedIntegralRoosDescent P X Xi j hdisjoint hcover K
    let := hp
    let hp' (i : I) := (hpi i).some
    let : ∀ i, HasCountableProducts
        (DerivedCategory (scalarReductionSource P.coefficients.l P.extension (Xi i).left)) := hp'
    obtain ⟨α, _, hb, hδ⟩ := hd
    constructor
    · rintro ⟨_, δ, hδK⟩ i
      exact ⟨inferInstance, _, (hδ δ).mp hδK i⟩
    · intro h
      choose hp δ hh using h
      obtain ⟨δ', hδ'⟩ := hb.surjective δ
      refine ⟨inferInstance, δ', (hδ δ').mpr ?_⟩
      intro i
      simpa only [congrFun hδ' i] using hh i
  have hext (a b : I → ℤ) (hab : ∀ i, a i ≤ b i) [Nonempty I] :
      ∃ A B : ℤ, (∃ i, A = a i) ∧ (∀ i, A ≤ a i) ∧
        (∃ i, B = b i) ∧ (∀ i, b i ≤ B) ∧ A ≤ B := by
    obtain ⟨i, hi⟩ := Finite.exists_min a
    obtain ⟨k, hk⟩ := Finite.exists_max b
    exact ⟨a i, b k, ⟨i, rfl⟩, hi, ⟨k, rfl⟩, hk, (hab i).trans (hk i)⟩
  have hsMono (a b : I → ℤ) (A B : ℤ) (hAB : A ≤ B)
      (ha : ∀ i, A ≤ a i) (hb : ∀ i, b i ≤ B) :
      (∀ (i : I) (n : ℕ), proEtaleCohomologicalSupport
        ((scalarReductionDerivedExtension P.coefficients.l P.extension (Xi i).left n).obj
          ((r i).obj K)) ⊆ Set.Icc (a i) (b i)) →
      ∀ n : ℕ, proEtaleCohomologicalSupport
        ((scalarReductionDerivedExtension P.coefficients.l P.extension X.left n).obj K) ⊆
          Set.Icc A B := by
    intro h
    apply (hs A B hAB).mpr
    intro i n m hm
    exact ⟨(ha i).trans (h i n hm).1, (h i n hm).2.trans (hb i)⟩
  have htMono (a b : I → ℤ) (A B : ℤ) (hAB : A ≤ B)
      (ha : ∀ i, A ≤ a i) (hb : ∀ i, b i ≤ B) :
      (∀ (i : I) (n : ℕ), HasProEtaleTorAmplitude (Xi i).left
        (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))
        ((scalarReductionDerivedExtension P.coefficients.l P.extension (Xi i).left n).obj
          ((r i).obj K)) (a i) (b i)) →
      ∀ n : ℕ, HasProEtaleTorAmplitude X.left
        (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))
        ((scalarReductionDerivedExtension P.coefficients.l P.extension X.left n).obj K) A B := by
    intro h
    apply (ht A B hAB).mpr
    intro i n
    exact torBounds_mono _ _ _ (h i n) hAB (ha i) (hb i)
  have hcst : sfIntegralConstructible P.coefficients.l P.extension X.left K ↔
      ∀ i, sfIntegralConstructible P.coefficients.l P.extension (Xi i).left ((r i).obj K) := by
    constructor
    · rintro ⟨hK, a, b, hab, hn⟩ i
      refine ⟨hc.mp hK i, a, b, hab, ?_⟩
      intro n
      exact ⟨(hlevel n).1.mp (hn n).1 i, (hs a b hab).mp (fun n ↦ (hn n).2) i n⟩
    · intro h
      refine ⟨hc.mpr (fun i ↦ (h i).1), ?_⟩
      by_cases hi : Nonempty I
      · let := hi
        choose a b hab hn using fun i ↦ (h i).2
        obtain ⟨A, B, _, hA, _, hB, hAB⟩ := hext a b hab
        refine ⟨A, B, hAB, fun n ↦ ⟨?_, ?_⟩⟩
        · exact (hlevel n).1.mpr (fun i ↦ (hn i n).1)
        · exact hsMono a b A B hAB hA hB (fun i n ↦ (hn i n).2) n
      · have : IsEmpty I := not_nonempty_iff.mp hi
        exact ⟨0, 0, le_refl _, fun n ↦
          ⟨(hlevel n).1.mpr (fun i ↦ isEmptyElim i),
            (hs 0 0 (le_refl _)).mpr (fun i ↦ isEmptyElim i) n⟩⟩
  have hctf : finiteTorConstructibleIntegral P.coefficients.l P.extension X.left K ↔
      ∀ i, finiteTorConstructibleIntegral P.coefficients.l P.extension (Xi i).left
        ((r i).obj K) := by
    constructor
    · rintro ⟨hK, a, b, hab, hn⟩ i
      exact ⟨hcst.mp hK i, a, b, hab, (ht a b hab).mp hn i⟩
    · intro h
      refine ⟨hcst.mpr (fun i ↦ (h i).1), ?_⟩
      by_cases hi : Nonempty I
      · let := hi
        choose a b hab hn using fun i ↦ (h i).2
        obtain ⟨A, B, _, hA, _, hB, hAB⟩ := hext a b hab
        exact ⟨A, B, hAB, htMono a b A B hAB hA hB hn⟩
      · have : IsEmpty I := not_nonempty_iff.mp hi
        exact ⟨0, 0, le_refl _, (ht 0 0 (le_refl _)).mpr (fun i ↦ isEmptyElim i)⟩
  refine ⟨?_, hcst, hctf, hs, ht, ?_, ?_, ?_⟩
  · rw [← intrinsicComplete_iff _ _ P.field P.coefficients.different]
    exact hc.trans (forall_congr' (fun i ↦
      intrinsicComplete_iff _ _ P.field P.coefficients.different _ _))
  · intro a b hab
    refine ⟨?_, fun A B hAB hA hB ↦
      ⟨hsMono a b A B hAB hA hB, htMono a b A B hAB hA hB⟩⟩
    intro hi
    let := hi
    obtain ⟨A, B, ha, hA, hb, hB, hAB⟩ := hext a b hab
    exact ⟨A, B, ha, hA, hb, hB, hAB,
      hsMono a b A B hAB hA hB, htMono a b A B hAB hA hB⟩
  · intro i hi L
    let := hi
    exact emptyIntegral_zero _ _ _ L
  · intro hi
    let := hi
    have hX : IsEmpty X.left := ⟨fun x ↦ by
      obtain ⟨i, _⟩ := Set.mem_iUnion.mp (hcover.symm ▸ Set.mem_univ x)
      exact isEmptyElim i⟩
    let := hX
    refine ⟨hX, fun L ↦ emptyIntegral_zero _ _ _ L, ?_, ?_, ?_, ?_, ?_⟩
    · exact (intrinsicComplete_iff _ _ P.field P.coefficients.different _ _).mp
        (hc.mpr (fun i ↦ isEmptyElim i))
    · exact hcst.mpr (fun i ↦ isEmptyElim i)
    · exact hctf.mpr (fun i ↦ isEmptyElim i)
    · exact (hs 0 0 (le_refl _)).mpr (fun i ↦ isEmptyElim i)
    · exact (ht 0 0 (le_refl _)).mpr (fun i ↦ isEmptyElim i)


end WeilConjectures.PurityFiniteSetting
