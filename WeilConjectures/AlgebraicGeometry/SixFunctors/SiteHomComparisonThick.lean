/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SixFunctors.EvaluationHomSiteComparison
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.AlgebraicGeometry.Support.SupportComparisonPullbackCoherence
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatWeaklyEtale
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralResidueDerivedMonoidal
public import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.CategoryTheory.ObjectProperty.Retract
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.CategoryTheory.Exact.ExactClosedDerivedHom
public import WeilConjectures.AlgebraicGeometry.Native.NativeDerivedHomSignedExact
import WeilConjectures.CategoryTheory.Exact.ExactDerivedHomComparisonShift
import WeilConjectures.CategoryTheory.SixFunctors.ContravariantIsoLocus
import all WeilConjectures.CategoryTheory.Exact.ExactClosedDerivedHom
import all WeilConjectures.CategoryTheory.Exact.ExactDerivedTensorSquare
import WeilConjectures.SixFunctors.ProEtale.Comparison.Monoidal
import WeilConjectures.SixFunctors.ProEtale.BaseChange.WeaklyEtaleDerived
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.InternalHom
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.InternalHom
import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMapProjection

/-! # Exactness and thick locus of the specified site Hom comparison

Source: blueprint, lem-weil-finite-duality-site-comparison, proof paragraphs 1--2;
Stacks Project, Tags 08J9, 08JB and 08JC
(blueprint: lem-sf-site-hom-comparison-thick).

The map is the recorded evaluation transpose. The shift structures below are normalized
by the adjunction mate of total-tensor shifts and the signed opposite-category convention.
## Main declarations

* `siteHomComparison_exact_thick`: exactness, signed naturality and thick closure.
* `siteHomComparison_restriction`: the canonical equation on every etale slice.
* The other declarations construct their canonical functors, shifts and maps.

Restrictions are exact inverse image along an etale object, canonically identified with
slice restriction. Every comparison is constructed from the existing adjunctions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxSize 2048
universe u v d e d₁ e₁
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open CategoryTheory.Pretriangulated CategoryTheory.Pretriangulated.Opposite

namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] Functor.mapDerivedCategory

/-- The structure morphism of an etale object, with its source and target explicit.
This is exactly U.hom; the alias keeps slice-object wrappers out of inferred functor
parameters. Source: Stacks 08JB (blueprint: lem-sf-site-hom-comparison-thick). -/
abbrev siteHomEtaleObjectHom (X : Scheme.{u}) (U : X.Etale) : U.left ⟶ X :=
  U.hom

/-- Derive the ordinary tensor comparison and transport it to the exact termwise
functor. This packages the existing construction without selecting new tensor data.
Source: Stacks 07A4 (blueprint: lem-sf-site-hom-comparison-thick). -/
@[irreducible] def siteHomExactDerivedMonoidal
    {C : Type d} [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C]
    [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    {D : Type e} [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D] [MonoidalCategory D]
    [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
    [Abelian.HasFunctorialFlatResolution D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.PreservesFlat] [F.IsLeftAdjoint] [F.Monoidal] :
    F.mapDerivedCategory.Monoidal :=
  Functor.exactClosedDerivedMonoidal F

private theorem isIso_exactDerivedHom
    {C : Type d} [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C]
    [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    {D : Type e} [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D] [MonoidalCategory D]
    [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
    [Abelian.HasFunctorialFlatResolution D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.PreservesFlat] [F.IsLeftAdjoint] [F.Monoidal]
    {L : D ⥤ C} [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (a : L ⊣ F) [∀ K : C, IsIso (Functor.LaxMonoidal.ihomComparison F K).natTrans]
    (K M : DerivedCategory C) :
    letI := siteHomExactDerivedMonoidal F
    IsIso (Functor.closedComparison F.mapDerivedCategory K M) := by
  unfold siteHomExactDerivedMonoidal
  exact Functor.isIso_closedComparison_exactDerived F a K M

/-- Assemble the canonical evaluation transpose for Etale derived inverse image.
The monoidal structure is an explicit parameter so specialization uses exactly the
canonical derived tensor comparison. Source: Stacks 08JB, 07A4
(blueprint: lem-sf-site-hom-comparison-thick). -/
@[irreducible] def siteHomEtaleRestrictionEvaluation
    (B : Type (u + 2)) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B]
    [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
    [Abelian.HasFunctorialFlatResolution B]
    {Y X : Scheme.{u}} (f : Y ⟶ X)
    (m : (Etale.upperStar B f).mapDerivedCategory.Monoidal)
    (K M : DerivedCategory (Sheaf (X.smallEtaleTopology) B)) :
    (Etale.upperStar B f).mapDerivedCategory.obj
        (((Etale.derivedHom B X).obj (op K)).obj M) ⟶
      ((Etale.derivedHom B Y).obj
        (op ((Etale.upperStar B f).mapDerivedCategory.obj K))).obj
          ((Etale.upperStar B f).mapDerivedCategory.obj M) :=
  let F := (Etale.upperStar B f).mapDerivedCategory
  let _ : F.Monoidal := m
  Functor.closedComparison F K M

/-- Assemble the canonical evaluation transpose for ProEtale derived inverse image.
The monoidal structure is an explicit parameter so specialization uses exactly the
canonical derived tensor comparison. Source: Stacks 08JB, 07A4
(blueprint: lem-sf-site-hom-comparison-thick). -/
@[irreducible] def siteHomProEtaleRestrictionEvaluation
    (B : Type (u + 2)) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B]
    [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
    [Abelian.HasFunctorialFlatResolution B]
    {Y X : Scheme.{u}} (f : Y ⟶ X)
    (m : (upperStar B f).mapDerivedCategory.Monoidal)
    (K M : DerivedCategory (Sheaf (Scheme.ProEt.topology X) B)) :
    (upperStar B f).mapDerivedCategory.obj
        (((derivedHom B X).obj (op K)).obj M) ⟶
      ((derivedHom B Y).obj
        (op ((upperStar B f).mapDerivedCategory.obj K))).obj
          ((upperStar B f).mapDerivedCategory.obj M) :=
  let F := (upperStar B f).mapDerivedCategory
  let _ : F.Monoidal := m
  Functor.closedComparison F K M

/-- The complete exactness and thick-locus assertion for a specified closed-category
comparison. This is a transparent proposition, not an extra hypothesis or chosen map.
It uses the canonical signed source shifts on both rows. Source: Stacks 08JC
(blueprint: lem-sf-site-hom-comparison-thick). -/
@[irreducible] def siteHomExactThickAssertion
    {C : Type d} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [MonoidalCategory C] [MonoidalClosed C] [(curriedTensor C).CommShift₂Int]
    {D : Type e} [Category.{v} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    [MonoidalCategory D] [MonoidalClosed D] [(curriedTensor D).CommShift₂Int]
    (F : C ⥤ D) [F.CommShift ℤ]
    (b : ∀ K M : C, F.obj ((ihom K).obj M) ⟶ (ihom (F.obj K)).obj (F.obj M))
    (M : C) : Prop :=
  let B := MonoidalClosed.internalHom.flip.obj M ⋙ F
  let E := F.op ⋙ MonoidalClosed.internalHom.flip.obj (F.obj M)
  let P : ObjectProperty C := fun K ↦ IsIso (b K M)
  ∃ (sB : B.CommShift ℤ) (sE : E.CommShift ℤ) (β : B ⟶ E),
    (∀ K : C, β.app (op K) = b K M) ∧
    (fun [_sB : B.CommShift ℤ] [_sE : E.CommShift ℤ] ↦
      B.IsTriangulated ∧ E.IsTriangulated ∧ NatTrans.CommShift β ℤ ∧
      (∀ (K : C) (n : ℤ), (B.commShiftIso n).hom.app (op K) =
        (n * (n + 1) / 2).negOnePow •
          (F.map ((siteHomOppositeSourceShift K n).hom.app M) ≫
            (F.commShiftIso n).hom.app ((ihom K).obj M))) ∧
      (∀ (K : C) (n : ℤ), (E.commShiftIso n).hom.app (op K) =
        (n * (n + 1) / 2).negOnePow •
          ((MonoidalClosed.internalHom.map ((F.commShiftIso (-n)).inv.app K).op).app
              (F.obj M) ≫
            (siteHomOppositeSourceShift (F.obj K) n).hom.app (F.obj M))) ∧
      (∀ T : Triangle C, T ∈ distTriang C →
        ∃ φ : B.mapTriangle.obj ((triangleOpEquivalence C).functor.obj (op T)) ⟶
          E.mapTriangle.obj ((triangleOpEquivalence C).functor.obj (op T)),
          φ.hom₁ = β.app (op T.obj₃) ∧ φ.hom₂ = β.app (op T.obj₂) ∧
            φ.hom₃ = β.app (op T.obj₁))) (_sB := sB) (_sE := sE) ∧
    P.IsTriangulated ∧ P.IsStableUnderRetracts

private theorem exactThickAssertion_of_signed
    {C : Type d} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [MonoidalCategory C] [MonoidalClosed C] [(curriedTensor C).CommShift₂Int]
    {D : Type e} [Category.{v} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    [MonoidalCategory D] [MonoidalClosed D] [(curriedTensor D).CommShift₂Int]
    (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated] [F.Additive]
    (M : C)
    [sH : (MonoidalClosed.internalHom.flip.obj M).CommShift ℤ]
    [sJ : (MonoidalClosed.internalHom.flip.obj (F.obj M)).CommShift ℤ]
    [(MonoidalClosed.internalHom.flip.obj M).IsTriangulated]
    [(MonoidalClosed.internalHom.flip.obj (F.obj M)).IsTriangulated]
    (hsH : ∀ K n,
      ((MonoidalClosed.internalHom.flip.obj M).commShiftIso n).hom.app (op K) =
        (n * (n + 1) / 2).negOnePow • (siteHomOppositeSourceShift K n).hom.app M)
    (hsJ : ∀ K n,
      ((MonoidalClosed.internalHom.flip.obj (F.obj M)).commShiftIso n).hom.app (op K) =
        (n * (n + 1) / 2).negOnePow •
          (siteHomOppositeSourceShift K n).hom.app (F.obj M))
    (b : ∀ K M : C, F.obj ((ihom K).obj M) ⟶ (ihom (F.obj K)).obj (F.obj M))
    (β : MonoidalClosed.internalHom.flip.obj M ⋙ F ⟶
      F.op ⋙ MonoidalClosed.internalHom.flip.obj (F.obj M))
    [NatTrans.CommShift β ℤ] (hβ : ∀ K, β.app (op K) = b K M) :
    siteHomExactThickAssertion F b M := by
  let B := MonoidalClosed.internalHom.flip.obj M ⋙ F
  let E := F.op ⋙ MonoidalClosed.internalHom.flip.obj (F.obj M)
  unfold siteHomExactThickAssertion
  dsimp only
  refine ⟨inferInstanceAs (B.CommShift ℤ), inferInstanceAs (E.CommShift ℤ), β, ?_, ?_, ?_⟩
  · intro K
    exact hβ K
  · refine ⟨inferInstanceAs B.IsTriangulated, inferInstanceAs E.IsTriangulated,
      inferInstanceAs (NatTrans.CommShift β ℤ), ?_, ?_, ?_⟩
    · intro K n
      change (B.commShiftIso n).hom.app (op K) = _
      rw [Functor.commShiftIso_comp_hom_app, hsH]
      simp only [Functor.map_units_smul, Linear.units_smul_comp]
      rfl
    · intro K n
      change (E.commShiftIso n).hom.app (op K) = _
      rw [Functor.commShiftIso_comp_hom_app]
      have hFop : (F.op.commShiftIso n).hom.app (op K) =
          ((F.commShiftIso (-n)).inv.app K).op := by
        rw [Functor.op_commShiftIso_hom_app F (op K) n (-n) (add_neg_cancel n)]
        change (F.map (𝟙 _)).op ≫ _ ≫ 𝟙 _ = _
        rw [F.map_id, op_id, Category.id_comp, Category.comp_id]
      rw [hFop]
      rw [hsJ]
      simp only [Linear.comp_units_smul]
      rfl
    · intro T _
      exact ⟨(NatTrans.mapTriangle β).app
        ((triangleOpEquivalence _).functor.obj (op T)), rfl, rfl, rfl⟩
  · simpa only [hβ] using contravariantComparison_isoLocus β

private theorem exactThickAssertion_of_exactFunctor
    {C : Type d} [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C]
    [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    {D : Type e} [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D] [MonoidalCategory D]
    [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
    [Abelian.HasFunctorialFlatResolution D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.PreservesFlat] [F.IsLeftAdjoint] [F.Monoidal] (M : DerivedCategory C)
    (b : ∀ K M : DerivedCategory C,
      F.mapDerivedCategory.obj ((ihom K).obj M) ⟶
        (ihom (F.mapDerivedCategory.obj K)).obj (F.mapDerivedCategory.obj M))
    (hb : letI := Functor.exactClosedDerivedMonoidal F
      ∀ K N, b K N = Functor.closedComparison F.mapDerivedCategory K N) :
    siteHomExactThickAssertion F.mapDerivedCategory b M := by
  let G := F.mapDerivedCategory
  let H := MonoidalClosed.internalHom.flip.obj M
  let J := MonoidalClosed.internalHom.flip.obj (G.obj M)
  letI := Functor.exactClosedDerivedMonoidal F
  let β : H ⋙ G ⟶ G.op ⋙ J :=
    { app := fun K ↦ Functor.closedComparison G K.unop M
      naturality := fun K L f ↦ by
        unfold Functor.closedComparison
        exact Functor.LaxMonoidal.map_pre_app_comp_ihomComparison_app G f.unop M }
  obtain ⟨sH, hH, hsH⟩ := nativeDerivedHom_signed_exact M
  obtain ⟨sJ, hJ, hsJ⟩ := nativeDerivedHom_signed_exact (G.obj M)
  letI := sH
  letI := sJ
  haveI : H.IsTriangulated := hH
  haveI : J.IsTriangulated := hJ
  haveI : NatTrans.CommShift β ℤ :=
    Functor.exactDerivedHomComparison_shift F M sH sJ hsH hsJ β (fun _ ↦ rfl)
  exact exactThickAssertion_of_signed G M hsH hsJ b β (fun K ↦ (hb K M).symm)

/-- Specialize the transparent assertion to the actual site evaluation comparison.
Abstracting the coefficient category keeps the canonical structures compact in kernel
checking. Source: blueprint comparison proof, paragraph 2
(blueprint: lem-sf-site-hom-comparison-thick). -/
@[irreducible] def siteHomSiteExactThick
    (B : Type (u + 2)) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B]
    [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
    [Abelian.HasFunctorialFlatResolution B]
    (X : Scheme.{u}) [(comparisonUpperStar B X).PreservesFlat]
    (M : DerivedCategory (Sheaf X.smallEtaleTopology B)) : Prop :=
  siteHomExactThickAssertion (comparisonUpperStar B X).mapDerivedCategory
    (siteComparisonEvaluationHom B X) M

/-- Canonical inverse-image comparison on the derived restriction square: localize the
ordinary adjunction-mate comparison, using exact-functor composition comparisons.
Source: Stacks 00WX, 08JB (blueprint: lem-sf-site-hom-comparison-thick). -/
def siteHomRestrictionSquareFor
    (B : Type (u + 2)) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B]
    [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
    [Abelian.HasFunctorialFlatResolution B]
    {Y X : Scheme.{u}} (f : Y ⟶ X) :
    (Etale.upperStar B f).mapDerivedCategory ⋙
        (comparisonUpperStar B Y).mapDerivedCategory ≅
      (comparisonUpperStar B X).mapDerivedCategory ⋙
        (upperStar B f).mapDerivedCategory :=
  let e : Etale.upperStar B f ⋙
      comparisonUpperStar B Y ≅
    comparisonUpperStar B X ⋙
      upperStar B f :=
    supportSiteComparisonCoefficientPullbackIso B f
  (Functor.mapDerivedCategoryCompIso
      (Etale.upperStar B f)
      (comparisonUpperStar B Y)).symm ≪≫
    Functor.mapDerivedCategoryNatIso e ≪≫
    Functor.mapDerivedCategoryCompIso
      (comparisonUpperStar B X)
      (upperStar B f)

/-- A comparison square for four closed categories, retaining the actual component
maps and the inverse-image comparison. This proposition is instantiated below by the
canonical evaluation transposes, not by arbitrary witnesses. Source: Stacks 08JB
(blueprint: lem-sf-site-hom-comparison-thick). -/
def siteHomRestrictionSquareAssertion
    {C : Type d} [Category.{v} C] {C₁ : Type d₁} [Category.{v} C₁]
    {D : Type e} [Category.{v} D] {D₁ : Type e₁} [Category.{v} D₁]
    (H : Cᵒᵖ ⥤ C ⥤ C) (H₁ : C₁ᵒᵖ ⥤ C₁ ⥤ C₁)
    (G : Dᵒᵖ ⥤ D ⥤ D) (G₁ : D₁ᵒᵖ ⥤ D₁ ⥤ D₁)
    (F : C ⥤ D) (F₁ : C₁ ⥤ D₁) (r_e : C ⥤ C₁) (r_p : D ⥤ D₁)
    (θ : r_e ⋙ F₁ ≅ F ⋙ r_p)
    (b : ∀ K M : C, F.obj ((H.obj (op K)).obj M) ⟶
      (G.obj (op (F.obj K))).obj (F.obj M))
    (b₁ : ∀ K M : C₁, F₁.obj ((H₁.obj (op K)).obj M) ⟶
      (G₁.obj (op (F₁.obj K))).obj (F₁.obj M))
    (h_e : ∀ K M : C, r_e.obj ((H.obj (op K)).obj M) ⟶
      (H₁.obj (op (r_e.obj K))).obj (r_e.obj M))
    (h_p : ∀ K M : D, r_p.obj ((G.obj (op K)).obj M) ⟶
      (G₁.obj (op (r_p.obj K))).obj (r_p.obj M)) (K M : C) : Prop :=
  IsIso (h_e K M) ∧ IsIso (h_p (F.obj K) (F.obj M)) ∧
    F₁.map (h_e K M) ≫ b₁ (r_e.obj K) (r_e.obj M) ≫
      (G₁.map (θ.inv.app K).op).app (F₁.obj (r_e.obj M)) ≫
      (G₁.obj (op (r_p.obj (F.obj K)))).map (θ.hom.app M) =
    θ.hom.app ((H.obj (op K)).obj M) ≫ r_p.map (b K M) ≫ h_p (F.obj K) (F.obj M)

/-- The evaluation-normalized restriction assertion, before coefficient specialization.
Its two monoidal arguments will be instantiated by the canonical derived tensor
structures. The proposition spells out both Hom restriction isomorphisms and the
comparison equation. Source: Stacks 08JB, 07A4
(blueprint: lem-sf-site-hom-comparison-thick). -/
def siteHomRestrictionAssertion
    (B : Type (u + 2)) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B]
    [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
    [Abelian.HasFunctorialFlatResolution B]
    {Y X : Scheme.{u}} (f : Y ⟶ X)
    [(comparisonUpperStar B X).PreservesFlat]
    [(comparisonUpperStar B Y).PreservesFlat]
    (m_e : (Etale.upperStar B f).mapDerivedCategory.Monoidal)
    (m_p : (upperStar B f).mapDerivedCategory.Monoidal)
    (K M : DerivedCategory (Sheaf X.smallEtaleTopology B)) : Prop :=
  siteHomRestrictionSquareAssertion
    (Etale.derivedHom B X) (Etale.derivedHom B Y)
    (derivedHom B X) (derivedHom B Y)
    (comparisonUpperStar B X).mapDerivedCategory
    (comparisonUpperStar B Y).mapDerivedCategory
    (Etale.upperStar B f).mapDerivedCategory (upperStar B f).mapDerivedCategory
    (siteHomRestrictionSquareFor B f)
    (siteComparisonEvaluationHom B X) (siteComparisonEvaluationHom B Y)
    (siteHomEtaleRestrictionEvaluation B f m_e)
    (siteHomProEtaleRestrictionEvaluation B f m_p) K M

private theorem etaleRestriction_isIso
    (B : Type (u + 2)) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B]
    [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
    [Abelian.HasFunctorialFlatResolution B]
    {Y X : Scheme.{u}} (f : Y ⟶ X) [Etale f] [(Etale.upperStar B f).PreservesFlat]
    (K M : DerivedCategory (Sheaf X.smallEtaleTopology B)) :
    IsIso (siteHomEtaleRestrictionEvaluation B f
      (siteHomExactDerivedMonoidal (Etale.upperStar B f)) K M) := by
  let L := Etale.etaleLowerShriek B f inferInstance
  let a : L ⊣ Etale.upperStar B f :=
    Etale.etaleLowerShriekUpperStarAdjunction B f inferInstance
  have : PreservesFiniteLimits L :=
    Etale.preservesFiniteLimits_etaleLowerShriek_of_hasSmallSiteSheafify B f inferInstance
  have : L.Additive := a.left_adjoint_additive
  have := a.leftAdjoint_preservesColimits
  have : PreservesFiniteColimits L :=
    PreservesColimitsOfSize.preservesFiniteColimits.{u + 1, u + 1} L
  have (P : Sheaf X.smallEtaleTopology B) :
      IsIso (Functor.LaxMonoidal.ihomComparison (Etale.upperStar B f) P).natTrans :=
    Etale.isIso_ihomComparison_upperStar B f P
  unfold siteHomEtaleRestrictionEvaluation
  exact isIso_exactDerivedHom (Etale.upperStar B f) a K M

private theorem proetaleRestriction_isIso
    (B : Type (u + 2)) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B]
    [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
    [Abelian.HasFunctorialFlatResolution B]
    {Y X : Scheme.{u}} (f : Y ⟶ X) [WeaklyEtale f] [(upperStar B f).PreservesFlat]
    (K M : DerivedCategory (Sheaf (Scheme.ProEt.topology X) B)) :
    IsIso (siteHomProEtaleRestrictionEvaluation B f
      (siteHomExactDerivedMonoidal (upperStar B f)) K M) := by
  have (P : Sheaf (Scheme.ProEt.topology X) B) :
      IsIso (Functor.LaxMonoidal.ihomComparison (upperStar B f) P).natTrans :=
    ProEtale.isIso_ihomComparison_upperStar B f P
  unfold siteHomProEtaleRestrictionEvaluation
  exact isIso_exactDerivedHom (upperStar B f) (weaklyEtaleLowerShriekAdjunction B f) K M

private theorem comparisonMonoidal_eq (X : Scheme.{u})
    [(comparisonUpperStar B X).PreservesFlat] :
    siteComparisonMonoidal B X = monoidal_comparisonUpperStar B X := by
  unfold siteComparisonMonoidal monoidal_comparisonUpperStar
  rfl

section RestrictionSquare
variable (B : Type (u + 2)) [Category.{u + 1} B] [Abelian B]
  [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B]
  [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
  [Abelian.HasFunctorialFlatResolution B]

private theorem comparisonDerivedMonoidal_eq (X : Scheme.{u})
    [(comparisonUpperStar B X).PreservesFlat] :
    letI : (comparisonUpperStar B X).Monoidal := siteComparisonMonoidal B X
    siteComparisonDerivedMonoidal B X =
      siteHomExactDerivedMonoidal (comparisonUpperStar B X) := by
  letI : (comparisonUpperStar B X).Monoidal := siteComparisonMonoidal B X
  unfold siteHomExactDerivedMonoidal
  exact Functor.exactDerivedMonoidal_eq_of_delta (comparisonUpperStar B X)
    (siteComparisonDerivedMonoidal B X) (siteComparisonDerivedMonoidal_δ B X)

private theorem ordinaryRestrictionSquare_eq {Y X : Scheme.{u}} (f : Y ⟶ X) :
    supportSiteComparisonCoefficientPullbackIso B f =
      (comparisonUpperStarCompUpperStarIso B f).symm := by
  rfl

private theorem ordinaryRestrictionSquare_monoidal {Y X : Scheme.{u}} (f : Y ⟶ X) :
    NatTrans.IsMonoidal (comparisonUpperStarCompUpperStarIso B f).inv := by
  haveI := isMonoidal_comparisonUpperStarCompUpperStarIso_hom (A := B) f
  infer_instance

private theorem restrictionSquare_monoidal {Y X : Scheme.{u}} (f : Y ⟶ X)
    [(comparisonUpperStar B X).PreservesFlat]
    [(comparisonUpperStar B Y).PreservesFlat]
    [(Etale.upperStar B f).PreservesFlat] [(upperStar B f).PreservesFlat] :
    letI : (comparisonUpperStar B X).mapDerivedCategory.Monoidal :=
    siteComparisonDerivedMonoidal B X
    letI : (comparisonUpperStar B Y).mapDerivedCategory.Monoidal :=
    siteComparisonDerivedMonoidal B Y
    letI := siteHomExactDerivedMonoidal (Etale.upperStar B f)
    letI := siteHomExactDerivedMonoidal (upperStar B f)
    NatTrans.IsMonoidal (siteHomRestrictionSquareFor B f).hom := by
  letI mX : (comparisonUpperStar B X).Monoidal := siteComparisonMonoidal B X
  letI mY : (comparisonUpperStar B Y).Monoidal := siteComparisonMonoidal B Y
  let e : Etale.upperStar B f ⋙ comparisonUpperStar B Y ≅
      comparisonUpperStar B X ⋙ upperStar B f :=
    supportSiteComparisonCoefficientPullbackIso B f
  have he : e = (comparisonUpperStarCompUpperStarIso B f).symm :=
    ordinaryRestrictionSquare_eq B f
  let P (a : (comparisonUpperStar B X).Monoidal)
      (b : (comparisonUpperStar B Y).Monoidal) : Prop :=
    letI := a
    letI := b
    NatTrans.IsMonoidal e.hom
  have h₀ : P (monoidal_comparisonUpperStar B X)
      (monoidal_comparisonUpperStar B Y) := by
    dsimp only [P]
    rw [he]
    exact ordinaryRestrictionSquare_monoidal B f
  haveI h : NatTrans.IsMonoidal e.hom :=
    Eq.mpr (congrArg₂ P (comparisonMonoidal_eq B X) (comparisonMonoidal_eq B Y)) h₀
  rw [comparisonDerivedMonoidal_eq B X, comparisonDerivedMonoidal_eq B Y]
  unfold siteHomExactDerivedMonoidal
    siteHomRestrictionSquareFor
  exact Functor.exactDerivedSquare_monoidal (comparisonUpperStar B X) (upperStar B f)
    (Etale.upperStar B f) (comparisonUpperStar B Y)
    e

private theorem siteComparisonEvaluationHom_eq_closedComparison (X : Scheme.{u})
    [(comparisonUpperStar B X).PreservesFlat]
    (K M : DerivedCategory (Sheaf X.smallEtaleTopology B)) :
    letI : (comparisonUpperStar B X).mapDerivedCategory.Monoidal :=
      siteComparisonDerivedMonoidal B X
    siteComparisonEvaluationHom B X K M =
      Functor.closedComparison (comparisonUpperStar B X).mapDerivedCategory K M := by
  unfold siteComparisonEvaluationHom Functor.closedComparison
  rfl

private theorem restrictionAssertion {Y X : Scheme.{u}} (f : Y ⟶ X) [Etale f]
    [(comparisonUpperStar B X).PreservesFlat]
    [(comparisonUpperStar B Y).PreservesFlat]
    [(Etale.upperStar B f).PreservesFlat] [(upperStar B f).PreservesFlat]
    (K M : DerivedCategory (Sheaf X.smallEtaleTopology B)) :
    siteHomRestrictionAssertion B f
      (siteHomExactDerivedMonoidal (Etale.upperStar B f))
      (siteHomExactDerivedMonoidal (upperStar B f)) K M := by
  refine ⟨etaleRestriction_isIso B f K M,
    proetaleRestriction_isIso B f _ _, ?_⟩
  letI : (comparisonUpperStar B X).mapDerivedCategory.Monoidal :=
    siteComparisonDerivedMonoidal B X
  letI : (comparisonUpperStar B Y).mapDerivedCategory.Monoidal :=
    siteComparisonDerivedMonoidal B Y
  letI := siteHomExactDerivedMonoidal (Etale.upperStar B f)
  letI := siteHomExactDerivedMonoidal (upperStar B f)
  have := restrictionSquare_monoidal B f
  rw [siteComparisonEvaluationHom_eq_closedComparison,
    siteComparisonEvaluationHom_eq_closedComparison]
  unfold siteHomEtaleRestrictionEvaluation siteHomProEtaleRestrictionEvaluation
  exact CategoryTheory.closedComparison_square
    (A := DerivedCategory (Sheaf X.smallEtaleTopology B))
    (B := DerivedCategory (Sheaf Y.smallEtaleTopology B))
    (E := DerivedCategory (Sheaf (Scheme.ProEt.topology X) B))
    (H := DerivedCategory (Sheaf (Scheme.ProEt.topology Y) B))
    (Etale.upperStar B f).mapDerivedCategory
    (upperStar B f).mapDerivedCategory (comparisonUpperStar B X).mapDerivedCategory
    (comparisonUpperStar B Y).mapDerivedCategory (siteHomRestrictionSquareFor B f) K M

end RestrictionSquare

private theorem siteHomExactThick_generic (V : Type (u + 2)) [Category.{u + 1} V] [Abelian V]
    [IsGrothendieckAbelian.{u + 1} V] [MonoidalCategory V]
    [MonoidalPreadditive V] [SymmetricCategory V] [MonoidalClosed V]
    [Abelian.HasFunctorialFlatResolution V] (X : Scheme.{u})
    [(comparisonUpperStar V X).PreservesFlat]
    (M : DerivedCategory (Sheaf X.smallEtaleTopology V)) :
    siteHomSiteExactThick V X M := by
  unfold siteHomSiteExactThick
  letI := siteComparisonMonoidal V X
  apply exactThickAssertion_of_exactFunctor
    (C := Sheaf X.smallEtaleTopology V)
    (D := Sheaf (Scheme.ProEt.topology X) V)
    (comparisonUpperStar V X) M (siteComparisonEvaluationHom V X)
  intro K N
  rw [siteComparisonEvaluationHom_eq_closedComparison]
  have he := comparisonDerivedMonoidal_eq V X
  unfold siteHomExactDerivedMonoidal at he
  exact congrArg (fun m ↦ @Functor.closedComparison _ _ _ _ _ _ _ _
    (comparisonUpperStar V X).mapDerivedCategory m.toLaxMonoidal K N) he

variable (A : Type (u + 1)) [CommRing A] [Finite A] (X : Scheme.{u})

/-- The first contravariant functor F RHom(-,M), using the recorded Hom and pullback.
Source: blueprint comparison proof, paragraph 2
(blueprint: lem-sf-site-hom-comparison-thick). -/
abbrev siteHomComparisonSource (M : Etale.DerivedCategoryModule A X) :=
  (Etale.derivedHom (ModuleCat.{u + 1} A) X).flip.obj M ⋙
    (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory

/-- The isomorphism locus of the specified evaluation transpose, not of chosen isomorphisms.
Source: blueprint comparison proof, paragraph 2
(blueprint: lem-sf-site-hom-comparison-thick). -/
def siteHomComparisonLocus (M : Etale.DerivedCategoryModule A X) :
    ObjectProperty (Etale.DerivedCategoryModule A X) :=
  fun K ↦ IsIso (siteComparisonEvaluationHom (ModuleCat.{u + 1} A) X K M)

/-- Exact etale restriction along an arbitrary object U → X, in fixed coefficients.
Source: Stacks 08JB (blueprint: lem-sf-site-hom-comparison-thick). -/
abbrev siteHomEtaleRestriction (U : X.Etale) :=
  (Etale.upperStar (ModuleCat.{u + 1} A) (siteHomEtaleObjectHom X U)).mapDerivedCategory

/-- Exact pro-etale restriction along the same etale object.
Source: Stacks 08JB (blueprint: lem-sf-site-hom-comparison-thick). -/
abbrev siteHomProEtaleRestriction (U : X.Etale) :=
  (upperStar (ModuleCat.{u + 1} A) (siteHomEtaleObjectHom X U)).mapDerivedCategory

/-- The fixed-coefficient instance of the canonical derived restriction square.
Source: Stacks 08JB (blueprint: lem-sf-site-hom-comparison-thick). -/
abbrev siteHomRestrictionSquare (U : X.Etale) :=
  siteHomRestrictionSquareFor (ModuleCat.{u + 1} A) (siteHomEtaleObjectHom X U)

/-- Strong monoidal structure on exact etale derived restriction, transported from
its K-flat derived tensor comparison. No tensorator is chosen arbitrarily.
Source: Stacks 07A4, 08JB (blueprint: lem-sf-site-hom-comparison-thick). -/
@[irreducible] def siteHomEtaleRestrictionMonoidal (U : X.Etale) :
    (siteHomEtaleRestriction A X U).Monoidal :=
  siteHomExactDerivedMonoidal (Etale.upperStar (ModuleCat.{u + 1} A) (siteHomEtaleObjectHom X U))

/-- Strong monoidal structure on exact pro-etale derived restriction, obtained by the
same K-flat comparison; weak etaleness of U → X gives preservation of flat sheaves.
Source: Stacks 07A4, 08JB (blueprint: lem-sf-site-hom-comparison-thick). -/
@[irreducible] def siteHomProEtaleRestrictionMonoidal (U : X.Etale) :
    (siteHomProEtaleRestriction A X U).Monoidal :=
  let F := upperStar (ModuleCat.{u + 1} A) (siteHomEtaleObjectHom X U)
  let _ : F.PreservesFlat := preservesFlat_upperStar_of_weaklyEtale (siteHomEtaleObjectHom X U)
  siteHomExactDerivedMonoidal F

/-- The canonical pro-etale internal-Hom restriction map, with the same evaluation
normalization. Source: Stacks 08J9, 08JB (blueprint: lem-sf-site-hom-comparison-thick). -/
abbrev siteHomProEtaleRestrictionHom (U : X.Etale)
    (K M : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))) :=
  siteHomProEtaleRestrictionEvaluation (ModuleCat.{u + 1} A) (siteHomEtaleObjectHom X U)
    (siteHomProEtaleRestrictionMonoidal A X U) K M

/-- Exactness, signed shift compatibility, the full reversed triangle morphism and thick
closure for the specified evaluation comparison, for each arbitrary fixed target M.
Source: blueprint comparison proof, paragraph 2; Stacks 08J9, 08JC
(blueprint: lem-sf-site-hom-comparison-thick).

Proof (node steps 1--6): comparison pullback is exact, and Hom into a K-injective target
is exact contravariantly. Represent M by I and resolve FI → J by a K-injective J.
On each source complex E the map is F Hom(E,I) → Hom(FE,FI) → Hom(FE,J).
Naturality descends through inverted quasi-isomorphisms. On K-flat E and a K-flat
resolution of Hom(E,I), uncurrying on every total-tensor summand identifies this map
with the existing evaluation transpose; replace arbitrary E by a K-flat resolution.
Signed reindexing commutes with both arrows. The correction n(n+1)/2 is the same
on both rows (lem-coef-signed-derived-internal-hom-exact), so the resulting exact
structures have precisely the displayed normalizations. Naturality at the boundary
and this shift equation give all three triangle squares. Triangle two-of-three gives
cone closure. Zero, isomorphisms, shifts and finite sums follow by exactness and
additivity. For a retract i:L → K, p:K → L and a=beta_K invertible, the inverse of
beta_L is B(i) a⁻¹ C(p); naturality and pi=1 prove both inverse identities. -/
theorem siteHomComparison_exact_thick (M : Etale.DerivedCategoryModule A X) :
    siteHomSiteExactThick (ModuleCat.{u + 1} A) X M := by
  exact siteHomExactThick_generic (ModuleCat.{u + 1} A) X M

/-- The actual comparison commutes with restriction to every etale object, including
restricted evaluation. Both Hom restriction maps are the canonical isomorphisms.
Source: blueprint comparison proof, paragraphs 1--2; Stacks 08JB and 07A4
(blueprint: lem-sf-site-hom-comparison-thick).

Proof (node step 7): the localized ringed-site square gives r_p F ≅ F_U r_e. Its
K-flat normalization is the same as localization of the ordinary inverse-image
comparison (lem-weil-pbc-ringed-slice-pullback-mate-normalization). Restriction
preserves evaluation and its transpose (lem-weil-pbc-ringed-slice-evaluation-transpose).
Uncurry both sides of the displayed equation. Each is restricted evaluation after
the inverse canonical tensor comparison. On each K-flat total-tensor summand the
comparison square commutes, since both routes restrict the ordinary tensor map.
Injectivity of the tensor-Hom bijection gives equality. This uses localization at
an object, not an open-immersion assumption, and applies to all unbounded K,M. -/
theorem siteHomComparison_restriction (U : X.Etale)
    (K M : Etale.DerivedCategoryModule A X) :
    siteHomRestrictionAssertion (ModuleCat.{u + 1} A) (siteHomEtaleObjectHom X U)
      (siteHomEtaleRestrictionMonoidal A X U) (siteHomProEtaleRestrictionMonoidal A X U)
      K M := by
  letI : (upperStar (ModuleCat.{u + 1} A) (siteHomEtaleObjectHom X U)).PreservesFlat :=
    preservesFlat_upperStar_of_weaklyEtale (Λ := A) (siteHomEtaleObjectHom X U)
  unfold siteHomEtaleRestrictionMonoidal siteHomProEtaleRestrictionMonoidal
  exact restrictionAssertion (ModuleCat.{u + 1} A)
    (Y := U.left) (X := X) (siteHomEtaleObjectHom X U) K M

end AlgebraicGeometry.ProEtale
