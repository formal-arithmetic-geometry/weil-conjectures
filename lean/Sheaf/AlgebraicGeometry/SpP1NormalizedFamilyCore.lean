/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P4
-/
module
public import Sheaf.AlgebraicGeometry.ProEtaleProjectiveLineTraceSystem
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarProjComparison
import Sheaf.AlgebraicGeometry.FiniteP1KummerSplitting
import Sheaf.AlgebraicGeometry.OrdinaryFiniteClassArbitraryBase
import Sheaf.AlgebraicGeometry.FiniteP1NoetherianBase
/-! # Constructing normalized projective-line decomposition families

Source: det-sp-p1-trace, clauses 1--2 and the arbitrary-base consequence.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale

set_option linter.unusedSimpArgs false

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem exists_left_of_exists_and {α : Sort*} {P Q : α → Prop}
    (h : ∃ a, P a ∧ Q a) : ∃ a, P a := by
  obtain ⟨a, ha, _⟩ := h
  exact ⟨a, ha⟩

private theorem sum_comparison_iso (A : Type (u + 1)) [CommRing A] (S : Scheme.{u})
    (K L : Etale.DerivedCategoryModule A S) : IsIso (geoP1SumComparison A S K L) := by
  have : PreservesBinaryBiproducts (geoP1Comparison A S) :=
    preservesBinaryBiproducts_of_preservesBiproducts _
  change IsIso ((geoP1Comparison A S).mapBiprod K L).inv
  infer_instance

private lemma mate_whiskerTop
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    {G G' : A ⥤ C} {H : B ⥤ D}
    (α : TwoSquare G' L₁ L₂ H) (γ : G ⟶ G') (K : B) :
    (mateEquiv adj₁ adj₂ (α.whiskerTop γ)).app K =
      γ.app (R₁.obj K) ≫ (mateEquiv adj₁ adj₂ α).app K := by
  simp [mateEquiv, TwoSquare.whiskerTop]

private lemma mate_whiskerBottom
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    {G : A ⥤ C} {H H' : B ⥤ D}
    (α : TwoSquare G L₁ L₂ H) (δ : H ⟶ H') (K : B) :
    (mateEquiv adj₁ adj₂ (α.whiskerBottom δ)).app K =
      (mateEquiv adj₁ adj₂ α).app K ≫ R₂.map (δ.app K) := by
  simp [mateEquiv, TwoSquare.whiskerBottom, ← Functor.map_comp, δ.naturality]

private theorem push_comparison_iso (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (K : Etale.DerivedCategoryModule A X) (hK : DerivedCategory.TStructure.t.plus K) :
    IsIso (geoP1PushComparison A f K) := by
  let α := TwoSquare.mk _ _ _ _
    (leftDerivedComparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) f).hom
  let eY :=
    (comparisonUpperStar (ModuleCat.{u + 1} A) Y).leftDerivedFunctorIsoMapDerivedCategory
  let eX :=
    (comparisonUpperStar (ModuleCat.{u + 1} A) X).leftDerivedFunctorIsoMapDerivedCategory
  have hs : (α.whiskerTop eY.inv).whiskerBottom eX.hom =
      TwoSquare.mk _ _ _ _ (geoP1PullComparison A f).hom := by
    ext M
    simp only [α, eY, eX, TwoSquare.mk, TwoSquare.whiskerTop_app, TwoSquare.whiskerBottom_app,
      leftDerivedComparisonUpperStarCompUpperStarIso, Functor.leftDerivedFunctorCompNatIso,
      Functor.leftDerivedFunctorCompIso, Functor.leftDerivedFunctorNatIso,
      geoP1PullComparison, leftDerivedUpperStarIsoMapDerivedCategory,
      Etale.leftDerivedUpperStarIsoMapDerivedCategory,
      Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_inv,
      Functor.isoWhiskerRight_inv, Category.assoc, Iso.inv_hom_id_app_assoc]
    simp only [Iso.inv_hom_id_app, Category.comp_id, NatTrans.naturality_assoc,
      ← Functor.map_comp, ← Functor.map_comp_assoc, Iso.inv_hom_id_app_assoc,
      CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
    erw [Category.comp_id]
  have hm := isIso_mateEquiv_leftDerivedComparisonUpperStarCompUpperStarIso_app
    (ModuleCat.{u + 1} A) f K hK
  have hmate : IsIso ((mateEquiv
      (Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
      ((α.whiskerTop eY.inv).whiskerBottom eX.hom)).app K) := by
    rw [mate_whiskerBottom, mate_whiskerTop]
    infer_instance
  rw [hs] at hmate
  simpa [geoP1PushComparison, mateEquiv, Adjunction.homEquiv_unit, TwoSquare.mk,
    geoP1Comparison, geoP1Pushforward, Etale.ordinaryFinitePushforward] using hmate

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] DerivedCategory HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions Functor.rightDerivedFunctor
  Functor.mapDerivedCategory AlgebraicGeometry.ProjectiveSpace
  Etale.projectiveLineTraceTransport Etale.projectiveLineTraceDatum

/-- The normalized finite projective-line decomposition families exist.
Source: det-sp-p1-trace, clauses 1--2 (blueprint: lem-sp-p1-normalized-family-core).

Proof: choose the Noetherian universal base Spec Z[1/N] and apply the ordinary
finite decomposition there. Its arbitrary-base clause supplies a normalized
Chern arrow and an invertible untwisted map at each base. Independently take the
existing normalized Kummer splitting family. The arbitrary-base class comparison
is injective, so its normalized Chern arrow equals the untwisted one. Form d by the exact
comparison image of this map and the canonical direct-image comparison. The
latter is invertible on bounded-below objects by the established comparison
of derived direct images. Transport from the left-derived comparison to the
exact-derived presentation is by whiskering the pullback square with its
canonical isomorphisms; the two mate whiskering identities show that it is
precisely geoP1PushComparison. The existing normalized splitting gives the
invertible unit/Chern map. Its comparison image, conjugated by the
biproduct comparison, defines b via asIso. Biproduct injection identities give
its required unit and Chern components. All inverses are inverses of specified
isomorphisms; d is a displayed construction. No arbitrary decomposition is
chosen, and boundedness is applied only to single objects and their shifts. -/
theorem exists_spP1NormalizedDecompositions
    (A : Type (u + 1)) [CommRing A] [Finite A] (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) :
    ∃ (c : SpP1ChernFamily A N hA) (b : SpP1TwistedFamily A N hA)
      (d : SpP1DecompositionFamily A N hA),
      SpP1NormalizedDecompositions A N hN hA c b d := by
  classical
  obtain ⟨U, hU, hNU, hmap⟩ := finiteP1_exists_noetherianBase.{u} N
  let := hU
  obtain ⟨c, hctwisted⟩ := exists_left_of_exists_and
    (Etale.exists_ordinaryFiniteP1SplittingMap N hN A hA)
  have hciso (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) :
      IsIso (Etale.p1DecompositionMap A N hN hA S hS (c S hS)) := by
    obtain ⟨cU, _, _, hbc⟩ := Etale.ordinaryFiniteP1Decomposition N hN A hA U hNU
    obtain ⟨f⟩ := hmap S hS
    obtain ⟨c', hc', hi, _⟩ := hbc S f
    have he : c' = c S hS :=
      (Etale.ordinaryFiniteClass_bijective_arbitraryBase A (ProjectiveLine S)
        (Scheme.finiteEtaleTateLine (ProjectiveLine S) N A hA) 2).1
          (hc'.trans (hctwisted S hS).1.symm)
    simpa only [he] using hi
  let d : SpP1DecompositionFamily A N hA := ⟨fun S hS ↦
    geoP1SumComparison A S _ _ ≫
      (geoP1Comparison A S).map (Etale.p1DecompositionMap A N hN hA S hS (c S hS)) ≫
      geoP1PushComparison A (ProjectiveLine S ↘ S) (Etale.ordinaryFiniteUnit A _)⟩
  have hbiso (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) :
      IsIso (geoP1SumComparison A S
          ((Etale.ordinaryFiniteLine A N hA S)⟦(2 : ℤ)⟧) (Etale.ordinaryFiniteUnit A S) ≫
        (geoP1Comparison A S).map (Etale.ordinaryFiniteP1SplittingMap A N hA
          (Etale.projectiveLineTraceTransport N hN A hA) S hS (c S hS)) ≫
        geoP1PushComparison A (ProjectiveLine S ↘ S)
          ((Etale.ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧)) := by
    have := (hctwisted S hS).2
    have := sum_comparison_iso A S
      ((Etale.ordinaryFiniteLine A N hA S)⟦(2 : ℤ)⟧) (Etale.ordinaryFiniteUnit A S)
    have := push_comparison_iso A (ProjectiveLine S ↘ S)
      ((Etale.ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧)
      (DerivedCategory.TStructure.t.plus.le_shift (2 : ℤ) _ ⟨0, inferInstance⟩)
    infer_instance
  let b : SpP1TwistedFamily A N hA := ⟨fun S hS ↦
    @asIso _ _ _ _ _ (hbiso S hS)⟩
  refine ⟨⟨c⟩, b, d, ?_⟩
  intro S hS
  refine ⟨(hctwisted S hS).1, ?_, HEq.rfl, ?_, ?_⟩
  · have := hciso S hS
    have := sum_comparison_iso A S (Etale.ordinaryFiniteUnit A S)
      (Etale.p1DecompositionTwist A N hA S (-1) (-2))
    have := push_comparison_iso A (ProjectiveLine S ↘ S)
      (Etale.ordinaryFiniteUnit A _) ⟨0, inferInstance⟩
    dsimp only [d, SpP1DecompositionFamily.map]
    infer_instance
  · apply heq_of_eq
    dsimp only [b, SpP1TwistedFamily.map, asIso]
    unfold geoP1TwistedUnit geoP1SumComparison Etale.ordinaryFiniteP1SplittingMap
    erw [biprod.inl_desc_assoc, ← CategoryTheory.Functor.map_comp_assoc, biprod.inl_desc]
    rfl
  · apply heq_of_eq
    dsimp only [b, SpP1TwistedFamily.map, asIso]
    unfold geoP1ChernPushforward geoP1SumComparison Etale.ordinaryFiniteP1SplittingMap
    erw [biprod.inr_desc_assoc, ← CategoryTheory.Functor.map_comp_assoc, biprod.inr_desc]

end AlgebraicGeometry.ProEtale
