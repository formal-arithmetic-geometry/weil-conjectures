/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.NativeInjectiveAdjunctionModel
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction

/-! # Resolution-independent native Weil derived Hom transposition

Source: Stacks Project, Derived Categories, Tags 070I and 08BJ; the native
Weil framework; blueprint fix-lem-tensor-adjunction.proof.md, Step 1.
(blueprint: lem-sf-native-weil-derived-hom-comparison)
-/

@[expose] public section

set_option autoImplicit false

universe u uA uB uDX uDY vA vB vDX vDY

open CategoryTheory Limits

namespace CategoryTheory.Adjunction

/-- The equations characterizing the resolution Hom transpose on localized categories.
They are written after composition by the resolution map and by beta, which are
invertible in the native K-injective application. Thus the equations specify the
four-arrow composite with inverse localization on Hom, not an arbitrary equivalence.
The first clause gives unique lifts between injective representatives, and the last
two clauses specify the identity transposes. All variables and arrows are ambient.
Source: Stacks Tags 070I and 08BJ, the node's Hom calculation and proof steps 1--7
(blueprint: lem-sf-native-weil-derived-hom-comparison). -/
def IsResolutionHomComparison
    {A : Type uA} {B : Type uB} {DX : Type uDX} {DY : Type uDY}
    [Category.{vA} A] [Category.{vB} B] [Category.{vDX} DX] [Category.{vDY} DY]
    (Fh : A ⥤ B) (Gh : B ⥤ A) (QX : B ⥤ DX) (QY : A ⥤ DY)
    (Fd : DY ⥤ DX) (Rd : DX ⥤ DY)
    (α : QY ⋙ Fd ≅ Fh ⋙ QX) (β : Gh ⋙ QY ⟶ QX ⋙ Rd)
    (adjh : Fh ⊣ Gh) (adj : Fd ⊣ Rd)
    (KI : B → Prop) (W : MorphismProperty B) : Prop :=
  (∀ (I I' : B), KI I → KI I' → ∀ (v : QX.obj I ⟶ QX.obj I'),
    ∃! t : I ⟶ I', QX.map t = v ∧
      β.app I ≫ Rd.map v = QY.map (Gh.map t) ≫ β.app I' ∧
      (IsIso v → IsIso t)) ∧
  (∀ (M : A) (J I : B), KI I → ∀ (r : J ⟶ I), W r →
    ∀ (h : QX.obj (Fh.obj M) ⟶ QX.obj J) (t : Fh.obj M ⟶ I),
      QX.map t = h ≫ QX.map r →
      adj.homEquiv _ _ (α.hom.app M ≫ h) ≫ Rd.map (QX.map r) =
        QY.map (adjh.unit.app M ≫ Gh.map t) ≫ β.app I) ∧
  (∀ (T T' : DY) (N : DX) (a : T' ⟶ T) (h : Fd.obj T ⟶ N),
    adj.homEquiv T' N (Fd.map a ≫ h) = a ≫ adj.homEquiv T N h) ∧
  (∀ (T : DY) (N N' : DX) (h : Fd.obj T ⟶ N) (b : N ⟶ N'),
    adj.homEquiv T N' (h ≫ b) = adj.homEquiv T N h ≫ Rd.map b) ∧
  (∀ (M : A) (I : B), KI I → ∀ (s : Fh.obj M ⟶ I), W s →
    adj.unit.app (QY.obj M) ≫ Rd.map (α.hom.app M) ≫ Rd.map (QX.map s) =
      QY.map (adjh.unit.app M ≫ Gh.map s) ≫ β.app I) ∧
  (∀ (I : B), KI I →
    Fd.map (β.app I) ≫ adj.counit.app (QX.obj I) =
      α.hom.app (Gh.obj I) ≫ QX.map (adjh.counit.app I))

private theorem resolutionHomComparison_of_normalizations
    {A : Type uA} {B : Type uB} {DX : Type uDX} {DY : Type uDY}
    [Category.{vA} A] [Category.{vB} B] [Category.{vDX} DX] [Category.{vDY} DY]
    (Fh : A ⥤ B) (Gh : B ⥤ A) (QX : B ⥤ DX) (QY : A ⥤ DY)
    (Fd : DY ⥤ DX) (Rd : DX ⥤ DY)
    (α : QY ⋙ Fd ≅ Fh ⋙ QX) (β : Gh ⋙ QY ⟶ QX ⋙ Rd)
    (adjh : Fh ⊣ Gh) (adj : Fd ⊣ Rd)
    (KI : B → Prop) (W : MorphismProperty B)
    (hQ : ∀ (M I : B), KI I → Function.Bijective
      (QX.map : (M ⟶ I) → (QX.obj M ⟶ QX.obj I)))
    (hη : ∀ M : A,
      adj.unit.app (QY.obj M) ≫ Rd.map (α.hom.app M) =
        QY.map (adjh.unit.app M) ≫ β.app (Fh.obj M))
    (hε : ∀ I : B,
      Fd.map (β.app I) ≫ adj.counit.app (QX.obj I) =
        α.hom.app (Gh.obj I) ≫ QX.map (adjh.counit.app I)) :
    IsResolutionHomComparison Fh Gh QX QY Fd Rd α β adjh adj KI W := by
  have htranspose (M : A) (I : B) (t : Fh.obj M ⟶ I) :
      adj.homEquiv _ _ (α.hom.app M ≫ QX.map t) =
        QY.map (adjh.unit.app M ≫ Gh.map t) ≫ β.app I := by
    rw [homEquiv_apply, Rd.map_comp, ← Category.assoc, hη]
    have hβ := β.naturality t
    dsimp only [Functor.comp_map] at hβ
    rw [Category.assoc, ← hβ, ← Category.assoc, ← QY.map_comp]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro I I' hI hI' v
    obtain ⟨t, ht⟩ := (hQ I I' hI').surjective v
    refine ⟨t, ⟨ht, ?_, ?_⟩, ?_⟩
    · rw [← ht]
      exact (β.naturality t).symm
    · intro hv
      have := hv
      obtain ⟨s, hs⟩ := (hQ I' I hI).surjective (inv v)
      refine ⟨⟨s, ?_, ?_⟩⟩
      · apply (hQ I I hI).injective
        simp only [Functor.map_comp, Functor.map_id, ht, hs, IsIso.hom_inv_id]
      · apply (hQ I' I' hI').injective
        simp only [Functor.map_comp, Functor.map_id, ht, hs, IsIso.inv_hom_id]
    · intro t' ht'
      exact (hQ I I' hI').injective (ht'.1.trans ht.symm)
  · intro M J I _ r _ h t ht
    rw [← adj.homEquiv_naturality_right, Category.assoc, ← ht]
    exact htranspose M I t
  · intro T T' N a h
    exact adj.homEquiv_naturality_left a h
  · intro T N N' h b
    exact adj.homEquiv_naturality_right h b
  · intro M I _ s _
    simpa only [homEquiv_apply, Functor.map_comp, Category.assoc] using htranspose M I s
  · intro I _
    exact hε I

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.ProEtaleWeilSheaf

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [hchar : Fact (ringChar k₀ ≠ l)]
  {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]
  (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))]

variable [hXs : IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [hYs : IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [hXt : LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [hYt : LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [hXq : QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [hYq : QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  [hfs : IsSeparated f] [hft : LocallyOfFiniteType f] [hfq : QuasiCompact f]

include hchar hXs hYs hXt hYt hXq hYq hfs hft hfq

/-- The resolution Hom composites are bijective and independent of resolution.
For each resolution, the unique equivalence is characterized after composing
with the invertible Rf_*(Qr). The target homotopy class t is characterized by
Q(t) = h Q(r); the K-injective Hom localization bijection supplies its unique
value. Thus the displayed equation specifies exactly the node's four-arrow
composite, without asking Lean to unfold the native adjunction's data.
All resolution equivalences equal the same ambient adjunction Hom equivalence,
which expresses their resolution independence directly.
They are the Hom equivalences of an adjunction on the actual ambient derived
categories, natural for all derived arrows, and have the specified unit and
counit normalizations. The factor isomorphisms explicitly identify D(F0)QM with
QF0M; no equality of these two presentations is silently assumed.
Source: Stacks Tags 070I, 08BJ; blueprint fix-lem-tensor-adjunction.proof.md, Step 1
(blueprint: lem-sf-native-weil-derived-hom-comparison).

Proof (the node's seven steps):
1. nativeWeilInjectiveAdjunctionModel gives exact F0 and K-injective G0I.
By lem-weil-pbc-kinjective-hom-derived, localization on Hom into I and G0I
is bijective. Qr and c_r are invertible, so the four-arrow composite is bijective.
2. Naturality of the specified underived unit makes homotopy transposition
natural in M and in maps between K-injectives. Naturality of beta transfers
this to the derived target.
3. Exact F0 inverts quasi-isomorphisms. Source naturality therefore holds also
for their inverses and composites, hence for every derived arrow by the
localization construction of def-weil-abstract-derived-category.
4. Lift Qr' b (Qr) inverse uniquely to a homotopy map between K-injectives.
The comparison equation of nativeWeilDerivedDirectImageModel gives the
beta-conjugation formula and target naturality for arbitrary derived b.
5. Set b to the identity to compare any two resolutions. Applying naturality
to specified source and target isomorphisms gives independence of complex
representatives. Lift an isomorphism and its inverse between K-injectives;
faithfulness of the Hom localization shows the lifts are inverse, so the
comparison is a homotopy equivalence.
6. Transpose the identity using a resolution of F0M: the four arrows send it
to Q(G0s eta_M) followed by c_s inverse. For K-injective I use the identity
resolution: the inverse transpose of the identity of G0I is epsilon_I.
Source naturality at beta_I gives the displayed derived counit normalization.
7. Define the derived unit and counit as the identity transposes. The two
naturality equations express every transpose using these maps; the two
inverse-composite identities give the triangle identities. This constructs
the asserted adjunction, with exactly those normalizations. All objects
remain in D of the abelian Weil categories, without boundedness restrictions. -/
theorem derivedHomComparison :
    ∃ adj : (upperStar k₀ l f).mapDerivedCategory ⊣
        (lowerStar k₀ l f).rightDerivedFunctor,
      CategoryTheory.Adjunction.IsResolutionHomComparison
        ((upperStar k₀ l f).mapHomotopyCategory (ComplexShape.up ℤ))
        ((lowerStar k₀ l f).mapHomotopyCategory (ComplexShape.up ℤ))
        DerivedCategory.Qh DerivedCategory.Qh
        (upperStar k₀ l f).mapDerivedCategory (lowerStar k₀ l f).rightDerivedFunctor
        (upperStar k₀ l f).mapDerivedCategoryFactorsh
        (lowerStar k₀ l f).rightDerivedFunctorUnit
        ((upperStarLowerStarAdjunction k₀ l f).mapHomotopyCategory (ComplexShape.up ℤ))
        adj
        (fun I ↦ ∃ (J : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ),
          J.IsKInjective ∧ (HomotopyCategory.quotient _ _).obj J = I)
        (HomotopyCategory.quasiIso (ProEtaleWeilSheaf k₀ l X) (ComplexShape.up ℤ)) := by
  have : PreservesFiniteLimits (upperStar k₀ l f) :=
    (nativeWeilInjectiveAdjunctionModel k₀ l f).2.2.1
  let adj := (upperStarLowerStarAdjunction k₀ l f).mapDerivedCategoryRightDerivedAdjunction
  refine ⟨adj, CategoryTheory.Adjunction.resolutionHomComparison_of_normalizations
    _ _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_⟩
  · intro M I hI
    obtain ⟨J, hJ, rfl⟩ := hI
    have := hJ
    exact CochainComplex.IsKInjective.Qh_map_bijective M J
  · intro M
    exact ((upperStarLowerStarAdjunction k₀ l f).mapHomotopyCategory
      (ComplexShape.up ℤ)).derivedη_fac_app
        (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
        (upperStar k₀ l f).mapDerivedCategoryFactorsh.hom
        (lowerStar k₀ l f).rightDerivedFunctorUnit M
  · intro I
    exact ((upperStarLowerStarAdjunction k₀ l f).mapHomotopyCategory
      (ComplexShape.up ℤ)).derivedε_fac_app
        (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
        (upperStar k₀ l f).mapDerivedCategoryFactorsh.hom
        (lowerStar k₀ l f).rightDerivedFunctorUnit I

end AlgebraicGeometry.ProEtaleWeilSheaf
