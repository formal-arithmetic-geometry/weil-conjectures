/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NU
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons
public import Sheaf.AlgebraicGeometry.CompactProjectionExchange
public import Sheaf.AlgebraicGeometry.ProperProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
public import Mathlib.CategoryTheory.Adjunction.Mates

import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionMonoidal

/-!
# Integration transposes, base change, and adjunction transport

Source: main-20261015, sec-smooth-purity/sk-prop-an,
cor-pur-vector-bundle-purity.proof.md, paragraphs 1--2, especially
"Transposing these equalities" (blueprint: lem-pur-integration-transpose-base-change).

All categories are ordinary unbounded small-etale module derived categories. Derived
inverse image is identified with exact inverse image by the recorded canonical
leftDerivedUpperStarIsoMapDerivedCategory. Projection maps are the existing
coefficient-first compactification maps; no arbitrary projection or exchange is supplied.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Etale

private lemma three_squares
    {C : Type*} [Category C] {A B C₁ D E F G H : C}
    (a : A ⟶ B) (b : B ⟶ C₁) (c : A ⟶ D) (d : D ⟶ C₁)
    (e : C₁ ⟶ E) (f : D ⟶ F) (g : F ⟶ E)
    (h : E ⟶ G) (i : F ⟶ H) (j : H ⟶ G)
    (ha : a ≫ b = c ≫ d) (hb : d ≫ e = f ≫ g) (hc : g ≫ h = i ≫ j) :
    a ≫ b ≫ e ≫ h = c ≫ f ≫ i ≫ j := by
  rw [reassoc_of% ha, reassoc_of% hb, hc]

private lemma tensorRightUnitor_naturality
    (B : Type*) [Category.{u + 1} B] [Abelian B] [IsGrothendieckAbelian.{u + 1} B]
    [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
    [Abelian.HasFunctorialFlatResolution B] (Y : Scheme.{u})
    {K L : DerivedCategory (Sheaf Y.smallEtaleTopology B)} (v : K ⟶ L) :
    ((derivedTensor B Y).map v).app (𝟙_ _) ≫ (derivedTensorRightUnitor B Y L).hom =
      (derivedTensorRightUnitor B Y K).hom ≫ v :=
  rightUnitor_naturality v

private lemma tensorRightUnitor_pullback
    (B : Type*) [Category.{u + 1} B] [Abelian B] [IsGrothendieckAbelian.{u + 1} B]
    [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
    [Abelian.HasFunctorialFlatResolution B] [UpperStarPreservesFlat B]
    {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology B)) :
    ((leftDerivedUpperStarTensorComparison B g).app K).app (𝟙_ _) ≫
        ((derivedTensor B Y').obj ((upperStar B g).leftDerivedFunctor.obj K)).map
          (leftDerivedUpperStarUnitIso B g).hom ≫
        (derivedTensorRightUnitor B Y' ((upperStar B g).leftDerivedFunctor.obj K)).hom =
      (upperStar B g).leftDerivedFunctor.map (derivedTensorRightUnitor B Y K).hom :=
  leftDerivedUpperStarTensorComparison_rightUnitor_hom B g K

attribute [local irreducible] derivedTensor derivedTensorSymmetry

variable (A : Type (u + 1)) [CommRing A] [Finite A]

omit [Finite A] in
private lemma compactProjection_naturality_right {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f] (K : DerivedCategoryModule A Y)
    {M N : DerivedCategoryModule A X} (w : M ⟶ N) :
    ((derivedTensor (ModuleCat.{u + 1} A) Y).obj K).map
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map w) ≫
      compactProjectionMapCoeffFirst A f K N =
    compactProjectionMapCoeffFirst A f K M ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map
        (((derivedTensor (ModuleCat.{u + 1} A) X).obj
          ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj K)).map w) := by
  have hp := NatTrans.congr_app ((projectionMap (ModuleCat.{u + 1} A) f).naturality w) K
  have hs := ((derivedTensorSymmetry (ModuleCat.{u + 1} A) Y).hom.app K).naturality
    ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map w)
  have ht := (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).congr_map
    (NatTrans.congr_app ((derivedTensorSymmetry (ModuleCat.{u + 1} A) X).hom.naturality w)
      ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj K))
  dsimp only [NatTrans.comp_app, Functor.comp_map, derivedTensorRightDerivedLowerShriek,
    rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar, Functor.comp_obj] at hp
  simp only [NatTrans.comp_app, Functor.map_comp] at ht
  simpa only [compactProjectionMapCoeffFirst, Functor.flip_map_app,
    Functor.flip_obj_obj, Category.assoc] using
    three_squares _ _ _ _ _ _ _ _ _ _ hs hp ht

/-- The functor G₀(K) = f* K tensor W.
Source: cor-pur-vector-bundle-purity.proof.md, paragraph 1
(blueprint: lem-pur-integration-transpose-base-change). -/
def integrationTwistedFunctor {X Y : Scheme.{u}} (f : X ⟶ Y)
    (W : DerivedCategoryModule A X) :
    DerivedCategoryModule A Y ⥤ DerivedCategoryModule A X :=
  (upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor ⋙
    derivedTensorRight (ModuleCat.{u + 1} A) X W

/-- Integration c_K = P⁻¹ followed by 1 tensor t and the right unitor.
Source: cor-pur-vector-bundle-purity.proof.md, paragraph 1
(blueprint: lem-pur-integration-transpose-base-change). -/
def integrationCounit {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (W : DerivedCategoryModule A X)
    (t : (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj W ⟶ 𝟙_ _)
    (hP : ∀ K : DerivedCategoryModule A Y, IsIso (compactProjectionMapCoeffFirst A f K W))
    (K : DerivedCategoryModule A Y) :
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj
      ((integrationTwistedFunctor A f W).obj K) ⟶ K :=
  @inv _ _ _ _ (compactProjectionMapCoeffFirst A f K W) (hP K) ≫
    ((derivedTensor (ModuleCat.{u + 1} A) Y).obj K).map t ≫
    (derivedTensorRightUnitor (ModuleCat.{u + 1} A) Y K).hom

/-- The specified Hom transpose of integration, with the actual chosen adjunction.
Source: cor-pur-vector-bundle-purity.proof.md, paragraph 1
(blueprint: lem-pur-integration-transpose-base-change). -/
def integrationTranspose {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (R : DerivedCategoryModule A Y ⥤ DerivedCategoryModule A X)
    (adj : rightDerivedLowerShriek (ModuleCat.{u + 1} A) f ⊣ R)
    (W : DerivedCategoryModule A X)
    (t : (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj W ⟶ 𝟙_ _)
    (hP : ∀ K : DerivedCategoryModule A Y, IsIso (compactProjectionMapCoeffFirst A f K W))
    (K : DerivedCategoryModule A Y) :
    (integrationTwistedFunctor A f W).obj K ⟶ R.obj K :=
  adj.homEquiv _ _ (integrationCounit A f W t hP K)

-- Retain the existing finite-coefficient interface.
set_option linter.unusedSectionVars false in
/-- Each integration transpose family is natural.
Source: cor-pur-vector-bundle-purity.proof.md, paragraphs 1--2
(blueprint: lem-pur-integration-transpose-base-change).
Proof: the proper projection and open tensor comparison are natural in K. Inverting
that naturality square shows u c_K = c_L F(G₀u). Apply the natural Hom bijection of
F ⊣ R (lem-sfb-adjunction-transpose-square) to get the displayed square. This applies
separately to the primed family as well. -/
theorem integrationTranspose_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f] (R : DerivedCategoryModule A Y ⥤ DerivedCategoryModule A X)
    (adj : rightDerivedLowerShriek (ModuleCat.{u + 1} A) f ⊣ R)
    (W : DerivedCategoryModule A X)
    (t : (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj W ⟶ 𝟙_ _)
    (hP : ∀ K : DerivedCategoryModule A Y, IsIso (compactProjectionMapCoeffFirst A f K W))
    {K L : DerivedCategoryModule A Y} (v : K ⟶ L) :
    (integrationTwistedFunctor A f W).map v ≫ integrationTranspose A f R adj W t hP L =
      integrationTranspose A f R adj W t hP K ≫ R.map v := by
  unfold integrationTranspose
  apply adj.homEquiv_naturality_left_square
  have hp : ((derivedTensor (ModuleCat.{u + 1} A) Y).map v).app
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj W) ≫
      compactProjectionMapCoeffFirst A f L W =
    compactProjectionMapCoeffFirst A f K W ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map
        ((integrationTwistedFunctor A f W).map v) := by
    have hs := NatTrans.congr_app
      ((derivedTensorSymmetry (ModuleCat.{u + 1} A) Y).hom.naturality v)
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj W)
    have hp := ((projectionMap (ModuleCat.{u + 1} A) f).app W).naturality v
    have ht := (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).congr_map
      (((derivedTensorSymmetry (ModuleCat.{u + 1} A) X).hom.app W).naturality
        ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.map v))
    dsimp only [Functor.flip_obj_map, Functor.flip_map_app, NatTrans.comp_app] at hs
    simp only [Functor.map_comp] at ht
    dsimp only [Functor.comp_map, rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar,
      derivedTensorRightDerivedLowerShriek, Functor.comp_obj] at hp
    simpa only [compactProjectionMapCoeffFirst, integrationTwistedFunctor,
      Functor.comp_map, derivedTensorRight, Functor.flip_obj_map, Category.assoc] using
      three_squares _ _ _ _ _ _ _ _ _ _ hs hp ht
  have := hP K
  have := hP L
  have hi : (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map
        ((integrationTwistedFunctor A f W).map v) ≫
      inv (compactProjectionMapCoeffFirst A f L W) =
    inv (compactProjectionMapCoeffFirst A f K W) ≫
      ((derivedTensor (ModuleCat.{u + 1} A) Y).map v).app
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj W) := by
    apply (cancel_mono (compactProjectionMapCoeffFirst A f L W)).1
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    rw [hp, IsIso.inv_hom_id_assoc]
  unfold integrationCounit
  rw [reassoc_of% hi]
  rw [← reassoc_of% (((derivedTensor (ModuleCat.{u + 1} A) Y).map v).naturality t)]
  simp only [Category.assoc]
  rw [tensorRightUnitor_naturality]

/-- The natural transformation with the specified integration transposes as components.
Source: cor-pur-vector-bundle-purity.proof.md, paragraphs 1--2
(blueprint: lem-pur-integration-transpose-base-change). -/
def integrationTransposeNatTrans {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f] (R : DerivedCategoryModule A Y ⥤ DerivedCategoryModule A X)
    (adj : rightDerivedLowerShriek (ModuleCat.{u + 1} A) f ⊣ R)
    (W : DerivedCategoryModule A X)
    (t : (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj W ⟶ 𝟙_ _)
    (hP : ∀ K : DerivedCategoryModule A Y, IsIso (compactProjectionMapCoeffFirst A f K W)) :
    integrationTwistedFunctor A f W ⟶ R where
  app := integrationTranspose A f R adj W t hP
  naturality := fun {_ _} v ↦ integrationTranspose_naturality A f R adj W t hP v

-- Retain the existing finite-coefficient interface.
set_option linter.unusedSectionVars false in
/-- Counit normalization determines each transpose uniquely.
Source: cor-pur-vector-bundle-purity.proof.md, paragraph 1
(blueprint: lem-pur-integration-transpose-base-change).
Proof: apply the adjunct-counit identity of lem-weil-pbc-adjunct-counit-identity.
The inverse Hom bijection sends b to F(b) followed by epsilon. Its injectivity gives
both directions and, at b = gamma_K, the normalization itself. -/
theorem integrationTranspose_unique {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f] (R : DerivedCategoryModule A Y ⥤ DerivedCategoryModule A X)
    (adj : rightDerivedLowerShriek (ModuleCat.{u + 1} A) f ⊣ R)
    (W : DerivedCategoryModule A X)
    (t : (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj W ⟶ 𝟙_ _)
    (hP : ∀ K : DerivedCategoryModule A Y, IsIso (compactProjectionMapCoeffFirst A f K W))
    (K : DerivedCategoryModule A Y)
    (b : (integrationTwistedFunctor A f W).obj K ⟶ R.obj K) :
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map b ≫ adj.counit.app K =
        integrationCounit A f W t hP K ↔
      b = integrationTranspose A f R adj W t hP K := by
  unfold integrationTranspose
  change (adj.homEquiv _ _).symm b = _ ↔ _
  exact (adj.homEquiv _ _).symm_apply_eq

/-- Transport along the integration isomorphism has exactly the integration counit,
and unit gamma⁻¹ eta; these actual maps satisfy both triangles.
Source: cor-pur-vector-bundle-purity.proof.md, paragraphs 1--2
(blueprint: lem-pur-integration-transpose-base-change).
Proof: compose the original Hom bijection with gamma inverse and use
lem-weil-pbc-adjunction-of-natural-bijection. Evaluating at identities gives the
specified unit and counit; the latter is c by integrationTranspose_unique. In the
left triangle cancel F(gamma) F(gamma inverse) before the original left triangle.
For the right triangle use naturality of gamma at c_K and of eta at gamma_K,
then cancel gamma inverse gamma using the original right triangle. -/
theorem integrationTranspose_transport {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f] (R : DerivedCategoryModule A Y ⥤ DerivedCategoryModule A X)
    (adj : rightDerivedLowerShriek (ModuleCat.{u + 1} A) f ⊣ R)
    (W : DerivedCategoryModule A X)
    (t : (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj W ⟶ 𝟙_ _)
    (hP : ∀ K : DerivedCategoryModule A Y, IsIso (compactProjectionMapCoeffFirst A f K W))
    (γ : integrationTwistedFunctor A f W ≅ R)
    (hγ : γ.hom = integrationTransposeNatTrans A f R adj W t hP) :
    (∀ K : DerivedCategoryModule A Y,
      (adj.ofNatIsoRight γ.symm).counit.app K =
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map (γ.hom.app K) ≫
          adj.counit.app K ∧
      (adj.ofNatIsoRight γ.symm).counit.app K = integrationCounit A f W t hP K) ∧
    (∀ M : DerivedCategoryModule A X,
      (adj.ofNatIsoRight γ.symm).unit.app M =
        adj.unit.app M ≫ γ.inv.app ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj M)) ∧
    (∀ M : DerivedCategoryModule A X,
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map
          (adj.unit.app M ≫ γ.inv.app
            ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj M)) ≫
        integrationCounit A f W t hP
          ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj M) =
        𝟙 ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj M)) ∧
    (∀ K : DerivedCategoryModule A Y,
      adj.unit.app ((integrationTwistedFunctor A f W).obj K) ≫
        γ.inv.app ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj
          ((integrationTwistedFunctor A f W).obj K)) ≫
        (integrationTwistedFunctor A f W).map (integrationCounit A f W t hP K) =
          𝟙 ((integrationTwistedFunctor A f W).obj K)) := by
  have hc (K : DerivedCategoryModule A Y) :
      (adj.ofNatIsoRight γ.symm).counit.app K = integrationCounit A f W t hP K := by
    change (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map (γ.hom.app K) ≫
      adj.counit.app K = _
    apply (integrationTranspose_unique A f R adj W t hP K _).2
    exact congrArg (fun α ↦ α.app K) hγ
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro K
    exact ⟨by simp [Adjunction.ofNatIsoRight_counit], hc K⟩
  · intro M
    simp [Adjunction.ofNatIsoRight_unit]
  · intro M
    simpa only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
      Functor.whiskerLeft_app, Iso.symm_hom, ← hc] using
      (adj.ofNatIsoRight γ.symm).left_triangle_components M
  · intro K
    simpa only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
      Functor.whiskerLeft_app, Iso.symm_hom, ← hc, Category.assoc] using
      (adj.ofNatIsoRight γ.symm).right_triangle_components K

/-- The proper/open exchange, in derived inverse-image coordinates. This is the
recorded exact exchange conjugated by Lg* = D(g*), with no new exchange choice.
Source: cor-pur-vector-bundle-purity.proof.md, paragraph 2
(blueprint: lem-pur-integration-transpose-base-change). -/
def integrationExchangeIso {X X' Y Y' : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian X'] [IsNoetherian Y] [IsNoetherian Y']
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {g' : X' ⟶ X}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification f] [HasCompactification f'] [QuasiCompact f']
    (sq : IsPullback g' f' f g) :
    rightDerivedLowerShriek (ModuleCat.{u + 1} A) f ⋙
        (upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor ≅
      (upperStar (ModuleCat.{u + 1} A) g').leftDerivedFunctor ⋙
        rightDerivedLowerShriek (ModuleCat.{u + 1} A) f' :=
  letI := (unboundedEtaleCompactSupport_baseChange A sq).1
  Functor.isoWhiskerLeft _ (leftDerivedUpperStarIsoMapDerivedCategory _ g) ≪≫
    asIso (unboundedEtaleCompactSupportBaseChange A sq) ≪≫
    Functor.isoWhiskerRight (leftDerivedUpperStarIsoMapDerivedCategory _ g').symm _

private lemma integrationExchangeIso_hom_app {X X' Y Y' : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian X'] [IsNoetherian Y] [IsNoetherian Y']
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {g' : X' ⟶ X}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification f] [HasCompactification f'] [QuasiCompact f']
    (sq : IsPullback g' f' f g) (M : DerivedCategoryModule A X) :
    (integrationExchangeIso A sq).hom.app M =
      (rightDerivedLowerShriekBaseChangeMap A sq).app M := by
  simp only [integrationExchangeIso, unboundedEtaleCompactSupportBaseChange,
    Iso.trans_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    asIso_hom, Iso.symm_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Category.assoc, Iso.hom_inv_id_app_assoc,
    ← Functor.map_comp, Iso.hom_inv_id_app]
  rw [(rightDerivedLowerShriek (ModuleCat.{u + 1} A) f').map_id]
  exact Category.comp_id _

/-- The tensor/pullback comparison followed by l, with its canonical pullback square.
Source: cor-pur-vector-bundle-purity.proof.md, paragraph 2
(blueprint: lem-pur-integration-transpose-base-change). -/
def integrationTensorBaseChangeIso {X X' Y Y' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {g' : X' ⟶ X}
    (sq : IsPullback g' f' f g) (W : DerivedCategoryModule A X)
    (W' : DerivedCategoryModule A X')
    (l : (upperStar (ModuleCat.{u + 1} A) g').leftDerivedFunctor.obj W ≅ W')
    (K : DerivedCategoryModule A Y) :
    (upperStar (ModuleCat.{u + 1} A) g').leftDerivedFunctor.obj
        ((integrationTwistedFunctor A f W).obj K) ≅
      (integrationTwistedFunctor A f' W').obj
        ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj K) :=
  leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) g' _ W ≪≫
    ((derivedTensor (ModuleCat.{u + 1} A) X').mapIso
      ((derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq.toCommSq).symm.app K)).app
        ((upperStar (ModuleCat.{u + 1} A) g').leftDerivedFunctor.obj W) ≪≫
    ((derivedTensor (ModuleCat.{u + 1} A) X').obj
      ((upperStar (ModuleCat.{u + 1} A) f').leftDerivedFunctor.obj
        ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj K))).mapIso l

/-- The exceptional exchange e_K is the transpose of C_RK inverse followed by g*epsilon_K.
Source: cor-pur-vector-bundle-purity.proof.md, paragraph 2
(blueprint: lem-pur-integration-transpose-base-change). -/
def integrationExceptionalExchange {X X' Y Y' : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian X'] [IsNoetherian Y] [IsNoetherian Y']
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {g' : X' ⟶ X}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification f] [HasCompactification f'] [QuasiCompact f']
    (sq : IsPullback g' f' f g)
    (R : DerivedCategoryModule A Y ⥤ DerivedCategoryModule A X)
    (R' : DerivedCategoryModule A Y' ⥤ DerivedCategoryModule A X')
    (adj : rightDerivedLowerShriek (ModuleCat.{u + 1} A) f ⊣ R)
    (adj' : rightDerivedLowerShriek (ModuleCat.{u + 1} A) f' ⊣ R')
    (K : DerivedCategoryModule A Y) :
    (upperStar (ModuleCat.{u + 1} A) g').leftDerivedFunctor.obj (R.obj K) ⟶
      R'.obj ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj K) :=
  adj'.homEquiv _ _ ((integrationExchangeIso A sq).inv.app (R.obj K) ≫
    (upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.map (adj.counit.app K))

/-- Base change of the specified transposes, and its conditional invertibility.
Source: cor-pur-vector-bundle-purity.proof.md, paragraphs 1--2
(blueprint: lem-pur-integration-transpose-base-change).
Proof: apply lem-asd-compact-projection-exchange, naturality in l, and the trace equation.
Cancel the two invertible projection maps to obtain c' F'(a) C = g*c. By
lem-amb-mate-unit-counit and naturality of C at gamma, the transpose of g'*gamma followed
by e is C inverse followed by g*c. The transpose of a followed by gamma' is the same
map by lem-weil-pbc-adjunct-counit-identity. Injectivity of the Hom bijection gives the
asserted equality. If both gamma families are isomorphisms, solve this equality for e;
it is gamma' composed with a and the inverse of g'*gamma, hence invertible. All objects
are arbitrary unbounded complexes; no constructibility or finite-Tor condition enters. -/
theorem integrationTranspose_baseChange {X X' Y Y' : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian X'] [IsNoetherian Y] [IsNoetherian Y']
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {g' : X' ⟶ X}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification f] [HasCompactification f'] [QuasiCompact f']
    (sq : IsPullback g' f' f g)
    (R : DerivedCategoryModule A Y ⥤ DerivedCategoryModule A X)
    (R' : DerivedCategoryModule A Y' ⥤ DerivedCategoryModule A X')
    (adj : rightDerivedLowerShriek (ModuleCat.{u + 1} A) f ⊣ R)
    (adj' : rightDerivedLowerShriek (ModuleCat.{u + 1} A) f' ⊣ R')
    (W : DerivedCategoryModule A X) (W' : DerivedCategoryModule A X')
    (l : (upperStar (ModuleCat.{u + 1} A) g').leftDerivedFunctor.obj W ≅ W')
    (t : (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj W ⟶ 𝟙_ _)
    (t' : (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f').obj W' ⟶ 𝟙_ _)
    (ht : (integrationExchangeIso A sq).hom.app W ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f').map l.hom ≫ t' =
      (upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.map t ≫
        (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) g).hom)
    (hP : ∀ K : DerivedCategoryModule A Y, IsIso (compactProjectionMapCoeffFirst A f K W))
    (hP' : ∀ L : DerivedCategoryModule A Y', IsIso (compactProjectionMapCoeffFirst A f' L W'))
    (K : DerivedCategoryModule A Y) :
    ((upperStar (ModuleCat.{u + 1} A) g').leftDerivedFunctor.map
        (integrationTranspose A f R adj W t hP K) ≫
      integrationExceptionalExchange A sq R R' adj adj' K =
        (integrationTensorBaseChangeIso A sq W W' l K).hom ≫
          integrationTranspose A f' R' adj' W' t' hP'
            ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj K)) ∧
    ((∀ M : DerivedCategoryModule A Y, IsIso (integrationTranspose A f R adj W t hP M)) →
      (∀ L : DerivedCategoryModule A Y', IsIso (integrationTranspose A f' R' adj' W' t' hP' L)) →
      IsIso (integrationExceptionalExchange A sq R R' adj adj' K)) := by
  let F := rightDerivedLowerShriek (ModuleCat.{u + 1} A) f
  let F' := rightDerivedLowerShriek (ModuleCat.{u + 1} A) f'
  let H := (upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor
  let J := (upperStar (ModuleCat.{u + 1} A) g').leftDerivedFunctor
  let C := integrationExchangeIso A sq
  let a := integrationTensorBaseChangeIso A sq W W' l K
  have hc : F'.map a.hom ≫ integrationCounit A f' W' t' hP' (H.obj K) =
      C.inv.app ((integrationTwistedFunctor A f W).obj K) ≫
        H.map (integrationCounit A f W t hP K) := by
    let S := derivedTensor (ModuleCat.{u + 1} A) Y
    let S' := derivedTensor (ModuleCat.{u + 1} A) Y'
    let P := compactProjectionMapCoeffFirst A f K W
    let P' := compactProjectionMapCoeffFirst A f' (H.obj K) W'
    let μ := ((leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} A) g).app K).app
      (F.obj W)
    have hp : H.map P ≫ C.hom.app ((integrationTwistedFunctor A f W).obj K) ≫
        F'.map a.hom =
      μ ≫ (S'.obj (H.obj K)).map (C.hom.app W ≫ F'.map l.hom) ≫ P' := by
      have h := compactProjectionMapCoeffFirst_baseChangeMap A sq W K
      rw [← integrationExchangeIso_hom_app A sq,
        ← integrationExchangeIso_hom_app A sq] at h
      dsimp only [a, integrationTensorBaseChangeIso, Iso.trans_hom, Iso.app_hom,
        Functor.mapIso_hom, Iso.symm_hom]
      simp only [Functor.map_comp, Category.assoc, leftDerivedUpperStarTensorIso_hom]
      dsimp only [H, F', F, P, C, μ, S', P', integrationTwistedFunctor,
        Functor.comp_obj, derivedTensorRight, Functor.flip_obj_obj]
      change _ ≫ _ ≫ _ ≫ _ ≫ _ = _
      dsimp only [derivedSquareUpperStarIsoInvApp] at h
      rw [reassoc_of% h]
      rw [← compactProjection_naturality_right A f' (H.obj K) l.hom]
    have htrace : μ ≫ (S'.obj (H.obj K)).map (C.hom.app W ≫ F'.map l.hom) ≫
        (S'.obj (H.obj K)).map t' ≫
        (derivedTensorRightUnitor (ModuleCat.{u + 1} A) Y' (H.obj K)).hom =
      H.map ((S.obj K).map t ≫
        (derivedTensorRightUnitor (ModuleCat.{u + 1} A) Y K).hom) := by
      rw [← (S'.obj (H.obj K)).map_comp_assoc, Category.assoc, ht]
      rw [(S'.obj (H.obj K)).map_comp]
      dsimp only [μ, S', H, F]
      simp only [Category.assoc]
      have hn := leftDerivedUpperStarTensorIso_hom_naturality_right g K t
      simp only [leftDerivedUpperStarTensorIso_hom] at hn
      rw [← reassoc_of% hn]
      rw [tensorRightUnitor_pullback]
      exact (H.map_comp _ _).symm
    have := hP K
    have := hP' (H.obj K)
    apply (cancel_epi (C.hom.app ((integrationTwistedFunctor A f W).obj K))).1
    simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
    apply (cancel_epi (H.map P)).1
    simp only [Category.assoc]
    rw [reassoc_of% hp]
    dsimp only [integrationCounit]
    change μ ≫ (S'.obj (H.obj K)).map (C.hom.app W ≫ F'.map l.hom) ≫
        P' ≫ inv P' ≫ (S'.obj (H.obj K)).map t' ≫
          (derivedTensorRightUnitor (ModuleCat.{u + 1} A) Y' (H.obj K)).hom =
      H.map P ≫ H.map (inv P ≫ (S.obj K).map t ≫
        (derivedTensorRightUnitor (ModuleCat.{u + 1} A) Y K).hom)
    rw [IsIso.hom_inv_id_assoc, ← H.map_comp, IsIso.hom_inv_id_assoc]
    exact htrace
  have he : J.map (integrationTranspose A f R adj W t hP K) ≫
      integrationExceptionalExchange A sq R R' adj adj' K =
    a.hom ≫ integrationTranspose A f' R' adj' W' t' hP' (H.obj K) := by
    apply (adj'.homEquiv _ _).symm.injective
    rw [adj'.homEquiv_naturality_left_symm, adj'.homEquiv_naturality_left_symm]
    simp only [integrationExceptionalExchange, integrationTranspose]
    dsimp only [H, J]
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    change F'.map (J.map (integrationTranspose A f R adj W t hP K)) ≫
        (C.inv.app (R.obj K) ≫ H.map (adj.counit.app K)) =
      F'.map a.hom ≫ integrationCounit A f' W' t' hP' (H.obj K)
    rw [reassoc_of% (C.inv.naturality
      (integrationTranspose A f R adj W t hP K))]
    change C.inv.app _ ≫ H.map (F.map _) ≫ H.map (adj.counit.app K) = _
    rw [← H.map_comp]
    rw [(integrationTranspose_unique A f R adj W t hP K _).2 rfl]
    exact hc.symm
  refine ⟨he, ?_⟩
  intro hγ hγ'
  have := hγ K
  have := hγ' (H.obj K)
  have : IsIso (J.map (integrationTranspose A f R adj W t hP K) ≫
      integrationExceptionalExchange A sq R R' adj adj' K) := by
    rw [he]
    infer_instance
  exact IsIso.of_isIso_comp_left
    (J.map (integrationTranspose A f R adj W t hP K)) _

end AlgebraicGeometry.Etale
