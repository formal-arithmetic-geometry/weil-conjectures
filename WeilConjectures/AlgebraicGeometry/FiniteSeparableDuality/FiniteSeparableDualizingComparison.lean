/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportGraphDerivedIsoSupplement
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Data
public import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceConstruction
public import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceTower
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleAmbientAdjointLocality
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMaps
public import WeilConjectures.SixFunctors.Etale.Derived.GenericFibre.InternalHom
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
public import WeilConjectures.CategoryTheory.SixFunctors.OrdinaryModuleDerivedInternalHom
public import WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteKInjectiveResolutionsMixedUniverses
public import WeilConjectures.CategoryTheory.SmoothPurity.QuasiIsoHomComplexMapMixedUniverses
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
public import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceCompactComparisonRestriction
public import WeilConjectures.AlgebraicGeometry.Affine.Space.AffineSpaceTopTrace
public import Mathlib.FieldTheory.Separable
public import WeilConjectures.Compactification.NagataCompactification

import all WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
import WeilConjectures.AlgebraicGeometry.IndEtaleInternalHomComparisonCoherence
import WeilConjectures.AlgebraicGeometry.Derived.DerivedPullbackCompositionMonoidal

/-!
# Separable algebraic base change of ordinary etale duality

Source: latest blueprint, det-pd-biduality-coefficients.proof.md (i), finite-base-field
paragraph; expert Wei Yang #1412, item 14
(blueprint: lem-sf-finite-separable-dualizing-comparison).

All categories here are ordinary unbounded derived categories on the small etale site.
The exceptional and Hom comparisons are the published counit mate and evaluation transpose.
The coordinate tower `affineTraceTower S N` is canonically affine N-space over S via
`affineTraceAffineSpaceIso`; its dimension-zero member is S itself.

## Main statements

* `finite_separable_dualizing_comparison`: the canonical dualizing and Hom isomorphisms,
  their evaluation normalization and naturality, and bounded-constructible conservativity.
* `counit_and_finite_etale_normalization`: the actual compact-support counit and finite
  etale sum/evaluation normalization.
* `comparison_transitivity` and `comparison_open_restriction`: the two coherence laws.
* `comparison_closed_affine_chart`: the same-dimension trace-normalized chart formula.

## Main definitions

`homComparison`, `sumComparison`, `openRestrictionIso` and `chartIso` assemble the specified
maps from the published adjunctions. The remaining definitions name their canonical
composition, purity, compact-support exchange, inverse-image and Tate identifications.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale.FiniteSeparableDuality

variable (A : Type (u + 1)) [CommRing A] [Finite A]

universe v w
open TwoSquare

private lemma exchange_at_chosen
    (F : CompactSupportFormalism.{w, v, u}) [F.HasProperExchange]
    {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X}
    [HasCompactification f] [HasCompactification f'] [QuasiCompact f']
    (sq : IsPullback g' f' f g) (c' : Compactification f')
    (h : c'.Z ⟶ (HasCompactification.compactification f).Z)
    (hi : IsPullback g' c'.i (HasCompactification.compactification f).i h)
    (hp : IsPullback h c'.g (HasCompactification.compactification f).g g) :
    F.lowerShriekBaseChange sq =
      (F.shriekBaseChange (HasCompactification.compactification f) c' h hi hp).whiskerBottom
        (F.shriekIso c' (HasCompactification.compactification f')).hom := by
  dsimp only [CompactSupportFormalism.lowerShriekBaseChange, TwoSquare.whiskerBottom]
  rw [shriekBaseChange_arbitrary F sq (HasCompactification.compactification f) c' h hi hp]
  rw [← F.shriekIso_trans (Compactification.ofIsPullback sq
    (HasCompactification.compactification f)) c'
    (HasCompactification.compactification f')]
  ext K
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
    TwoSquare.mk, TwoSquare.natTrans, Category.assoc]

private lemma exchange_chosen_paste
    (F : CompactSupportFormalism.{w, v, u}) [F.HasProperExchange]
    {X X' X'' Y Y' Y'' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {f'' : X'' ⟶ Y''}
    {b : Y' ⟶ Y} {a : Y'' ⟶ Y'} {b' : X' ⟶ X} {a' : X'' ⟶ X'}
    [HasCompactification f] [HasCompactification f'] [HasCompactification f'']
    [QuasiCompact f'] [QuasiCompact f'']
    (sq₁ : IsPullback b' f' f b) (sq₂ : IsPullback a' f'' f' a)
    (sq₃ : IsPullback (a' ≫ b') f'' f (a ≫ b)) :
    F.lowerShriekBaseChange sq₃ =
      ((F.lowerShriekBaseChange sq₁ ≫ᵥ F.lowerShriekBaseChange sq₂).whiskerLeft
        (F.pbComp a' b').inv).whiskerRight (F.pbComp a b).hom := by
  let c := HasCompactification.compactification f
  let c' := c.ofIsPullback sq₁
  let c'' := c'.ofIsPullback sq₂
  let h₁ : c''.Z ⟶ c'.Z := pullback.fst c'.g a
  let h₂ : c'.Z ⟶ c.Z := pullback.fst c.g b
  have hi₁ := c'.isPullback_i_ofIsPullback sq₂
  have hp₁ := (c'.isPullback_g_ofIsPullback sq₂).flip
  have hi₂ := c.isPullback_i_ofIsPullback sq₁
  have hp₂ := (c.isPullback_g_ofIsPullback sq₁).flip
  have hi := hi₁.paste_horiz hi₂
  have hp := hp₁.paste_horiz hp₂
  rw [exchange_at_chosen F sq₃ c'' (h₁ ≫ h₂) hi hp,
    exchange_at_chosen F sq₁ c' h₂ hi₂ hp₂,
    chosenBaseChange_arbitrary F sq₂ c' c'' h₁ hi₁ hp₁,
    F.shriekBaseChange_paste_horiz c c' c'' h₁ h₂ hi₁ hp₁ hi₂ hp₂ hi hp]
  ext K
  simp only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.whiskerLeft,
    TwoSquare.whiskerRight, TwoSquare.vComp, TwoSquare.mk, TwoSquare.natTrans,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.assoc, ExchangeFormalism.pbComp'_rfl,
    Functor.comp_obj]
  simp only [Functor.map_comp, Category.assoc]
  rw [← F.shriekIso_symm c' (HasCompactification.compactification f')]
  have hc : (F.pb a).map
        ((F.shriekIso c' (HasCompactification.compactification f')).hom.app
          ((F.pb b').obj K)) ≫
      (F.pb a).map
        ((F.shriekIso c' (HasCompactification.compactification f')).inv.app
          ((F.pb b').obj K)) = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id]
  simp only [Iso.symm_hom]
  rw [reassoc_of% hc]
  erw [((F.shriekIso c''
    (HasCompactification.compactification f'')).hom.naturality
      ((F.pbComp a' b').inv.app K))]
  rfl


attribute [local instance] unbounded_has_base_change unbounded_has_proper_exchange

-- The public normalization theorem has extra geometric hypotheses; its formal proof does not.
private lemma chosen_base_change_general
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' Y Y' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {v : Y' ⟶ Y} {v' : X' ⟶ X}
    [HasCompactification f] [HasCompactification f'] [QuasiCompact f']
    (sq : IsPullback v' f' f v) :
    ((unboundedFormalism A).lowerShriekBaseChange sq).natTrans =
      unboundedEtaleCompactSupportBaseChange A sq := by
  let B := ModuleCat.{u + 1} A
  let c := HasCompactification.compactification f
  dsimp only [CompactSupportFormalism.lowerShriekBaseChange, TwoSquare.whiskerBottom]
  rw [shriek_base_change_general, unbounded_shriek_iso]
  rw [unboundedEtaleCompactSupportExchange, unboundedEtaleCompactSupportBaseChange,
    rightDerivedLowerShriekBaseChangeMap]
  ext K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.assoc]
  apply congrArg (fun t ↦ _ ≫ _ ≫ t)
  exact (rightDerivedLowerShriekIso A (c.ofIsPullback sq)).hom.naturality
    ((leftDerivedUpperStarIsoMapDerivedCategory B v').hom.app K)


private theorem exchange_comp_general
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' X'' Y Y' Y'' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {f'' : X'' ⟶ Y''}
    {v : Y' ⟶ Y} {w : Y'' ⟶ Y'} {v' : X' ⟶ X} {w' : X'' ⟶ X'}
    [HasCompactification f] [HasCompactification f'] [HasCompactification f'']
    [QuasiCompact f'] [QuasiCompact f'']
    (sq₁ : IsPullback v' f' f v) (sq₂ : IsPullback w' f'' f' w)
    (sq₃ : IsPullback (w' ≫ v') f'' f (w ≫ v)) :
    unboundedEtaleCompactSupportBaseChange A sq₃ =
      Functor.whiskerLeft (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f)
        (unboundedEtaleUpperStarCompIso A w v).hom ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (unboundedEtaleCompactSupportBaseChange A sq₁)
        (upperStar (ModuleCat.{u + 1} A) w).mapDerivedCategory ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (upperStar (ModuleCat.{u + 1} A) v').mapDerivedCategory
        (unboundedEtaleCompactSupportBaseChange A sq₂) ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (unboundedEtaleUpperStarCompIso A w' v').inv
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f'') := by
  have h := congrArg TwoSquare.natTrans
    (exchange_chosen_paste (unboundedFormalism A) sq₁ sq₂ sq₃)
  have hc {S T U : Scheme.{u}} (a : S ⟶ T) (b : T ⟶ U) :
      (unboundedFormalism A).pbComp a b = unboundedEtaleUpperStarCompIso A a b := rfl
  rw [hc, hc] at h
  simp only [chosen_base_change_general, TwoSquare.whiskerLeft,
    TwoSquare.whiskerRight, TwoSquare.vComp, TwoSquare.mk, TwoSquare.natTrans] at h
  change (_ : (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f ⋙
      (upperStar (ModuleCat.{u + 1} A) (w ≫ v)).mapDerivedCategory ⟶
      (upperStar (ModuleCat.{u + 1} A) (w' ≫ v')).mapDerivedCategory ⋙
        rightDerivedLowerShriek (ModuleCat.{u + 1} A) f'')) = _ at h
  simp only [Category.assoc] at h
  exact h

attribute [local irreducible] unboundedEtaleCompactSupportBaseChange


private theorem exchange_paste (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' X'' Y Y' Y'' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {f'' : X'' ⟶ Y''}
    {v : Y' ⟶ Y} {w : Y'' ⟶ Y'} {v' : X' ⟶ X} {w' : X'' ⟶ X'}
    [HasCompactification f] [HasCompactification f'] [HasCompactification f'']
    [QuasiCompact f'] [QuasiCompact f'']
    (sq₁ : IsPullback v' f' f v) (sq₂ : IsPullback w' f'' f' w)
    (K : DerivedCategoryModule A X) :
    (ordinaryFinitePullback A w).map ((rightDerivedLowerShriekBaseChangeMap A sq₁).app K) ≫
        (rightDerivedLowerShriekBaseChangeMap A sq₂).app
          ((ordinaryFinitePullback A v').obj K) =
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) w v).inv.app _ ≫
        (rightDerivedLowerShriekBaseChangeMap A (sq₂.paste_horiz sq₁)).app K ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f'').map
          ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) w' v').hom.app K) := by
  have h := congr_app (exchange_comp_general A sq₁ sq₂
    (sq₂.paste_horiz sq₁)) K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    unboundedEtaleCompactSupportBaseChange,
    unboundedEtaleUpperStarCompIso, Iso.trans_hom, Iso.trans_inv, Functor.map_comp,
    Category.assoc] at h
  apply (cancel_epi ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) w v).hom.app _)).mp
  apply (cancel_mono ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f'').map
    ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) w' v').inv.app K))).mp
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, ← Functor.map_comp,
    Iso.hom_inv_id_app]
  apply (cancel_epi ((leftDerivedUpperStarIsoMapDerivedCategory
    (ModuleCat.{u + 1} A) (w ≫ v)).inv.app _)).mp
  apply (cancel_mono ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f'').map
    ((leftDerivedUpperStarIsoMapDerivedCategory
      (ModuleCat.{u + 1} A) (w' ≫ v')).hom.app K))).mp
  simp only [leftDerivedUpperStarComp, Functor.leftDerivedFunctorNatIso,
    Functor.leftDerivedFunctorCompIso, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_inv, Category.assoc, Iso.inv_hom_id_app_assoc,
    Functor.map_comp]
  simp only [leftDerivedUpperStarIsoMapDerivedCategory, Iso.inv_hom_id_app_assoc,
    ← Functor.map_comp, Iso.inv_hom_id_app, Category.comp_id] at h ⊢
  simp only [Category.id_comp]
  rw [h]
  simp only [Functor.map_comp, ordinaryFinitePullback]
  have hn :=
    (upperStar (ModuleCat.{u + 1} A) w).leftDerivedFunctorIsoMapDerivedCategory.inv.naturality
    ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f').map
      ((upperStar (ModuleCat.{u + 1} A) v').leftDerivedFunctorIsoMapDerivedCategory.hom.app K))
  rw [reassoc_of% hn]
  have he := (rightDerivedLowerShriekBaseChangeMap A sq₂).naturality
    ((upperStar (ModuleCat.{u + 1} A) v').leftDerivedFunctorIsoMapDerivedCategory.hom.app K)
  simp only [Functor.comp_map] at he
  rw [reassoc_of% he]
  rw [← Functor.map_comp_assoc]
  rw [← (upperStar (ModuleCat.{u + 1} A) w').leftDerivedFunctorIsoMapDerivedCategory.hom.naturality]
  simp only [Functor.map_comp, Category.assoc]
  have hlast :=
    (upperStar (ModuleCat.{u + 1} A) w).leftDerivedFunctorIsoMapDerivedCategory.inv.naturality
      ((rightDerivedLowerShriekBaseChangeMap A sq₁).app K)
  simp only [Functor.comp_obj] at hlast
  rw [← reassoc_of% hlast]

-- Pasting the inverse exchanges and taking their exceptional mates.
private theorem exceptional_base_comp
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' X'' Y Y' Y'' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {f'' : X'' ⟶ Y''}
    {v : Y' ⟶ Y} {w : Y'' ⟶ Y'} {v' : X' ⟶ X} {w' : X'' ⟶ X'}
    [HasCompactification f] [HasCompactification f'] [HasCompactification f'']
    [QuasiCompact f'] [QuasiCompact f'']
    (sq₁ : IsPullback v' f' f v) (sq₂ : IsPullback w' f'' f' w)
    (K : DerivedCategoryModule A Y) :
    (rightDerivedUpperShriekBaseChangeMap A (sq₂.paste_horiz sq₁)).app K =
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) w' v').hom.app
        ((rightDerivedUpperShriek A f).obj K) ≫
      (upperStar (ModuleCat.{u + 1} A) w').leftDerivedFunctor.map
        ((rightDerivedUpperShriekBaseChangeMap A sq₁).app K) ≫
      (rightDerivedUpperShriekBaseChangeMap A sq₂).app
        ((upperStar (ModuleCat.{u + 1} A) v).leftDerivedFunctor.obj K) ≫
      (rightDerivedUpperShriek A f'').map
        ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) w v).inv.app K) := by
  have := isIso_rightDerivedLowerShriekBaseChangeMap A sq₁
  have := isIso_rightDerivedLowerShriekBaseChangeMap A sq₂
  have := isIso_rightDerivedLowerShriekBaseChangeMap A (sq₂.paste_horiz sq₁)
  let E₁ := rightDerivedLowerShriekBaseChangeMap A sq₁
  let E₂ := rightDerivedLowerShriekBaseChangeMap A sq₂
  let E₃ := rightDerivedLowerShriekBaseChangeMap A (sq₂.paste_horiz sq₁)
  let c := leftDerivedUpperStarComp (ModuleCat.{u + 1} A) w v
  let c' := leftDerivedUpperStarComp (ModuleCat.{u + 1} A) w' v'
  let δ₁ := TwoSquare.mk _ _ _ _ (inv E₁)
  let δ₂ := TwoSquare.mk _ _ _ _ (inv E₂)
  have h : TwoSquare.mk _ _ _ _ (inv E₃) =
      ((δ₁.hComp δ₂).whiskerTop c'.hom).whiskerBottom c.inv := by
    apply TwoSquare.ext
    intro M
    dsimp only [TwoSquare.whiskerBottom, TwoSquare.whiskerTop, TwoSquare.hComp,
      TwoSquare.mk, TwoSquare.natTrans, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app]
    simp only [Category.id_comp, Category.comp_id, Category.assoc]
    let Vw := (upperStar (ModuleCat.{u + 1} A) w).leftDerivedFunctor
    let F := rightDerivedLowerShriek (ModuleCat.{u + 1} A) f''
    have he : (asIso E₃).app M =
        c.app _ ≪≫ Vw.mapIso ((asIso E₁).app M) ≪≫
          (asIso E₂).app _ ≪≫ F.mapIso (c'.symm.app M) := by
      apply Iso.ext
      apply (cancel_epi (c.inv.app _)).mp
      apply (cancel_mono (F.map (c'.hom.app M))).mp
      simp only [Iso.app_hom, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
        asIso_hom, Category.assoc, Iso.inv_hom_id_app_assoc,
        ← F.map_comp, Iso.inv_hom_id_app]
      have hid := CategoryTheory.Functor.map_id F
        (((upperStar (ModuleCat.{u + 1} A) v').leftDerivedFunctor ⋙
          (upperStar (ModuleCat.{u + 1} A) w').leftDerivedFunctor).obj M)
      rw [hid]
      erw [Category.comp_id]
      exact (exchange_paste A sq₁ sq₂ M).symm
    have hi := congrArg Iso.inv he
    simpa only [Iso.app_inv, asIso_inv, Iso.trans_inv, Functor.mapIso_inv,
      Iso.symm_inv, Category.assoc, Vw, F] using hi
  have hm := congrArg (fun z ↦ z.natTrans.app K)
    (congrArg (mateEquiv
      (rightDerivedUpperShriekAdjunction A f)
      (rightDerivedUpperShriekAdjunction A f'')) h)
  rw [mateEquiv_whiskerTop_whiskerBottom, mateEquiv_vcomp] at hm
  simpa only [rightDerivedUpperShriekBaseChangeMap, δ₁, δ₂, E₁, E₂, E₃,
    TwoSquare.whiskerLeft, TwoSquare.whiskerRight, TwoSquare.vComp,
    TwoSquare.natTrans, TwoSquare.mk, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Category.assoc, c, c'] using hm


private theorem dualizing_base_comp
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' X'' Y Y' Y'' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {f'' : X'' ⟶ Y''}
    {v : Y' ⟶ Y} {w : Y'' ⟶ Y'} {v' : X' ⟶ X} {w' : X'' ⟶ X'}
    [HasCompactification f] [HasCompactification f'] [HasCompactification f'']
    [QuasiCompact f'] [QuasiCompact f'']
    (sq₁ : IsPullback v' f' f v) (sq₂ : IsPullback w' f'' f' w) :
    dualizingComplexBaseChangeMap A (sq₂.paste_horiz sq₁) =
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) w' v').hom.app
        (dualizingComplex A f) ≫
      (upperStar (ModuleCat.{u + 1} A) w').leftDerivedFunctor.map
        (dualizingComplexBaseChangeMap A sq₁) ≫ dualizingComplexBaseChangeMap A sq₂ := by
  have hu := (canonicalDerivedPullbackCompositionMonoidal A v w (𝟙 Y'')
    (𝟙_ _) (𝟙_ _)).2.1
  have hn := (rightDerivedUpperShriekBaseChangeMap A sq₂).naturality
    (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) v).hom
  simp only [Functor.comp_map] at hn
  unfold dualizingComplexBaseChangeMap dualizingComplex
  rw [exceptional_base_comp A sq₁ sq₂]
  simp only [Category.assoc, Functor.map_comp]
  erw [reassoc_of% hn]
  rw [← hu]
  simp only [Functor.map_comp]
  simp only [← Functor.map_comp, Iso.inv_hom_id_app_assoc]


set_option maxHeartbeats 1000000 in
-- Kernel checking the concrete derived closed structures needs a larger heartbeat budget.
attribute [-instance] ModuleCat.MonoidalCategory.instBraidedCategory in
/-- Transitivity of both actual comparison maps under intermediate extensions.
The formulation permits any cartesian presentations and therefore inserts the canonical
inverse-image composition isomorphism explicitly.
Source: latest blueprint det-pd-biduality-coefficients.proof.md (i), expert #1412 item 14
(blueprint: lem-sf-finite-separable-dualizing-comparison).

Proof: compact-support exchange obeys horizontal pasting, so the two dualizing paths have
the same structural adjunct. The triangle identities give the first equation. Transpose
the two Hom paths through tensor-Hom. Both are pullback of evaluation followed by that
same dualizing path; monoidal coherence identifies their tensorators. Injectivity of
transposition gives the second equation. No invertibility or finite-degree restriction
is needed for this formal identity, so it applies also at infinite intermediate fields.
-/
theorem comparison_transitivity {X₀ X₁ X₂ S₀ S₁ S₂ : Scheme.{u}}
    {a₀ : X₀ ⟶ S₀} {a₁ : X₁ ⟶ S₁} {a₂ : X₂ ⟶ S₂}
    {g₁ : X₁ ⟶ X₀} {g₂ : X₂ ⟶ X₁} {h₁ : S₁ ⟶ S₀} {h₂ : S₂ ⟶ S₁}
    [HasCompactification a₀] [HasCompactification a₁] [HasCompactification a₂]
    [QuasiCompact a₁] [QuasiCompact a₂]
    (s₁ : IsPullback g₁ a₁ a₀ h₁) (s₂ : IsPullback g₂ a₂ a₁ h₂)
    (s₁₂ : IsPullback (g₂ ≫ g₁) a₂ a₀ (h₂ ≫ h₁)) :
    dualizingComplexBaseChangeMap A s₁₂ =
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) g₂ g₁).hom.app
          (dualizingComplex A a₀) ≫
        (L((g₂)^*[ModuleCat.{u + 1} A])).map (dualizingComplexBaseChangeMap A s₁) ≫
          dualizingComplexBaseChangeMap A s₂ ∧
    ∀ K : DerivedCategoryModule A X₀,
      homComparison A s₁₂ K =
        (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) g₂ g₁).hom.app
            ((verdierDual A a₀).obj (op K)) ≫
          (L((g₂)^*[ModuleCat.{u + 1} A])).map (homComparison A s₁ K) ≫
            homComparison A s₂ ((L((g₁)^*[ModuleCat.{u + 1} A])).obj K) ≫
              (verdierDual A a₂).map
                ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) g₂ g₁).hom.app K).op := by
  have hd := dualizing_base_comp A s₁ s₂
  change dualizingComplexBaseChangeMap A s₁₂ = _ at hd
  refine ⟨hd, ?_⟩
  intro K
  dsimp only [homComparison, verdierDual, Functor.flip_obj_obj]
  rw [hd]
  simp only [Functor.map_comp, Category.assoc]
  have hc := (indEtaleInternalHomComparison_coherence_and_bounds A g₁ K
    (dualizingComplex A a₀)).1 g₂ g₁ (g₂ ≫ g₁) rfl K (dualizingComplex A a₀)
  rw [reassoc_of% hc]
  erw [reassoc_of% (MonoidalClosed.pre_comm_ihom_map
    ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) g₂ g₁).hom.app K)
    ((L((g₂)^*[ModuleCat.{u + 1} A])).map (dualizingComplexBaseChangeMap A s₁)))]
  erw [MonoidalClosed.pre_comm_ihom_map
    ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) g₂ g₁).hom.app K)
    (dualizingComplexBaseChangeMap A s₂)]
  erw [← derivedHomUpperStarComparison_naturality_assoc
    (ModuleCat.{u + 1} A) g₂ ((L((g₁)^*[ModuleCat.{u + 1} A])).obj K)
    (dualizingComplexBaseChangeMap A s₁)]
  rfl


end AlgebraicGeometry.Etale.FiniteSeparableDuality

#print axioms AlgebraicGeometry.Etale.FiniteSeparableDuality.comparison_transitivity
