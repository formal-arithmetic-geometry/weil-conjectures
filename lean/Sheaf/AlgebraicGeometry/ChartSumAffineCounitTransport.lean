/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q83
-/
module

public import Sheaf.AlgebraicGeometry.AffineSpaceTopTrace
public import Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality
public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.CategoryTheory.Adjunction.Basic

import Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons
import Sheaf.AlgebraicGeometry.AffineTraceRightNormalForm
import Sheaf.AlgebraicGeometry.FiniteEtaleTwistLine
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel

/-!
# Ordered sum-affine chart adjunctions and their actual counits

Source: blueprint main-20261015, sec-smooth-purity/sk-lem-sp-reduction/
sk-lem-sp-reduction-exceptional.proof.md, Charts
(blueprint: lem-sp-chart-sum-affine-counit-transport).

The coordinate tower is the existing affine-space model, including the identity at zero.
The comparisons below are constructed from the published proper/open and common-refinement
comparisons. All asserted model coherence is restricted to bounded-below inputs.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.ChartSumAffine

/-- Canonical composition on three specified models, through the restricted closure.
Source: blueprint Charts, canonical composition comparison
(blueprint: lem-sp-chart-sum-affine-counit-transport). -/
def composition (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y S : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ S}
    [QuasiCompact f] [QuasiCompact (f ≫ g)]
    (ce : Compactification f) (cd : Compactification g) (cg : Compactification (f ≫ g)) :
    rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) ce ⋙
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cd ≅
      rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cg :=
  Functor.isoWhiskerRight
      (rightDerivedLowerShriekOfCompactificationIso A ce (cg.ofComp cd).restrict) _ ≪≫
    rightDerivedLowerShriekOfCompactificationCompIso A cd (cg.ofComp cd) ≪≫
    rightDerivedLowerShriekOfCompactificationIso A (cd.comp (cg.ofComp cd)) cg

/-- Compare the ordered affine left functor to any compactification of its projection.
At zero use the identity model; at a successor use the standard line compactification,
the comparison for the preceding stage, and canonical composition.
Source: blueprint Charts and ordered affine-space construction
(blueprint: lem-sp-chart-sum-affine-counit-transport). -/
def affineComparison (A : Type (u + 1)) [CommRing A] [Finite A]
    (S : Scheme.{u}) [IsNoetherian S] : (d : ℕ) →
    (cd : Compactification (affineTraceProjection S d)) →
    affineTraceLeft A S d ≅
      rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cd
  | 0, cd =>
    ((Functor.isoWhiskerRight
        (mapDerivedCategoryOpenImmersionLowerShriekId (ModuleCat.{u + 1} A) S) _ ≪≫
      Functor.leftUnitor _ ≪≫ rightDerivedLowerStarIdIso A S).symm) ≪≫
      rightDerivedLowerShriekOfCompactificationIso A
        (Compactification.ofIsProper (𝟙 S)) cd
  | d + 1, cd =>
    let cp := HasCompactification.compactification (affineTraceProjection S d)
    Functor.isoWhiskerLeft (affineTraceLineLeft A (affineTraceTower S d))
        (affineComparison A S d cp) ≪≫
      composition A (affineTraceLineCompactification (affineTraceTower S d)) cp cd

/-- The actual ordered affine adjunction transported to the specified left model.
Source: blueprint Charts, ordered affine counit
(blueprint: lem-sp-chart-sum-affine-counit-transport). -/
def affineAdjunction (N : ℕ) (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤)))
    (d : ℕ) (cd : Compactification (affineTraceProjection S d)) :
    rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cd ⊣
      affineTraceRight A N hA S d :=
  (affineTraceAdjunction A N hA t D S hS d).ofNatIsoLeft (affineComparison A S d cd)

/-- The specified chart comparison is alpha after applying F_d to c_e inverse.
Source: blueprint Charts, lambda
(blueprint: lem-sp-chart-sum-affine-counit-transport). -/
def comparison (A : Type (u + 1)) [CommRing A] [Finite A]
    (M : EtaleCompactSupportNormalization A)
    {U V S : Scheme.{u}} [IsNoetherian U] [IsNoetherian V] [IsNoetherian S]
    (e : U ⟶ V) [Etale e] [IsSeparated e] [QuasiCompact e]
    (p : V ⟶ S) [QuasiCompact p]
    (ce : Compactification e) (cd : Compactification p) (cg : Compactification (e ≫ p)) :
    (etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory ⋙
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cd ≅
      rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cg :=
  Functor.isoWhiskerRight (M.comparison e ce).symm _ ≪≫ composition A ce cd cg

/-- The chart comparison in the coordinate model, with its inherited Noetherian structure.
Source: blueprint Charts, lambda
(blueprint: lem-sp-chart-sum-affine-counit-transport). -/
def chartComparison (A : Type (u + 1)) [CommRing A] [Finite A]
    (M : EtaleCompactSupportNormalization A)
    (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    {U : Scheme.{u}} [IsNoetherian U]
    (e : U ⟶ affineTraceTower S d) [Etale e] [IsSeparated e] [QuasiCompact e]
    (ce : Compactification e) (cd : Compactification (affineTraceProjection S d))
    (cg : Compactification (e ≫ affineTraceProjection S d)) :=
  letI := affineTraceNoetherian S d
  comparison A M e (affineTraceProjection S d) ce cd cg

/-- The model-independent right functor H = e* G_d, in the ordered Tate normal form.
Source: blueprint Charts, right adjoint
(blueprint: lem-sp-chart-sum-affine-counit-transport). -/
abbrev right (N : ℕ) (A : Type (u + 1)) [CommRing A] (hA : (N : A) = 0)
    (S : Scheme.{u}) (d : ℕ) {U : Scheme.{u}} (e : U ⟶ affineTraceTower S d) :=
  affineTraceRight A N hA S d ⋙ (upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory

/-- The chart adjunction is the specified sum-then-affine composite transported by lambda.
Source: blueprint Charts, Hom bijection
(blueprint: lem-sp-chart-sum-affine-counit-transport). -/
def adjunction (N : ℕ) (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    (M : EtaleCompactSupportNormalization A)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤)))
    (d : ℕ) {U : Scheme.{u}} [IsNoetherian U]
    (e : U ⟶ affineTraceTower S d) [Etale e] [IsSeparated e] [QuasiCompact e]
    (ce : Compactification e) (cd : Compactification (affineTraceProjection S d))
    (cg : Compactification (e ≫ affineTraceProjection S d)) :
    rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cg ⊣
      affineTraceRight A N hA S d ⋙
        (upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory :=
  letI := affineTraceNoetherian S d
  ((derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) e inferInstance).comp
    (affineAdjunction N A hA t D S hS d cd)).ofNatIsoLeft
      (comparison A M e (affineTraceProjection S d) ce cd cg)

-- The following calculations use the comparison argument of
-- ChartNormalizedModelIdentification on arbitrary normalized data.
-- Refinement normalization and the common-refinement cocycle fix the actual comparison maps.
private theorem comparison_refinement
    (R : Type (u + 1)) [CommRing R] [Finite R]
    (N : EtaleCompactSupportNormalization R)
    {U V : Scheme.{u}} [IsNoetherian U] [IsNoetherian V]
    (e : U ⟶ V) [Etale e] [IsSeparated e]
    {c d : Compactification e} (r : c.Refinement d) :
    (rightDerivedLowerShriekOfCompactificationIso.{u} R d c).hom ≫
      (N.comparison e c).hom = (N.comparison e d).hom := by
  have : IsLocallyNoetherian d.Z := LocallyOfFiniteType.isLocallyNoetherian d.g
  have : CompactSpace d.Z := QuasiCompact.compactSpace_of_compactSpace d.g
  rw [unboundedEtaleCompactSupport_refinement_normalization R e r N]
  simpa only [unboundedEtaleRefinementOpenComparison, Iso.symm_hom, Category.assoc]
    using N.refinement e c d r

private theorem comparison_change
    (R : Type (u + 1)) [CommRing R] [Finite R]
    (N : EtaleCompactSupportNormalization R)
    {U V : Scheme.{u}} [IsNoetherian U] [IsNoetherian V]
    (e : U ⟶ V) [Etale e] [IsSeparated e] (c d : Compactification e) :
    (rightDerivedLowerShriekOfCompactificationIso.{u} R c d).hom ≫
      (N.comparison e d).hom = (N.comparison e c).hom := by
  have h₁ := comparison_refinement R N e (Compactification.infFst c d)
  have h₂ := comparison_refinement R N e (Compactification.infSnd c d)
  rw [← h₂, ← Category.assoc]
  have h := (unboundedEtaleCompactSupport_comparison_coherence R e).2 c d
    (Compactification.inf c d)
  rw [← Iso.trans_hom, h]
  exact h₁

private theorem comparison_inverse_change
    (R : Type (u + 1)) [CommRing R] [Finite R]
    (N : EtaleCompactSupportNormalization R)
    {U V : Scheme.{u}} [IsNoetherian U] [IsNoetherian V]
    (e : U ⟶ V) [Etale e] [IsSeparated e] (c d : Compactification e)
    (K : DerivedCategoryModule R U) :
    (N.comparison e c).inv.app K ≫
        (rightDerivedLowerShriekOfCompactificationIso R c d).hom.app K =
      (N.comparison e d).inv.app K := by
  apply (cancel_mono ((N.comparison e d).hom.app K)).1
  have h := NatTrans.congr_app (comparison_change R N e c d) K
  simp only [NatTrans.comp_app] at h
  rw [Category.assoc, h]
  simp

-- Transport every tower to the chosen models, where the compositor is independent of choices.
set_option backward.isDefEq.respectTransparency false in
private theorem model_composition_to_chosen
    (R : Type (u + 1)) [CommRing R] [Finite R]
    {U V Y : Scheme.{u}} [IsNoetherian U] [IsNoetherian V] [IsNoetherian Y]
    (e : U ⟶ V) (f : V ⟶ Y)
    [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (ce : Compactification e) (cf : Compactification f)
    (cg : Compactification (e ≫ f))
    (K : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} R))) :
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} R) cf).map
        ((rightDerivedLowerShriekIso.{u} R ce).hom.app K) ≫
      (rightDerivedLowerShriekIso.{u} R cf).hom.app
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} R) e).obj K) ≫
      (unboundedEtaleLowerShriekCompIso R e f).hom.app K =
    (composition R ce cf cg).hom.app K ≫
      (rightDerivedLowerShriekIso.{u} R cg).hom.app K := by
  have h := NatTrans.congr_app
    (unboundedEtaleLowerShriekCompIso_tower R e f cf (cg.ofComp cf)) K
  rw [h]
  simp only [NatTrans.comp_app, NatTrans.hcomp_app, composition, Iso.trans_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Category.assoc,
    Iso.hom_inv_id_app_assoc]
  have he : (rightDerivedLowerShriekIso R ce).hom.app K ≫
      (rightDerivedLowerShriekIso R (cg.ofComp cf).restrict).inv.app K =
      (rightDerivedLowerShriekOfCompactificationIso R ce (cg.ofComp cf).restrict).hom.app
        K := by
    apply (cancel_mono
      ((rightDerivedLowerShriekIso R (cg.ofComp cf).restrict).hom.app K)).1
    simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
    exact (congrArg (fun q ↦ q.hom.app K)
      ((unboundedEtaleCompactSupport_comparison_coherence R e).2 ce
        (cg.ofComp cf).restrict (HasCompactification.compactification e))).symm
  have hg := congrArg (fun q ↦ q.hom.app K)
    ((unboundedEtaleCompactSupport_comparison_coherence R (e ≫ f)).2
      (cf.comp (cg.ofComp cf)) cg (HasCompactification.compactification (e ≫ f)))
  simp only [Iso.trans_hom, NatTrans.comp_app] at hg
  simp only [← Functor.map_comp_assoc, he]
  erw [← hg]
  rfl

set_option maxRecDepth 2048 in
private theorem chart_to_chosen
    (R : Type (u + 1)) [CommRing R] [Finite R]
    (N : EtaleCompactSupportNormalization R)
    {U V Y : Scheme.{u}} [IsNoetherian U] [IsNoetherian V] [IsNoetherian Y]
    (e : U ⟶ V) (f : V ⟶ Y) [Etale e] [IsSeparated e]
    [QuasiCompact e] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (ce : Compactification e) (cf : Compactification f)
    (cg : Compactification (e ≫ f))
    (K : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} R))) :
    (comparison R N e f ce cf cg).hom.app K ≫
        (rightDerivedLowerShriekIso.{u} R cg).hom.app K =
      (rightDerivedLowerShriekIso.{u} R cf).hom.app
          ((etaleLowerShriek (ModuleCat.{u + 1} R) e inferInstance).mapDerivedCategory.obj K) ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} R) f).map
          ((N.comparison e (HasCompactification.compactification e)).inv.app K) ≫
        (unboundedEtaleLowerShriekCompIso R e f).hom.app K := by
  simp only [comparison, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Iso.symm_hom, Functor.whiskerRight_app, Category.assoc]
  rw [← model_composition_to_chosen R e f ce cf cg K]
  rw [← (rightDerivedLowerShriekIso.{u} R cf).hom.naturality_assoc]
  rw [← Functor.map_comp_assoc, rightDerivedLowerShriekIso, comparison_inverse_change]
  rfl

private theorem chart_change
    (R : Type (u + 1)) [CommRing R] [Finite R]
    (N : EtaleCompactSupportNormalization R)
    {U V Y : Scheme.{u}} [IsNoetherian U] [IsNoetherian V] [IsNoetherian Y]
    (e : U ⟶ V) (f : V ⟶ Y) [Etale e] [IsSeparated e]
    [QuasiCompact e] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (ce ce' : Compactification e) (cf cf' : Compactification f)
    (cg cg' : Compactification (e ≫ f))
    (K : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} R))) :
    (rightDerivedLowerShriekOfCompactificationIso.{u} R cf cf').hom.app
          ((etaleLowerShriek (ModuleCat.{u + 1} R) e inferInstance).mapDerivedCategory.obj K) ≫
        (comparison R N e f ce' cf' cg').hom.app K =
      (comparison R N e f ce cf cg).hom.app K ≫
        (rightDerivedLowerShriekOfCompactificationIso.{u} R cg cg').hom.app K := by
  apply (cancel_mono ((rightDerivedLowerShriekIso.{u} R cg').hom.app K)).1
  simp only [Category.assoc]
  rw [chart_to_chosen R N e f ce' cf' cg' K]
  have hf := NatTrans.congr_app (congrArg Iso.hom
    ((unboundedEtaleCompactSupport_comparison_coherence R f).2 cf cf'
      (HasCompactification.compactification f)))
      ((etaleLowerShriek (ModuleCat.{u + 1} R) e inferInstance).mapDerivedCategory.obj K)
  have hg := NatTrans.congr_app (congrArg Iso.hom
    ((unboundedEtaleCompactSupport_comparison_coherence R (e ≫ f)).2 cg cg'
      (HasCompactification.compactification (e ≫ f)))) K
  simp only [Iso.trans_hom, NatTrans.comp_app] at hf hg
  rw [← Category.assoc, ← Category.assoc]
  erw [hf]
  erw [hg]
  simpa only [rightDerivedLowerShriekIso, Category.assoc] using
    (chart_to_chosen R N e f ce cf cg K).symm

private theorem composition_change_target
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y S : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian S]
    (f : X ⟶ Y) (g : Y ⟶ S)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (cf : Compactification f) (cg : Compactification g)
    (c c' : Compactification (f ≫ g))
    (K : DerivedCategoryModule A X) :
    (composition A cf cg c).hom.app K ≫
        (rightDerivedLowerShriekOfCompactificationIso A c c').hom.app K =
      (composition A cf cg c').hom.app K := by
  apply (cancel_mono ((rightDerivedLowerShriekIso A c').hom.app K)).1
  have h := congrArg (fun q ↦ q.hom.app K)
    ((unboundedEtaleCompactSupport_comparison_coherence A (f ≫ g)).2 c c'
      (HasCompactification.compactification (f ≫ g)))
  simp only [Iso.trans_hom, NatTrans.comp_app] at h
  simp only [Category.assoc, rightDerivedLowerShriekIso]
  rw [h]
  exact (model_composition_to_chosen A f g cf cg c K).symm.trans
    (model_composition_to_chosen A f g cf cg c' K)

private theorem affineComparison_change
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (c c' : Compactification (affineTraceProjection S d))
    (K : DerivedCategoryModule A (affineTraceTower S d)) :
    (affineComparison A S d c).hom.app K ≫
        (rightDerivedLowerShriekOfCompactificationIso A c c').hom.app K =
      (affineComparison A S d c').hom.app K := by
  cases d with
  | zero =>
    have h := congrArg (fun q ↦ q.hom.app K)
      ((unboundedEtaleCompactSupport_comparison_coherence A (𝟙 S)).2
        (Compactification.ofIsProper (𝟙 S)) c c')
    simpa only [affineComparison, Iso.trans_hom, NatTrans.comp_app, Category.assoc] using
      congrArg (fun q ↦
        (((Functor.isoWhiskerRight
          (mapDerivedCategoryOpenImmersionLowerShriekId (ModuleCat.{u + 1} A) S) _ ≪≫
          Functor.leftUnitor _ ≪≫ rightDerivedLowerStarIdIso A S).symm).hom.app K) ≫ q) h
  | succ d =>
    let := affineTraceNoetherian S d
    let : IsNoetherian (AffineSpace PUnit.{u + 1} (affineTraceTower S d)) :=
      affineTraceNoetherian S (d + 1)
    simp only [affineComparison, Iso.trans_hom, NatTrans.comp_app, Category.assoc]
    rw [composition_change_target]

private theorem transport_counit
    {C D : Type*} [Category C] [Category D]
    {P F F' : C ⥤ D} {R : D ⥤ C}
    (a : P ⊣ R) (e : P ≅ F) (e' : P ≅ F') (r : F ≅ F') (K : D)
    (h : e.hom.app (R.obj K) ≫ r.hom.app (R.obj K) = e'.hom.app (R.obj K)) :
    r.hom.app (R.obj K) ≫ (a.ofNatIsoLeft e').counit.app K =
      (a.ofNatIsoLeft e).counit.app K := by
  simp only [Adjunction.ofNatIsoLeft_counit, NatTrans.comp_app, Functor.whiskerLeft_app]
  apply (cancel_epi (e.hom.app (R.obj K))).1
  simp only [← Category.assoc, h, Iso.hom_inv_id_app, Category.id_comp]

private theorem right_plus
    (N : ℕ) (hN : 0 < N) (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : (N : A) = 0) (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    {U : Scheme.{u}} (e : U ⟶ affineTraceTower S d)
    (K : DerivedCategory.Plus (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    _root_.DerivedCategory.TStructure.t.plus
      ((right N A hA S d e).obj (DerivedCategory.Plus.ι.obj K)) := by
  let X := affineTraceTower S d
  let L := Scheme.finiteEtaleTateSheaf A N X hA (d : ℤ)
  let B := (ordinaryFinitePullback A (affineTraceProjection S d)).obj
    (DerivedCategory.Plus.ι.obj K)
  have hB : _root_.DerivedCategory.TStructure.t.plus B :=
    _root_.DerivedCategory.TStructure.t.plus.prop_of_iso
      ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A)
        (affineTraceProjection S d)).app (DerivedCategory.Plus.ι.obj K)).symm
      (((upperStar (ModuleCat.{u + 1} A) (affineTraceProjection S d)).mapDerivedCategoryPlus.obj
        K).property)
  have hX := affineTraceInvertible N S hS d
  have hstalk : ∀ x : X, IsUnit (N : X.presheaf.stalk x) := by
    intro x
    simpa only [map_natCast] using hX.map (X.presheaf.germ ⊤ x (by trivial)).hom
  have hf : ObjectProperty.flat L :=
    (ObjectProperty.flat_iff_preservesFiniteLimits _).2
      (Scheme.finite_etale_torsion_twist_line X N hN hstalk A hA d).2.2.1
  obtain ⟨n, hn⟩ := hB
  have : B.IsGE n := hn
  let T := (_root_.DerivedCategory.singleFunctor _ 0).obj L
  have ht := _root_.DerivedCategory.torAmplitudeIn_singleFunctor_obj_of_flat hf
  have : (T ⊗ B).IsGE (0 + n) :=
    _root_.DerivedCategory.isGE_tensor_of_torAmplitudeIn ht B n
  obtain ⟨_⟩ := _root_.DerivedCategory.nonempty_braidedCategory
    (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
  have : (B ⊗ T).IsGE (0 + n) :=
    _root_.DerivedCategory.TStructure.t.isGE_of_iso (β_ T B) _
  have hb : _root_.DerivedCategory.TStructure.t.plus ((B ⊗ T)⟦2 * (d : ℤ)⟧) :=
    ⟨0 + n - 2 * (d : ℤ), _root_.DerivedCategory.TStructure.t.isGE_shift _
      (0 + n) (2 * (d : ℤ)) (0 + n - 2 * (d : ℤ)) (by omega)⟩
  obtain ⟨q⟩ := (affineTraceRight_normalForm A N hN hA S hS d).1
  have ha : _root_.DerivedCategory.TStructure.t.plus
      ((affineTraceRight A N hA S d).obj (DerivedCategory.Plus.ι.obj K)) :=
    _root_.DerivedCategory.TStructure.t.plus.prop_of_iso
      (q.app (DerivedCategory.Plus.ι.obj K)).symm hb
  obtain ⟨m, hm⟩ := ha
  have := hm
  exact ⟨m, (upperStar (ModuleCat.{u + 1} A) e).isGE_mapDerivedCategory_obj _ m⟩

/-- The specified chart Hom map and actual sum-then-affine counit are invariant under
changes of all three compactification models. All comparison identities are evaluated
on bounded-below inputs; the constructions themselves use ordinary unbounded categories.
The tower is canonically affine d-space, its right functor is the existing Tate normal
form, and its zeroth adjunction is the existing identity adjunction.

Source: blueprint main-20261015, sec-smooth-purity/sk-lem-sp-reduction/
sk-lem-sp-reduction-exceptional.proof.md, Charts
(blueprint: lem-sp-chart-sum-affine-counit-transport).

Proof:
1. Use lem-amb-affine-space-top-trace's ordered adjunction and transport it by
   affineComparison. Compose the exact degreewise sum/evaluation adjunction first,
   using def-sp-etale-adjoint-chart-comparison and def-weil-pbc-composite-adjunction.
   Its counit delta is F_d(v_{G_d K}) followed by the actual affine counit. Exact sum
   and inverse image, proper right derived image, Tate tensor and shift preserve D+.
2. The defined chartComparison is alpha F_d(c_e inverse). Apply
   lem-sfb-adjunction-transport-left-iso: the Hom map precomposes by lambda, and the
   inverse Hom map sends the identity to lambda inverse followed by delta.
3. Graph normalization gives c'_e rho_e = c_e. Canonical composition's independence
   in lem-amb-etale-compact-comparisons gives alpha' F'_d(rho_e)(rho_d F_e) = rho_g alpha.
   Naturality of rho_d at c_e inverse gives lambda'(rho_d E) = rho_g lambda.
   In particular changing only ce leaves lambda and the chart adjunction unchanged.
4. Coherence gives kappa' = kappa rho_d. Transporting the same ordered counit gives
   rho_d at G_d K followed by epsilon'_d = epsilon_d. Naturality at the sum counit
   gives rho_d at E H K followed by delta' = delta.
5. Evaluate step 3 at H K, invert lambda, and substitute step 4 to obtain the chart
   counit identity. For three models, apply the common-refinement cocycles for d
   and g and substitute them in these same identities. The sum adjunction depends
   only on e. At dimension zero the ordered adjunction is literally the identity,
   so the formula reduces to the sum counit with the canonical identity comparison.
-/
theorem counit_transport (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    (M : EtaleCompactSupportNormalization A)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    {U : Scheme.{u}} [IsNoetherian U]
    (e : U ⟶ affineTraceTower S d) [Etale e] [IsSeparated e] [QuasiCompact e]
    (ce : Compactification e) [IsNoetherian ce.Z]
    (cd : Compactification (affineTraceProjection S d)) [IsNoetherian cd.Z]
    (cg : Compactification (e ≫ affineTraceProjection S d)) [IsNoetherian cg.Z] :
    (∀ (K : DerivedCategory.Plus (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A))),
      _root_.DerivedCategory.TStructure.t.plus
        ((right N A hA S d e).obj (DerivedCategory.Plus.ι.obj K))) ∧
    (∀ (L : DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)))
      (K : DerivedCategory.Plus (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)))
      (a : (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cg).obj
        (DerivedCategory.Plus.ι.obj L) ⟶ DerivedCategory.Plus.ι.obj K),
      (adjunction N A hA t D M S hS d e ce cd cg).homEquiv _ _ a =
        (derivedEtaleLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} A) e inferInstance).homEquiv _ _
          ((affineAdjunction N A hA t D S hS d cd).homEquiv _ _
            ((chartComparison A M S d e ce cd cg).hom.app
              (DerivedCategory.Plus.ι.obj L) ≫ a))) ∧
    (∀ (K : DerivedCategory.Plus (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A))),
      (adjunction N A hA t D M S hS d e ce cd cg).counit.app
          (DerivedCategory.Plus.ι.obj K) =
        (chartComparison A M S d e ce cd cg).inv.app
            ((right N A hA S d e).obj (DerivedCategory.Plus.ι.obj K)) ≫
          (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cd).map
            ((derivedEtaleLowerShriekUpperStarAdjunction
              (ModuleCat.{u + 1} A) e inferInstance).counit.app
                ((affineTraceRight A N hA S d).obj (DerivedCategory.Plus.ι.obj K))) ≫
          (affineAdjunction N A hA t D S hS d cd).counit.app
            (DerivedCategory.Plus.ι.obj K)) ∧
    (∀ (ce' : Compactification e) [IsNoetherian ce'.Z]
      (cd' : Compactification (affineTraceProjection S d)) [IsNoetherian cd'.Z]
      (cg' : Compactification (e ≫ affineTraceProjection S d)) [IsNoetherian cg'.Z],
      (∀ (K : DerivedCategory.Plus (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A))),
        (rightDerivedLowerShriekOfCompactificationIso A cg cg').hom.app
            ((right N A hA S d e).obj (DerivedCategory.Plus.ι.obj K)) ≫
          (adjunction N A hA t D M S hS d e ce' cd' cg').counit.app
            (DerivedCategory.Plus.ι.obj K) =
          (adjunction N A hA t D M S hS d e ce cd cg).counit.app
            (DerivedCategory.Plus.ι.obj K)) ∧
      (∀ (K : DerivedCategory.Plus (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A))),
        (rightDerivedLowerShriekOfCompactificationIso A cd cd').hom.app
            (((etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory).obj
              ((right N A hA S d e).obj (DerivedCategory.Plus.ι.obj K))) ≫
          ((derivedEtaleLowerShriekUpperStarAdjunction
            (ModuleCat.{u + 1} A) e inferInstance).comp
              (affineAdjunction N A hA t D S hS d cd')).counit.app
                (DerivedCategory.Plus.ι.obj K) =
          ((derivedEtaleLowerShriekUpperStarAdjunction
            (ModuleCat.{u + 1} A) e inferInstance).comp
              (affineAdjunction N A hA t D S hS d cd)).counit.app
                (DerivedCategory.Plus.ι.obj K)) ∧
      (∀ (L : DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))),
        (chartComparison A M S d e ce cd cg).hom.app (DerivedCategory.Plus.ι.obj L) ≫
            (rightDerivedLowerShriekOfCompactificationIso A cg cg').hom.app
              (DerivedCategory.Plus.ι.obj L) =
          (rightDerivedLowerShriekOfCompactificationIso A cd cd').hom.app
              (((etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory).obj
                (DerivedCategory.Plus.ι.obj L)) ≫
            (chartComparison A M S d e ce' cd' cg').hom.app (DerivedCategory.Plus.ι.obj L)) ∧
      (∀ (L : DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))),
        (chartComparison A M S d e ce cd cg).hom.app (DerivedCategory.Plus.ι.obj L) =
          (chartComparison A M S d e ce' cd cg).hom.app (DerivedCategory.Plus.ι.obj L)) ∧
      (∀ (cd'' : Compactification (affineTraceProjection S d)) [IsNoetherian cd''.Z]
        (cg'' : Compactification (e ≫ affineTraceProjection S d)) [IsNoetherian cg''.Z]
        (L : DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)))
        (K : DerivedCategory.Plus
          (Sheaf (affineTraceTower S d).smallEtaleTopology (ModuleCat.{u + 1} A))),
        (rightDerivedLowerShriekOfCompactificationIso A cg cg').hom.app
              (DerivedCategory.Plus.ι.obj L) ≫
            (rightDerivedLowerShriekOfCompactificationIso A cg' cg'').hom.app
              (DerivedCategory.Plus.ι.obj L) =
          (rightDerivedLowerShriekOfCompactificationIso A cg cg'').hom.app
            (DerivedCategory.Plus.ι.obj L) ∧
        (rightDerivedLowerShriekOfCompactificationIso A cd cd').hom.app
              (DerivedCategory.Plus.ι.obj K) ≫
            (rightDerivedLowerShriekOfCompactificationIso A cd' cd'').hom.app
              (DerivedCategory.Plus.ι.obj K) =
          (rightDerivedLowerShriekOfCompactificationIso A cd cd'').hom.app
            (DerivedCategory.Plus.ι.obj K))) := by
  let := affineTraceNoetherian S d
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact right_plus N hN A hA S hS d e
  · intro L K a
    simp only [adjunction, chartComparison, Adjunction.homEquiv_ofNatIsoLeft_apply,
      Adjunction.comp_homEquiv]
    rfl
  · intro K
    simp only [adjunction, chartComparison, Adjunction.ofNatIsoLeft_counit,
      NatTrans.comp_app, Functor.whiskerLeft_app, Adjunction.comp_counit_app]
  · intro ce' _ cd' _ cg' _
    have hc (K : DerivedCategoryModule A S) :
        (rightDerivedLowerShriekOfCompactificationIso A cd cd').hom.app
            ((affineTraceRight A N hA S d).obj K) ≫
          (affineAdjunction N A hA t D S hS d cd').counit.app K =
        (affineAdjunction N A hA t D S hS d cd).counit.app K := by
      exact transport_counit (affineTraceAdjunction A N hA t D S hS d)
        (affineComparison A S d cd) (affineComparison A S d cd')
        (rightDerivedLowerShriekOfCompactificationIso A cd cd') K
        (affineComparison_change A S d cd cd' _)
    have hd (K : DerivedCategoryModule A S) :
        (rightDerivedLowerShriekOfCompactificationIso A cd cd').hom.app
            ((etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory.obj
              ((right N A hA S d e).obj K)) ≫
          ((derivedEtaleLowerShriekUpperStarAdjunction
            (ModuleCat.{u + 1} A) e inferInstance).comp
              (affineAdjunction N A hA t D S hS d cd')).counit.app K =
        ((derivedEtaleLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} A) e inferInstance).comp
            (affineAdjunction N A hA t D S hS d cd)).counit.app K := by
      simp only [Adjunction.comp_counit_app]
      rw [← Category.assoc,
        ← (rightDerivedLowerShriekOfCompactificationIso A cd cd').hom.naturality,
        Category.assoc, hc]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro K
      let B := (right N A hA S d e).obj (DerivedCategory.Plus.ι.obj K)
      have hl := chart_change A M e (affineTraceProjection S d)
        ce ce' cd cd' cg cg' B
      have hi : (rightDerivedLowerShriekOfCompactificationIso A cg cg').hom.app B ≫
            (comparison A M e (affineTraceProjection S d) ce' cd' cg').inv.app B =
          (comparison A M e (affineTraceProjection S d) ce cd cg).inv.app B ≫
            (rightDerivedLowerShriekOfCompactificationIso A cd cd').hom.app
              ((etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory.obj
                B) := by
        apply (cancel_epi
          ((comparison A M e (affineTraceProjection S d) ce cd cg).hom.app B)).1
        rw [← Category.assoc, ← hl]
        simp only [Category.assoc, Iso.hom_inv_id_app, Iso.hom_inv_id_app_assoc]
        exact Category.comp_id _
      simp only [adjunction, Adjunction.ofNatIsoLeft_counit,
        NatTrans.comp_app, Functor.whiskerLeft_app]
      rw [← Category.assoc, hi, Category.assoc, hd]
    · intro K
      exact hd _
    · intro L
      exact (chart_change A M e (affineTraceProjection S d)
        ce ce' cd cd' cg cg' (DerivedCategory.Plus.ι.obj L)).symm
    · intro L
      have h := chart_change A M e (affineTraceProjection S d)
        ce ce' cd cd cg cg (DerivedCategory.Plus.ι.obj L)
      have hd0 := (unboundedEtaleCompactSupport_comparison_coherence A
        (affineTraceProjection S d)).1 cd
      have hg0 := (unboundedEtaleCompactSupport_comparison_coherence A
        (e ≫ affineTraceProjection S d)).1 cg
      simpa only [hd0, hg0, Iso.refl_hom, NatTrans.id_app,
        Category.id_comp, Category.comp_id, chartComparison] using h.symm
    · intro cd'' _ cg'' _ L K
      constructor
      · exact congrArg (fun q ↦ q.hom.app (DerivedCategory.Plus.ι.obj L))
          ((unboundedEtaleCompactSupport_comparison_coherence A
            (e ≫ affineTraceProjection S d)).2 cg cg' cg'')
      · exact congrArg (fun q ↦ q.hom.app (DerivedCategory.Plus.ι.obj K))
          ((unboundedEtaleCompactSupport_comparison_coherence A
            (affineTraceProjection S d)).2 cd cd' cd'')

end AlgebraicGeometry.Etale.ChartSumAffine
