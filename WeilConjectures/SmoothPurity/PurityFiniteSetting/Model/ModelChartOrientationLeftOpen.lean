/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Model.ModelChartOrientationRestrictionDefinitions
import WeilConjectures.SmoothPurity.PurityFiniteSetting.DiagonalPasting.PurityDiagonalSectionPasting
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Diagonal.DiagonalEtaleLocalityUnitChange
import WeilConjectures.AlgebraicGeometry.Vector.VectorIntegrationBaseCoefficientComposition

/-! # Open naturality of the left orientation composite -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

private theorem chart_left_reading (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (r : ℕ) (h : X ⟶ Y)
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [SmoothOfRelativeDimension r h]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates) :
    letI := P.noetherian aY
    letI := P.noetherian (h ≫ aY)
    letI := Dnc.compactifiable P h aY
    letI := P.comparedExponent (𝟙 (Spec (.of P.field.k)))
    P.chartDiagonalDelta r h aY ≪≫ P.chartDiagonalBeta r h aY t =
      Dnc.sourceComparison P r (pullback.fst h h) (h ≫ aY) (pullback.diagonal h) ≪≫
        (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.mapIso
          (DiagonalPasting.alpha P.Coefficient P r h (h ≫ aY) ≪≫
            P.chartDualizingUnit h ≪≫ P.chartOrdinaryOrientation r h aY) := by
  let := P.noetherian aY
  let := P.noetherian (h ≫ aY)
  let := Dnc.compactifiable P h aY
  let := P.comparedExponent (𝟙 (Spec (.of P.field.k)))
  have hn := P.diagonal_dnc_chart_normalization r h aY t
  have hs := (P.chartOrdinaryOrientation_spec r h aY).2
  have he := congrArg (fun z ↦ P.chartDiagonalAlpha r h aY ≪≫ z) hn
  simp only [chartDiagonalAssembly, Iso.self_symm_id_assoc] at he
  rw [hs] at he
  rw [← he]
  simp only [chartDiagonalAlpha, Functor.mapIso_trans, Iso.trans_assoc,
    Iso.symm_self_id_assoc]
  rfl

private theorem etale_restriction_inverse (P : PurityFiniteSetting.{u})
    {U X Y : Scheme.{u}} [IsNoetherian U] [IsNoetherian X] [IsNoetherian Y]
    (j : U ⟶ X) [Etale j] [IsSeparated j] [LocallyOfFiniteType j] [QuasiCompact j]
    (h : X ⟶ Y) [HasCompactification h] [HasCompactification (j ≫ h)] :
    letI := P.comparedExponent (𝟙 (Spec (.of P.field.k)))
    (DiagonalPasting.etaleRestriction P.Coefficient P j h).symm =
      Etale.sectionStructuralLocalityIso P.Coefficient j h (j ≫ h) rfl := by
  let := P.comparedExponent (𝟙 (Spec (.of P.field.k)))
  let H := Etale.existsUnique_etaleAmbientAdjointLocalityIso P.Coefficient j h
    (HasCompactification.compactification h)
    (HasCompactification.compactification (j ≫ h))
    (Etale.rightDerivedUpperShriek P.Coefficient h)
    (Etale.rightDerivedUpperShriek P.Coefficient (j ≫ h))
    (Etale.rightDerivedUpperShriekAdjunction P.Coefficient h)
    (Etale.rightDerivedUpperShriekAdjunction P.Coefficient (j ≫ h))
  have he : Classical.choose H.exists = Classical.choose H :=
    H.unique H.exists.choose_spec (Classical.choose_spec H).1
  simp only [DiagonalPasting.etaleRestriction, DiagonalPasting.restrictionUnit,
    Iso.trans_symm, Iso.symm_symm_eq]
  change _ ≪≫ (Classical.choose H.exists).app _ =
    _ ≪≫ (Classical.choose H).app _
  rw [he]

private theorem ordinary_target_open (P : PurityFiniteSetting.{u})
    {X Y X' Y' : Scheme.{u}} (r : ℕ) (h : X ⟶ Y)
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [SmoothOfRelativeDimension r h]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (v : Y' ⟶ Y) [IsOpenImmersion v] [QuasiCompact v]
    (h' : X' ⟶ Y') [IsSeparated h'] [LocallyOfFiniteType h'] [QuasiCompact h']
    [SmoothOfRelativeDimension r h']
    (j : X' ⟶ X) (sq : IsPullback j h' h v)
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates) :
    letI := Dnc.compactifiable P h aY
    letI := Dnc.compactifiable P h' (v ≫ aY)
    letI := P.comparedExponent (𝟙 (Spec (.of P.field.k)))
    (Etale.ordinaryFinitePullback P.Coefficient j).mapIso
        (P.chartDualizingUnit h ≪≫ P.chartOrdinaryOrientation r h aY) ≪≫
      Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates t j (P.diagonalExponent_isUnit (h ≫ aY)) r =
      DiagonalPasting.beta P.Coefficient P r sq (h ≫ aY) ≪≫
        P.chartDualizingUnit h' ≪≫ P.chartOrdinaryOrientation r h' (v ≫ aY) := by
  let := Dnc.compactifiable P h aY
  let := Dnc.compactifiable P h' (v ≫ aY)
  let := P.comparedExponent (𝟙 (Spec (.of P.field.k)))
  have hs := P.chartOrientation_open_baseChange r h aY v h' j sq t
  apply Iso.ext
  have he := congrArg (fun z ↦
    (Etale.ordinaryFinitePullback P.Coefficient j).map (P.chartDualizingUnit h).hom ≫ z) hs
  simp only [chartOrdinaryBaseChange, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id] at he
  erw [(Etale.ordinaryFinitePullback P.Coefficient j).map_id, Category.id_comp] at he
  simpa only [DiagonalPasting.beta, Iso.trans_hom, Functor.mapIso_hom] using he

private theorem ordinary_source_open (P : PurityFiniteSetting.{u})
    {U X Y : Scheme.{u}} (r : ℕ) (h : X ⟶ Y)
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [SmoothOfRelativeDimension r h]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (j : U ⟶ X) [Etale j] [IsSeparated j] [LocallyOfFiniteType j] [QuasiCompact j]
    [SmoothOfRelativeDimension r (j ≫ h)]
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates) :
    letI := P.noetherian aY
    letI := P.noetherian (h ≫ aY)
    letI := P.noetherian ((j ≫ h) ≫ aY)
    letI := Dnc.compactifiable P h aY
    letI := Dnc.compactifiable P (j ≫ h) aY
    letI := P.comparedExponent (𝟙 (Spec (.of P.field.k)))
    (Etale.ordinaryFinitePullback P.Coefficient j).mapIso
        (P.chartDualizingUnit h ≪≫ P.chartOrdinaryOrientation r h aY) ≪≫
      Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates t j (P.diagonalExponent_isUnit (h ≫ aY)) r =
      (DiagonalPasting.etaleRestriction P.Coefficient P j h).symm ≪≫
        P.chartDualizingUnit (j ≫ h) ≪≫ P.chartOrdinaryOrientation r (j ≫ h) aY := by
  let := P.noetherian aY
  let := P.noetherian (h ≫ aY)
  let := P.noetherian ((j ≫ h) ≫ aY)
  let := Dnc.compactifiable P h aY
  let := Dnc.compactifiable P (j ≫ h) aY
  let := P.comparedExponent (𝟙 (Spec (.of P.field.k)))
  let N := Etale.canonicalEtaleCompactSupportNormalization P.Coefficient
  have hs := P.chartOrientation_etale_restriction r h aY j N t
  have hu := P.diagonalEtaleLocality_unitChange N j h (j ≫ h) rfl
  rw [etale_restriction_inverse]
  apply Iso.ext
  simp only [Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  rw [hs]
  have hu' := congrArg Iso.hom hu
  simpa only [OrientationCounit.unitChange, chartDualizingUnit, smoothPurityUnitIso,
    diagonalDualizingCongr, eqToIso_refl, Iso.trans_hom, Iso.refl_hom,
    Functor.mapIso_hom, Category.comp_id, Category.assoc] using
    congrArg (fun z ↦ z ≫ (P.chartOrdinaryOrientation r (j ≫ h) aY).hom) hu'

private theorem orientation_congr (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (r : ℕ) (h h' : X ⟶ Y)
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [IsSeparated h'] [LocallyOfFiniteType h'] [QuasiCompact h']
    [SmoothOfRelativeDimension r h] [SmoothOfRelativeDimension r h']
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (w : h = h') :
    letI := P.noetherian aY
    letI := Dnc.compactifiable P h aY
    letI := Dnc.compactifiable P h' aY
    letI := P.comparedExponent (𝟙 (Spec (.of P.field.k)))
    DiagonalPasting.dualizingCongr P.Coefficient P w ≪≫
      P.chartDualizingUnit h' ≪≫ P.chartOrdinaryOrientation r h' aY =
      P.chartDualizingUnit h ≪≫ P.chartOrdinaryOrientation r h aY := by
  subst h'
  simp only [DiagonalPasting.dualizingCongr, Iso.refl_trans]

private theorem ordinary_open (P : PurityFiniteSetting.{u})
    {X Y X' Y' : Scheme.{u}} [IsAffine X] [IsAffine Y] [IsAffine X'] [IsAffine Y']
    (r : ℕ) (h : X ⟶ Y) (h' : X' ⟶ Y') (j : X' ⟶ X) (v : Y' ⟶ Y)
    [IsOpenImmersion j] [IsOpenImmersion v]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [IsSeparated h'] [LocallyOfFiniteType h'] [QuasiCompact h']
    [SmoothOfRelativeDimension r h] [SmoothOfRelativeDimension r h']
    (w : j ≫ h = h' ≫ v)
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates) :
    letI := P.noetherian aY
    letI := P.noetherian (h ≫ aY)
    letI := P.noetherian (v ≫ aY)
    letI := P.noetherian (h' ≫ v ≫ aY)
    letI := Dnc.compactifiable P h aY
    letI := Dnc.compactifiable P h' (v ≫ aY)
    letI := P.comparedExponent (𝟙 (Spec (.of P.field.k)))
    (Etale.ordinaryFinitePullback P.Coefficient j).mapIso
        (P.chartDualizingUnit h ≪≫ P.chartOrdinaryOrientation r h aY) ≪≫
      Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates t j (P.diagonalExponent_isUnit (h ≫ aY)) r =
      DiagonalPasting.openDualizing P.Coefficient P r h h' j v w (h ≫ aY) ≪≫
        P.chartDualizingUnit h' ≪≫ P.chartOrdinaryOrientation r h' (v ≫ aY) := by
  let := P.noetherian aY
  let := P.noetherian (h ≫ aY)
  let := P.noetherian (v ≫ aY)
  let := P.noetherian (h' ≫ v ≫ aY)
  let := P.comparedExponent (𝟙 (Spec (.of P.field.k)))
  let k := DiagonalPasting.openFactor h h' j v w
  let b := pullback.fst h v
  let q := pullback.snd h v
  have hk := DiagonalPasting.openFactorProperties h h' j v w
  let : IsOpenImmersion k := hk.1
  let : SmoothOfRelativeDimension r q := by
    have := smoothOfRelativeDimension_isStableUnderBaseChange (n := r)
    exact MorphismProperty.pullback_snd h v inferInstance
  let : SmoothOfRelativeDimension r (k ≫ q) := hk.2.2.symm ▸ inferInstance
  let := P.noetherian (q ≫ v ≫ aY)
  let := Dnc.compactifiable P h aY
  let := Dnc.compactifiable P q (v ≫ aY)
  let := Dnc.compactifiable P h' (v ≫ aY)
  let := Dnc.compactifiable P (k ≫ q) (v ≫ aY)
  let A := P.chartDualizingUnit h ≪≫ P.chartOrdinaryOrientation r h aY
  let R := Etale.ordinaryFinitePullback P.Coefficient j
  let K := Etale.ordinaryFinitePullback P.Coefficient k
  let c := Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
    k b j hk.2.1.symm
  have ht := congrArg Iso.hom
    (ordinary_target_open P r h aY v q b (IsPullback.of_hasPullback h v) t)
  have hs := congrArg Iso.hom (ordinary_source_open P r q (v ≫ aY) k t)
  have hc := congrArg Iso.hom (orientation_congr P r (k ≫ q) h' (v ≫ aY) hk.2.2)
  have hp := Etale.vectorIntegrationBaseCoefficientPullback_comp P.Coefficient
    P.diagonalExponent P.diagonalExponent_annihilates t k b j hk.2.1.symm
    (P.diagonalExponent_isUnit (h ≫ aY))
    (P.diagonalExponent_isUnit (q ≫ v ≫ aY)) r
  have hn := c.hom.naturality A.hom
  simp only [Functor.comp_map] at hn
  apply Iso.ext
  simp only [Iso.trans_hom, Functor.mapIso_hom] at ht hs hc ⊢
  change R.map A.hom ≫ _ = _
  rw [← hp]
  erw [reassoc_of% hn]
  erw [← K.map_comp_assoc, ht, K.map_comp]
  simp only [Category.assoc]
  erw [hs]
  dsimp only [DiagonalPasting.openDualizing]
  simp only [c, Etale.leftDerivedUpperStarComp, Iso.trans_hom, Iso.symm_hom,
    Iso.app_hom, NatTrans.comp_app, Functor.mapIso_hom, Category.assoc]
  erw [← hc]
  rfl

private theorem pull_comparison_naturality (P : PurityFiniteSetting.{u})
    {X X' : Scheme.{u}} (j : X' ⟶ X)
    {K L : Etale.DerivedCategoryModule P.Coefficient X} (e : K ≅ L) :
    (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) j).leftDerivedFunctor.mapIso
        ((ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.mapIso e) ≪≫
      Dnc.pullComparison P j L =
      Dnc.pullComparison P j K ≪≫
        (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) X').mapDerivedCategory.mapIso
          ((Etale.ordinaryFinitePullback P.Coefficient j).mapIso e) := by
  let c := OrientationCounit.comparisonPull P j
  have hn := c.hom.naturality e.hom
  apply Iso.ext
  simpa only [c, OrientationCounit.comparisonPull, Dnc.pullComparison,
    OrientationRefinement.pull, Iso.trans_hom, Iso.app_hom, Iso.symm_hom,
    Iso.app_inv, Functor.mapIso_hom, Functor.comp_map,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.assoc] using hn

/-- Open naturality of the total DNC orientation on its actual section source.
Source: model descent Steps 8--9, normalized DNC and normal-bundle restriction.
(blueprint: lem-pur-model-chart-orientation-left-open).

Proof: affine DNC normalization identifies each delta-beta composite with
sourceComparison followed by the ordinary diagonal restriction, the coefficient-unit
change and the unique ordinary chart orientation. This reading is independent of t.
Factor the open square into target-open base change and residual source-open
restriction. The ordinary orientation restriction equations, together with
coefficient-unit naturality of etale locality and composition of Tate pullback,
give the restriction square for these ordinary readings. Use the projective-line
trace transport prescribed by modelOrientationTwistPullback in this calculation.
The total-alpha open clause of diagonal section pasting supplies the source square.
Apply the site comparison functor, use naturality of its pullback comparison,
and cancel the intermediate source comparisons. The result is the displayed
equation with exactly modelChartSectionRestriction on the source. All steps apply
to empty opens and rank zero; no frame or orientation is selected. -/
theorem model_chart_orientation_left_open (P : PurityFiniteSetting.{u})
    {U V T U' V' T' : Scheme.{u}}
    [IsAffine U] [IsAffine V] [IsAffine T]
    [IsAffine U'] [IsAffine V'] [IsAffine T']
    (d e : ℕ) (f : U ⟶ V) (g : V ⟶ T) (f' : U' ⟶ V') (g' : V' ⟶ T')
    (j : U' ⟶ U) (v : V' ⟶ V) (w : T' ⟶ T)
    [IsOpenImmersion j] [IsOpenImmersion v] [IsOpenImmersion w]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [IsSeparated f'] [LocallyOfFiniteType f'] [QuasiCompact f']
    [IsSeparated g'] [LocallyOfFiniteType g'] [QuasiCompact g']
    [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g]
    [SmoothOfRelativeDimension d f'] [SmoothOfRelativeDimension e g']
    (hf : j ≫ f = f' ≫ v) (hg : v ≫ g = g' ≫ w)
    (aT : T ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aT] [QuasiCompact aT]
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates) :
    letI := (DiagonalPasting.geometryProperties d e f g).2.2.2.2
    letI := (DiagonalPasting.geometryProperties d e f' g').2.2.2.2
    (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) j).leftDerivedFunctor.mapIso
        (P.modelChartLeft d e f g aT t) ≪≫
      P.modelOrientationTwistPullback j (f ≫ g ≫ aT) (d + e) =
    P.modelChartSectionRestriction (d + e) (f ≫ g) (f' ≫ g') j w
        (DiagonalPasting.compositeSquare f g f' g' j v w hf hg) aT ≪≫
      P.modelChartLeft d e f' g' (w ≫ aT) t := by
  let := (DiagonalPasting.geometryProperties d e f g).2.2.2.2
  let := (DiagonalPasting.geometryProperties d e f' g').2.2.2.2
  let := P.noetherian aT
  let := P.noetherian (g ≫ aT)
  let := P.noetherian (f ≫ g ≫ aT)
  let := P.noetherian (w ≫ aT)
  let := P.noetherian (g' ≫ w ≫ aT)
  let := P.noetherian (f' ≫ g' ≫ w ≫ aT)
  let := P.comparedExponent (𝟙 (Spec (.of P.field.k)))
  let := Dnc.compactifiable P (f ≫ g) aT
  let := Dnc.compactifiable P (f' ≫ g') (w ≫ aT)
  let J := Etale.ordinaryFinitePullback P.Coefficient j
  let F := (ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} P.Coefficient) U').mapDerivedCategory
  let a := DiagonalPasting.alpha P.Coefficient P (d + e) (f ≫ g) (f ≫ g ≫ aT)
  let a' := DiagonalPasting.alpha P.Coefficient P (d + e) (f' ≫ g')
    (f' ≫ g' ≫ w ≫ aT)
  let b := P.chartDualizingUnit (f ≫ g) ≪≫
    P.chartOrdinaryOrientation (d + e) (f ≫ g) aT
  let b' := P.chartDualizingUnit (f' ≫ g') ≪≫
    P.chartOrdinaryOrientation (d + e) (f' ≫ g') (w ≫ aT)
  let sq := DiagonalPasting.compositeSquare f g f' g' j v w hf hg
  let S := DiagonalPasting.openSection P.Coefficient P (d + e) (f ≫ g) (f' ≫ g')
    j w sq (f ≫ g ≫ aT)
  let O := DiagonalPasting.openDualizing P.Coefficient P (d + e) (f ≫ g) (f' ≫ g')
    j w sq (f ≫ g ≫ aT)
  let t₀ := Etale.projectiveLineTraceTransport P.diagonalExponent
    (pow_pos P.coefficients.prime.out.pos P.level)
    P.Coefficient P.diagonalExponent_annihilates
  let T := Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient
    P.diagonalExponent P.diagonalExponent_annihilates t₀ j
    (P.diagonalExponent_isUnit (f ≫ g ≫ aT)) (d + e)
  have ho : J.mapIso b ≪≫ T = O ≪≫ b' :=
    ordinary_open P (d + e) (f ≫ g) (f' ≫ g') j w sq aT t₀
  have ha := ((DiagonalPasting.diagonalSectionPasting P d e f g aT).2
    f' g' j v w hf hg).1.2.2.1
  have ha' : F.mapIso (J.mapIso a ≪≫ O) = F.mapIso (S ≪≫ a') := by
    apply Iso.ext
    exact ha
  have he : F.mapIso (J.mapIso (a ≪≫ b) ≪≫ T) =
      F.mapIso (S ≪≫ (a' ≪≫ b')) := by
    rw [J.mapIso_trans, Iso.trans_assoc, ho, ← Iso.trans_assoc,
      Functor.mapIso_trans, ha', ← Functor.mapIso_trans, Iso.trans_assoc]
  have hn := pull_comparison_naturality P j (a ≪≫ b)
  simp only [modelChartLeft, chart_left_reading, modelOrientationTwistPullback,
    modelChartSectionRestriction, Functor.mapIso_trans, Iso.trans_assoc]
  apply Iso.ext
  have hn' := congrArg Iso.hom hn
  have he' := congrArg Iso.hom he
  simp only [b, b', Functor.mapIso_trans, Iso.trans_hom, Functor.mapIso_hom,
    Category.assoc] at hn' he'
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc,
    Iso.inv_hom_id_assoc]
  rw [reassoc_of% hn']
  rw [he']
end WeilConjectures.PurityFiniteSetting
