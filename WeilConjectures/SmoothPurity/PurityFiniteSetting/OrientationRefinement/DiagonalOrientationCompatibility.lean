/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.OrientationRefinement.DiagonalOrientationRefinementData
import all WeilConjectures.AlgebraicGeometry.SectionReesBaseChange.SectionReesBaseChangeEtale
import WeilConjectures.SmoothPurity.PurityFiniteSetting.OrientationRefinement.ComparedSmoothExchangeComposition
import WeilConjectures.SmoothPurity.PurityFiniteSetting.SectionRestriction.PuritySectionEtaleRestriction
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Diagonal.DiagonalExchangeNaturality
import all WeilConjectures.AlgebraicGeometry.Vector.VectorIntegrationMate
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Dnc.SmoothSectionExchangeComposition
import WeilConjectures.SmoothPurity.PurityFiniteSetting.OrientationRefinement.VectorZeroSectionIntegrationBaseChange
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Dnc.ComparisonPullbackDerivedCoherence
import all Mathlib.CategoryTheory.Limits.HasLimits
import all Mathlib.Logic.Small.Defs

/-! # Compatibility of normalized diagonal charts under affine restriction

Source: blueprint latest, sec-smooth-purity/sk-prop-sp-orientation,
thm-pur-diagonal-dualizing-object.proof.md, Steps 4--8.
(blueprint: lem-pur-affine-diagonal-orientation-chart-compatibility).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.AffineZariskiSite
namespace WeilConjectures.PurityFiniteSetting.OrientationRefinement

private theorem mapped_adjunct_isIso
    {C D E : Type*} [Category C] [Category D] [Category E]
    {L : C ⥤ D} {R : D ⥤ C} (a : L ⊣ R)
    {X W : C} {Y Z : D} (c : L.obj X ⟶ Y) (e : Y ≅ Z)
    (H : C ⥤ E) (i : X ≅ W) {A : E} (j : H.obj W ≅ A)
    (hc : IsIso (a.homEquiv X Y c)) :
    IsIso (j.inv ≫ H.map (i.inv ≫ a.homEquiv X Z (c ≫ e.hom))) := by
  rw [Adjunction.homEquiv_naturality_right]
  have := hc
  infer_instance

private theorem vector_beta_isIso (P : PurityFiniteSetting.{u}) (B : Scheme.{u})
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB]
    (d : ℕ) (F : B.Modules) [F.IsFiniteLocallyFreeOfRank d] :
    IsIso (vectorBetaInverse P B aB d F) := by
  let := P.noetherian aB
  let := (Etale.vectorIntegration_geometry B d F).1
  let := (Etale.vectorIntegration_geometry B d F).2.1
  let := (Etale.vectorIntegration_geometry B d F).2.2
  let := Dnc.compactifiable P (VectorBundleZeroSection.π B d F) aB
  have hi := Etale.integration_unit_adjunct_isIso P.diagonalExponent
    (pow_pos P.coefficients.prime.out.pos P.level) P.Coefficient
    P.diagonalExponent_annihilates B (P.diagonalExponent_isUnit aB) d F
  dsimp only at hi
  have := hi
  dsimp only [vectorBetaInverse]
  exact mapped_adjunct_isIso
    (Etale.rightDerivedUpperShriekAdjunction P.Coefficient
      (VectorBundleZeroSection.π B d F))
    (Etale.vectorBundleIntegration P.diagonalExponent
      (pow_pos P.coefficients.prime.out.pos P.level) P.Coefficient
      P.diagonalExponent_annihilates B (P.diagonalExponent_isUnit aB) d F)
    (Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} P.Coefficient) B)
    (Etale.ordinaryFinitePullback P.Coefficient (VectorBundleZeroSection.zero B d F))
    (Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates
      (purityTwistTransport P.Coefficient P.diagonalExponent
        (pow_pos P.coefficients.prime.out.pos P.level) P.diagonalExponent_annihilates)
      (VectorBundleZeroSection.π B d F) (P.diagonalExponent_isUnit aB) d)
    (Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates
      (purityTwistTransport P.Coefficient P.diagonalExponent
        (pow_pos P.coefficients.prime.out.pos P.level) P.diagonalExponent_annihilates)
      (VectorBundleZeroSection.zero B d F)
      (P.diagonalExponent_isUnit (VectorBundleZeroSection.π B d F ≫ aB)) d) hi

private theorem baseChange_ext {B B' : Scheme.{u}} {d : ℕ} {b : B' ⟶ B}
    {X : SectionRestriction.Pair B d} {X' : SectionRestriction.Pair B' d}
    (x y : SectionRestriction.BaseChange b X' X) (h : x.map = y.map) : x = y := by
  cases x
  cases y
  congr

private theorem normal_restriction {B B' N N' : Scheme.{u}}
    (g : N ⟶ B) (g' : N' ⟶ B') (s : B ⟶ N) (s' : B' ⟶ N')
    [IsClosedImmersion s] [IsClosedImmersion s']
    (hs : s ≫ g = 𝟙 B) (hs' : s' ≫ g' = 𝟙 B')
    (b : B' ⟶ B) (j : N' ⟶ N) [IsOpenImmersion j]
    (sq : IsPullback j g' g b) (w : s' ≫ j = b ≫ s) :
    ∃ n : s'.ker.normalCone ⟶ s.ker.normalCone,
      n ≫ s.ker.normalConeToDeformationSpace = s'.ker.normalConeToDeformationSpace ≫
        SectionReesBaseChange.pairMap s s' j b w ∧
      IsPullback n (Scheme.Hom.normalConeProj g' s') (Scheme.Hom.normalConeProj g s) b ∧
      s'.normalConeZeroSection ≫ n = b ≫ s.normalConeZeroSection := by
  have centres : IsPullback s' b j s := by
    apply IsPullback.of_right (h₁₂ := g') (h₂₂ := g) ?_ w sq.flip
    simpa only [hs, hs'] using IsPullback.id_horiz b
  have hker : s'.ker = s.ker.comap j := Scheme.Hom.ker_of_isPullback s j centres.flip
  let hJ : ∀ ⦃U' : N'.AffineZariskiSite⦄ ⦃U : N.AffineZariskiSite⦄
      (hU : U'.1 ≤ j ⁻¹ᵁ U.1),
      (s.ker.siteIdeal U).map (j.appLE U.1 U'.1 hU).hom ≤ s'.ker.siteIdeal U' :=
    fun {U' U} hU ↦
      (s.ker.ideal_map_appLE_le_ideal_comap j ⟨U.1, U.2⟩ ⟨U'.1, U'.2⟩ hU).trans
        (Scheme.IdealSheafData.le_def.mp
          (Scheme.Modules.closedImmersion_conormal_functorial s' s j b w).1 ⟨U'.1, U'.2⟩)
  have hc := SectionReesBaseChange.pairMap_compatible g g' s s' j b w sq.w
  obtain ⟨n, _, _, hn, hp, hz, _⟩ := hc.2.2.2
  have hcov : ∀ x : N', ∃ (U' : N'.AffineZariskiSite) (U : N.AffineZariskiSite)
      (hU : U'.1 ≤ j ⁻¹ᵁ U.1), x ∈ U'.1 ∧
      IsPushout (j.appLE U.1 U'.1 hU) (s.ker.toReesPresheaf.app (op U))
        (s'.ker.toReesPresheaf.app (op U'))
        ((Scheme.IdealSheafData.extendedReesPullbackData j s.ker s'.ker hJ).map hU) := by
    intro x
    obtain ⟨U, hU, hx, _⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
      N'.isBasis_affineOpens (show x ∈ (⊤ : N'.Opens) from trivial)
    exact ⟨⟨U, hU⟩, _, _, hx,
      Scheme.IdealSheafData.isPushout_extendedReesPullbackData_imageSite j s.ker s'.ker hJ
        hker ⟨U, hU⟩⟩
  have hq := Scheme.IdealSheafData.isPullback_deformationSpaceMap_proj j s.ker s'.ker hJ
    hcov g g' b sq
  change IsPullback (SectionReesBaseChange.pairMap s s' j b w)
    (Scheme.Hom.deformationSpaceProj g' s') (Scheme.Hom.deformationSpaceProj g s)
    (AffineSpace.map (ULift.{u} (Fin 1)) b) at hq
  have outer := (Scheme.Hom.isPullback_normalConeToDeformationSpace g' s').paste_horiz hq
  rw [AffineSpace.zeroSection_comp_map, ← hn] at outer
  exact ⟨n, hn, IsPullback.of_right outer hp
    (Scheme.Hom.isPullback_normalConeToDeformationSpace g s), hz⟩

private theorem restriction_square {X Y : Scheme.{u}} (f : X ⟶ Y)
    {V V' : Y.Opens} (h : V' ≤ V) :
    IsPullback (inclusion f h) (f ∣_ V') (f ∣_ V) (Y.homOfLE h) := by
  apply IsPullback.of_right (h₁₂ := (f ⁻¹ᵁ V).ι) (h₂₂ := V.ι) ?_
    (morphismRestrict_homOfLE f V' V h).symm (isPullback_morphismRestrict f V).flip
  simpa only [inclusion, X.homOfLE_ι, Y.homOfLE_ι] using
    (isPullback_morphismRestrict f V').flip
private theorem product_square {X Y X' Y' : Scheme.{u}}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (a : X' ⟶ X) (b : Y' ⟶ Y)
    (sq : IsPullback a f' f b) :
    IsPullback (pullback.map f' f' f f a a b sq.w.symm sq.w.symm)
      (pullback.fst f' f') (pullback.fst f f) a := by
  exact IsPullback.paste_twist_right sq (IsPullback.of_hasPullback f f).flip f' a
    sq.w.symm (pullback.snd f' f') (pullback.fst f' f')
    (IsPullback.of_hasPullback f' f').flip (by simp) (by simp)

private theorem geometry_exists {X Y : Scheme.{u}} (f : X ⟶ Y) [IsSeparated f]
    {V V' : Y.affineOpens} (h : V'.1 ≤ V.1) : Nonempty (Geometry f h) := by
  let a := inclusion f h
  have : IsOpenImmersion a := inferInstanceAs (IsOpenImmersion (X.homOfLE (f.preimage_mono h)))
  let b := Y.homOfLE h
  let sq := restriction_square f h
  let p := pullback.map (f ∣_ V'.1) (f ∣_ V'.1) (f ∣_ V.1) (f ∣_ V.1)
    a a b sq.w.symm sq.w.symm
  have hp : p ≫ pullback.fst (f ∣_ V.1) (f ∣_ V.1) =
      pullback.fst (f ∣_ V'.1) (f ∣_ V'.1) ≫ a := by simp [p]
  have hs : p ≫ pullback.snd (f ∣_ V.1) (f ∣_ V.1) =
      pullback.snd (f ∣_ V'.1) (f ∣_ V'.1) ≫ a := by simp [p]
  have hd : pullback.diagonal (f ∣_ V'.1) ≫ p = a ≫ pullback.diagonal (f ∣_ V.1) := by
    apply pullback.hom_ext <;> simp [Category.assoc, hp, hs]
  have hc := product_square (f ∣_ V.1) (f ∣_ V'.1) a b sq
  have : IsOpenImmersion p := MorphismProperty.of_isPullback
    (P := @IsOpenImmersion) hc.flip inferInstance
  obtain ⟨n, hn, hnc, hz⟩ := normal_restriction
    (pullback.fst (f ∣_ V.1) (f ∣_ V.1))
    (pullback.fst (f ∣_ V'.1) (f ∣_ V'.1))
    (pullback.diagonal (f ∣_ V.1)) (pullback.diagonal (f ∣_ V'.1))
    (pullback.diagonal_fst _) (pullback.diagonal_fst _) a p hc hd
  exact ⟨⟨p, hp, hs, hd, hc, n, hn, hnc, hz⟩⟩

attribute [local irreducible] VectorBundleZeroSection.scheme VectorBundleZeroSection.π
  VectorBundleZeroSection.over VectorBundleZeroSection.antiEquivalence
  Etale.rightDerivedLowerShriek Etale.rightDerivedUpperShriek
  Etale.rightDerivedUpperShriekAdjunction
  vectorBetaInverse Dnc.sectionBaseChange Etale.vectorIntegrationBaseCoefficientPullback

private theorem model_beta_compat (P : PurityFiniteSetting.{u})
    {B B' Q Q' : Scheme.{u}}
    [IsNoetherian B] [IsNoetherian B'] [IsNoetherian Q] [IsNoetherian Q']
    (aB : B ⟶ Spec (.of P.field.k)) (aB' : B' ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB]
    [LocallyOfFiniteType aB'] [QuasiCompact aB']
    (d : ℕ) (q : Q ⟶ B) (q' : Q' ⟶ B')
    [HasCompactification q] [HasCompactification q'] [QuasiCompact q] [QuasiCompact q']
    [LocallyOfFiniteType q] [LocallyOfFiniteType q']
    [SmoothOfRelativeDimension d q] [SmoothOfRelativeDimension d q']
    [HasInvertibleExponent P.Coefficient Q] [HasInvertibleExponent P.Coefficient Q']
    (z : B ⟶ Q) (z' : B' ⟶ Q') (b : B' ⟶ B) (n : Q' ⟶ Q)
    (sq : IsPullback n q' q b) (hnzero : z' ≫ n = b ≫ z)
    (F : B.Modules) (F' : B'.Modules)
    [F.IsFiniteLocallyFreeOfRank d] [F'.IsFiniteLocallyFreeOfRank d]
    (e : VectorBundleZeroSection.scheme B d F ≅ Q)
    (e' : VectorBundleZeroSection.scheme B' d F' ≅ Q')
    (he : e.hom ≫ q = VectorBundleZeroSection.π B d F)
    (he' : e'.hom ≫ q' = VectorBundleZeroSection.π B' d F')
    (hz : VectorBundleZeroSection.zero B d F ≫ e.hom = z)
    (hz' : VectorBundleZeroSection.zero B' d F' ≫ e'.hom = z')
    (β : Etale.sectionInvariant P.Coefficient q z ≅ P.diagonalTwistEtale B d)
    (β' : Etale.sectionInvariant P.Coefficient q' z' ≅ P.diagonalTwistEtale B' d) :
    letI := (Etale.vectorIntegration_geometry B d F).1
    letI := (Etale.vectorIntegration_geometry B d F).2.1
    letI := (Etale.vectorIntegration_geometry B' d F').1
    letI := (Etale.vectorIntegration_geometry B' d F').2.1
    letI := Dnc.compactifiable P (VectorBundleZeroSection.π B d F) aB
    letI := Dnc.compactifiable P (VectorBundleZeroSection.π B' d F') aB'
    β.inv ≫ (Etale.leftDerivedUpperStarId (ModuleCat.{u + 1} P.Coefficient) B).inv.app
        (Etale.sectionInvariant P.Coefficient q z) ≫
      (Dnc.sectionBaseChange P.Coefficient d q
        (IsPullback.of_horiz_isIso ⟨he.trans (Category.comp_id _).symm⟩)
        z (VectorBundleZeroSection.zero B d F)
        (hz.trans (Category.id_comp _).symm)).hom = vectorBetaInverse P B aB d F →
    β'.inv ≫ (Etale.leftDerivedUpperStarId (ModuleCat.{u + 1} P.Coefficient) B').inv.app
        (Etale.sectionInvariant P.Coefficient q' z') ≫
      (Dnc.sectionBaseChange P.Coefficient d q'
        (IsPullback.of_horiz_isIso ⟨he'.trans (Category.comp_id _).symm⟩)
        z' (VectorBundleZeroSection.zero B' d F')
        (hz'.trans (Category.id_comp _).symm)).hom = vectorBetaInverse P B' aB' d F' →
    (Etale.ordinaryFinitePullback P.Coefficient b).mapIso β ≪≫
        Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
          P.diagonalExponent_annihilates
          (purityTwistTransport P.Coefficient P.diagonalExponent
            (pow_pos P.coefficients.prime.out.pos P.level) P.diagonalExponent_annihilates)
          b (P.diagonalExponent_isUnit aB) d =
      Dnc.sectionBaseChange P.Coefficient d q sq z z' hnzero ≪≫ β' := by
  intro hn hn'
  let := (Etale.vectorIntegration_geometry B d F).1
  let := (Etale.vectorIntegration_geometry B d F).2.1
  let := (Etale.vectorIntegration_geometry B d F).2.2
  let := (Etale.vectorIntegration_geometry B' d F').1
  let := (Etale.vectorIntegration_geometry B' d F').2.1
  let := (Etale.vectorIntegration_geometry B' d F').2.2
  let := Dnc.compactifiable P (VectorBundleZeroSection.π B d F) aB
  have hq : q = e.inv ≫ VectorBundleZeroSection.π B d F := by
    rw [← he, Iso.inv_hom_id_assoc]
  let : IsAffineHom q := by rw [hq]; infer_instance
  let : IsSeparated q := inferInstance
  have hq' : q' = e'.inv ≫ VectorBundleZeroSection.π B' d F' := by
    rw [← he', Iso.inv_hom_id_assoc]
  let : IsAffineHom q' := by rw [hq']; infer_instance
  let : IsSeparated q' := inferInstance
  let := Dnc.compactifiable P (VectorBundleZeroSection.π B' d F') aB'
  let := (VectorBundleZeroSection.finite_type_frames
    P.field.k B aB d F).choose_spec.2.2.2.2.2.1
  let := Dnc.invertibleExponent P (VectorBundleZeroSection.π B d F ≫ aB)
  let v := e'.hom ≫ n ≫ e.inv
  have hv : v ≫ VectorBundleZeroSection.π B d F =
      VectorBundleZeroSection.π B' d F' ≫ b := by
    dsimp only [v]
    rw [Category.assoc, Category.assoc, ← he, Iso.inv_hom_id_assoc,
      sq.w, ← Category.assoc, he']
  have hzv : VectorBundleZeroSection.zero B' d F' ≫ v =
      b ≫ VectorBundleZeroSection.zero B d F := by
    dsimp only [v]
    rw [← Category.assoc, hz', ← Category.assoc, hnzero, Category.assoc,
      ← hz, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  let sqe : IsPullback e.hom (VectorBundleZeroSection.π B d F) q (𝟙 B) :=
    IsPullback.of_horiz_isIso ⟨he.trans (Category.comp_id _).symm⟩
  let sqe' : IsPullback e'.hom (VectorBundleZeroSection.π B' d F') q' (𝟙 B') :=
    IsPullback.of_horiz_isIso ⟨he'.trans (Category.comp_id _).symm⟩
  let sqv : IsPullback v (VectorBundleZeroSection.π B' d F')
      (VectorBundleZeroSection.π B d F) (b) := by
    have hev : v ≫ e.hom = e'.hom ≫ n := by simp [v]
    have hs : IsPullback (v ≫ e.hom) (VectorBundleZeroSection.π B' d F')
        q (b ≫ 𝟙 B) := by
      simpa only [hev, Category.id_comp, Category.comp_id] using
        sqe'.paste_horiz sq
    exact IsPullback.of_right hs hv sqe
  let c := (Etale.leftDerivedUpperStarId (ModuleCat.{u + 1} P.Coefficient) B).symm.app
      (Etale.sectionInvariant P.Coefficient q z) ≪≫
    Dnc.sectionBaseChange P.Coefficient d q
      (b := 𝟙 B) (f' := VectorBundleZeroSection.π B d F)
      (a := e.hom) sqe z
      (VectorBundleZeroSection.zero B d F) (hz.trans (Category.id_comp _).symm)
  let c' := (Etale.leftDerivedUpperStarId (ModuleCat.{u + 1} P.Coefficient) B').symm.app
      (Etale.sectionInvariant P.Coefficient q' z') ≪≫
    Dnc.sectionBaseChange P.Coefficient d q'
      (b := 𝟙 B') (f' := VectorBundleZeroSection.π B' d F')
      (a := e'.hom) sqe' z'
      (VectorBundleZeroSection.zero B' d F') (hz'.trans (Category.id_comp _).symm)
  let cn := Dnc.sectionBaseChange P.Coefficient d q sq
    z z' hnzero
  let cv := Dnc.sectionBaseChange P.Coefficient d (VectorBundleZeroSection.π B d F)
    sqv (VectorBundleZeroSection.zero B d F) (VectorBundleZeroSection.zero B' d F') hzv
  have hc₁ := Dnc.section_baseChange_comp_right_id P.Coefficient
    (X := Q) (X' := VectorBundleZeroSection.scheme B d F)
    (X'' := VectorBundleZeroSection.scheme B' d F') (B := B) (B' := B') d q
    (VectorBundleZeroSection.π B d F) (VectorBundleZeroSection.π B' d F')
    (b := b) (a := e.hom) (a' := v) sqe sqv z
    (VectorBundleZeroSection.zero B d F)
    (VectorBundleZeroSection.zero B' d F') hz hzv
  have hc₂ := Dnc.section_baseChange_comp_left_id P.Coefficient
    (X := Q) (X' := Q')
    (X'' := VectorBundleZeroSection.scheme B' d F') (B := B) (B' := B') d q q'
    (VectorBundleZeroSection.π B' d F') (b := b)
    (a := n) (a' := e'.hom) sq sqe'
    z z'
    (VectorBundleZeroSection.zero B' d F') hnzero hz'
  have hev : v ≫ e.hom = e'.hom ≫ n := by simp [v]
  have hcs : (Etale.ordinaryFinitePullback P.Coefficient (b)).mapIso c ≪≫ cv =
      cn ≪≫ c' := by
    change (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient)
      (b)).leftDerivedFunctor.mapIso c ≪≫ cv = cn ≪≫ c'
    dsimp only [c, c', cn, cv]
    rw [← hc₁, ← hc₂]
    have hh := Dnc.section_baseChange_congr P.Coefficient d q
      (VectorBundleZeroSection.π B' d F') (b := b) (b' := b)
      (by simpa only [Category.comp_id] using sqv.paste_horiz sqe)
      (by simpa only [Category.id_comp] using sqe'.paste_horiz sq)
      z (VectorBundleZeroSection.zero B' d F')
      (by rw [← Category.assoc, hzv, Category.assoc, hz])
      (by rw [← Category.assoc, hz', hnzero]) hev rfl
    simpa only [eqToIso_refl, Iso.refl_trans] using hh
  have hvec := vector_zero_section_integration_baseChange P B B' aB aB' d F F'
    (b) v sqv hzv
  have hnc : β.inv ≫ c.hom = vectorBetaInverse P B aB d F := by
    dsimp only [c, Iso.trans_hom]
    exact hn
  have hnc' : β'.inv ≫ c'.hom = vectorBetaInverse P B' aB' d F' := by
    dsimp only [c', Iso.trans_hom]
    exact hn'
  have hc : c.hom = β.hom ≫ vectorBetaInverse P B aB d F := by
    exact (cancel_epi β.inv).1 (by
      simpa only [c, Iso.trans_hom, Iso.symm_hom, Iso.app_inv,
        Category.assoc, Iso.inv_hom_id_assoc] using hnc)
  have hc' : c'.hom = β'.hom ≫ vectorBetaInverse P B' aB' d F' := by
    exact (cancel_epi β'.inv).1 (by
      simpa only [c', Iso.trans_hom, Iso.symm_hom, Iso.app_inv,
        Category.assoc, Iso.inv_hom_id_assoc] using hnc')
  let := vector_beta_isIso P B' aB' d F'
  let t := Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
    P.diagonalExponent_annihilates
    (purityTwistTransport P.Coefficient P.diagonalExponent
      (pow_pos P.coefficients.prime.out.pos P.level) P.diagonalExponent_annihilates)
    (b) (P.diagonalExponent_isUnit aB) d
  have hb : (Etale.ordinaryFinitePullback P.Coefficient (b)).mapIso
      β ≪≫ t = cn ≪≫ β' := by
    apply Iso.ext
    apply (cancel_mono (vectorBetaInverse P B' aB' d F')).1
    have hch := congrArg Iso.hom hcs
    simp only [Iso.trans_hom, Functor.mapIso_hom, hc, hc', Functor.map_comp,
      Category.assoc] at hch
    simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
    change (Etale.ordinaryFinitePullback P.Coefficient (b)).map
        (vectorBetaInverse P B aB d F) ≫ cv.hom =
      t.hom ≫ vectorBetaInverse P B' aB' d F' at hvec
    rw [← hvec]
    exact hch
  exact hb

/-- The four comparison equations hold for normalized charts on every nested finite type
affine target open. This is the compatibility component used by the refinement theorem;
it is strictly smaller because it supplies no chart existence, transitivity, or cover.
The proof pastes the smooth exceptional exchanges, the DNC normalized comparison, and
the zero-section integration base-change equation, then cancels the four factors.

(blueprint: lem-pur-affine-diagonal-orientation-chart-compatibility).
-/
theorem diagonalOrientationCompatible (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] (aX : X ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aX] [QuasiCompact aX] (f : X ⟶ Y) (_hf : f ≫ aY = aX)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (d : ℕ) [SmoothOfRelativeDimension d f] :
    ∀ (V V' : Y.affineOpens)
      (_hV : (V.1.ι ≫ aY).appTop.hom.FiniteType)
      (_hV' : (V'.1.ι ≫ aY).appTop.hom.FiniteType)
      (h : V'.1 ≤ V.1),
      ∀ (D : Chart P f aY d V) (D' : Chart P f aY d V'),
        Compatible P f aY d D D' h := by
  intro V V' hV hV' h D D'
  obtain ⟨G⟩ := geometry_exists f h
  let sq := restriction_square f h
  let := D.geometry.separated
  let := D.geometry.finiteType
  let := D.geometry.quasiCompact
  let := D.geometry.smoothDimension
  let := D.geometry.baseFiniteType
  let := D.geometry.baseQuasiCompact
  let := D.geometry.sourceSeparated
  let := D.geometry.sourceFiniteType
  let := D.geometry.sourceQuasiCompact
  let := D'.geometry.separated
  let := D'.geometry.finiteType
  let := D'.geometry.quasiCompact
  let := D'.geometry.smoothDimension
  let := D'.geometry.baseFiniteType
  let := D'.geometry.baseQuasiCompact
  let := D'.geometry.sourceSeparated
  let := D'.geometry.sourceFiniteType
  let := D'.geometry.sourceQuasiCompact
  refine ⟨sq, G, ?_, ?_, ?_, ?_⟩
  · have he := exchange_comp P d f (f ∣_ V.1) (f ∣_ V'.1) aY
      (V.1.ι ≫ aY) (V'.1.ι ≫ aY) (isPullback_morphismRestrict f V.1).flip sq
    have heq := exchange_congr P d f (f ∣_ V'.1) aY (V'.1.ι ≫ aY)
      (sq.paste_horiz (isPullback_morphismRestrict f V.1).flip)
      (isPullback_morphismRestrict f V'.1).flip
      (X.homOfLE_ι (f.preimage_mono h)) (Y.homOfLE_ι h)
    have hh :
        (pull P (inclusion f h)).mapIso (rho P f aY d V D.geometry) ≪≫
            eF P f aY d D.geometry D'.geometry h sq =
          (ProEtale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
            (inclusion f h) (f ⁻¹ᵁ V.1).ι).symm.app (omega P f aY) ≪≫
            exchange P d f (f ∣_ V'.1) aY (V'.1.ι ≫ aY)
              (sq.paste_horiz (isPullback_morphismRestrict f V.1).flip) := by
      change (pull P (inclusion f h)).mapIso
          (exchange P d f (f ∣_ V.1) aY (V.1.ι ≫ aY)
            (isPullback_morphismRestrict f V.1).flip) ≪≫
          exchange P d (f ∣_ V.1) (f ∣_ V'.1) (V.1.ι ≫ aY)
            (V'.1.ι ≫ aY) sq = _
      rw [he]
      apply Iso.ext
      simp only [Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Iso.inv_hom_id_app_assoc]
    rw [hh, heq]
    dsimp only [sourceComposition, rho, affineDiagonalRho, exchange, omega]
    simp only [Iso.trans_assoc]
  · let B := (f ⁻¹ᵁ V.1).toScheme
    let B' := (f ⁻¹ᵁ V'.1).toScheme
    let aB := (f ∣_ V.1) ≫ V.1.ι ≫ aY
    let aB' := (f ∣_ V'.1) ≫ V'.1.ι ≫ aY
    let g := f ∣_ V.1
    let g' := f ∣_ V'.1
    let p := pullback.fst g g
    let p' := pullback.fst g' g'
    let r := pullback.snd g g
    let r' := pullback.snd g' g'
    let s := pullback.diagonal g
    let s' := pullback.diagonal g'
    let := P.noetherian (V.1.ι ≫ aY)
    let := P.noetherian (V'.1.ι ≫ aY)
    let := P.noetherian aB
    let := P.noetherian aB'
    let := P.noetherian (p ≫ aB)
    let := P.noetherian (p' ≫ aB')
    let := Dnc.compactifiable P g (V.1.ι ≫ aY)
    let := Dnc.compactifiable P g' (V'.1.ι ≫ aY)
    let := Dnc.compactifiable P p aB
    let := Dnc.compactifiable P p' aB'
    let := Dnc.invertibleExponent P (g ≫ V.1.ι ≫ aY)
    let := Dnc.invertibleExponent P (g' ≫ V'.1.ι ≫ aY)
    let := Dnc.invertibleExponent P (p ≫ aB)
    let := (P.comparedDiagonalBaseChange d g aB (V.1.ι ≫ aY) rfl).2.2.2.1
    let := (P.comparedDiagonalBaseChange d g' aB' (V'.1.ι ≫ aY) rfl).2.2.2.1
    let := Etale.isIso_rightDerivedUpperShriekBaseChangeMap_of_smoothOfRelativeDimension_general
      P.Coefficient g d sq
    let := (Etale.isIso_dualizingComplexBaseChangeMap_iff P.Coefficient sq).2
      (inferInstanceAs (IsIso ((Etale.rightDerivedUpperShriekBaseChangeMap
        P.Coefficient sq).app (𝟙_ _))))
    let := Etale.isIso_rightDerivedUpperShriekBaseChangeMap_of_smoothOfRelativeDimension_general
      P.Coefficient p d G.cartesian
    let := (Etale.isIso_dualizingComplexBaseChangeMap_iff P.Coefficient G.cartesian).2
      (inferInstanceAs (IsIso ((Etale.rightDerivedUpperShriekBaseChangeMap
        P.Coefficient G.cartesian).app (𝟙_ _))))
    have hrect := dualizing_base_rectangle P.Coefficient
      (IsPullback.of_hasPullback g g).flip sq G.cartesian
      (IsPullback.of_hasPullback g' g').flip G.snd_eq sq.w
    have hiso :
        (Etale.ordinaryFinitePullback P.Coefficient G.product).mapIso
            (asIso (Etale.dualizingComplexBaseChangeMap P.Coefficient
              (IsPullback.of_hasPullback g g).flip)) ≪≫
            asIso (Etale.dualizingComplexBaseChangeMap P.Coefficient G.cartesian) =
          ((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
            G.product r).symm.app _ ≪≫
            (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
              r' (inclusion f h) (G.product ≫ r) G.snd_eq).app _) ≪≫
            (Etale.ordinaryFinitePullback P.Coefficient r').mapIso
              (asIso (Etale.dualizingComplexBaseChangeMap P.Coefficient sq)) ≪≫
              asIso (Etale.dualizingComplexBaseChangeMap P.Coefficient
                (IsPullback.of_hasPullback g' g').flip) := by
      apply Iso.ext
      simpa only [Iso.trans_hom, Functor.mapIso_hom, asIso_hom, Iso.symm_hom,
        Iso.app_inv, Iso.app_hom, Category.assoc] using hrect
    have het := section_inverse_exchange_naturality P.Coefficient
      (inclusion f h) r r' G.product s s' G.snd_eq G.diagonal_eq
      (pullback.diagonal_snd g) (pullback.diagonal_snd g') _ _ _ _
      (asIso (Etale.dualizingComplexBaseChangeMap P.Coefficient
        (IsPullback.of_hasPullback g g).flip))
      (asIso (Etale.dualizingComplexBaseChangeMap P.Coefficient
        (IsPullback.of_hasPullback g' g').flip))
      (asIso (Etale.dualizingComplexBaseChangeMap P.Coefficient sq))
      (asIso (Etale.dualizingComplexBaseChangeMap P.Coefficient G.cartesian)) hiso
    have het' : (Etale.ordinaryFinitePullback P.Coefficient (inclusion f h)).mapIso
        (P.diagonalComparedRestriction g
          (asIso (Etale.dualizingComplexBaseChangeMap P.Coefficient
            (IsPullback.of_hasPullback g g).flip))) ≪≫
        asIso (Etale.dualizingComplexBaseChangeMap P.Coefficient sq) =
      Dnc.sectionBaseChange P.Coefficient d p G.cartesian s s' G.diagonal_eq ≪≫
        P.diagonalComparedRestriction g'
          (asIso (Etale.dualizingComplexBaseChangeMap P.Coefficient
            (IsPullback.of_hasPullback g' g').flip)) := by
      apply Iso.ext
      simpa only [diagonalComparedRestriction, Dnc.sectionBaseChange,
        Etale.sectionCoherencePullbackIso, Iso.trans_hom, Functor.mapIso_hom,
        Iso.symm_hom, Iso.app_hom, Iso.app_inv, Category.assoc,
        Etale.ordinaryFinitePullback, Etale.sectionInvariant, g, g', p, p', r, r', s, s']
        using congrArg Iso.hom het
    dsimp only [Etale.ordinaryFinitePullback] at het'
    have hnat := Dnc.pullComparison_naturality P (inclusion f h)
      (P.diagonalComparedRestriction g
        (asIso (Etale.dualizingComplexBaseChangeMap P.Coefficient
          (IsPullback.of_hasPullback g g).flip)))
    dsimp only [alpha, affineDiagonalAlpha, eF, eC, sourceComparison, exchange,
      sectionExchange]
    simp only [Functor.mapIso_trans, Iso.trans_assoc, Iso.symm_self_id_assoc]
    rw [reassoc_of% hnat]
    rw [← Functor.mapIso_trans, het', Functor.mapIso_trans]
  · let pair : SectionRestriction.Pair (f ⁻¹ᵁ V.1).toScheme d :=
      ⟨_, pullback.fst (f ∣_ V.1) (f ∣_ V.1), pullback.diagonal (f ∣_ V.1),
        inferInstance, inferInstance, inferInstance, inferInstance, pullback.diagonal_fst _⟩
    let pair' : SectionRestriction.Pair (f ⁻¹ᵁ V'.1).toScheme d :=
      ⟨_, pullback.fst (f ∣_ V'.1) (f ∣_ V'.1), pullback.diagonal (f ∣_ V'.1),
        inferInstance, inferInstance, inferInstance, inferInstance, pullback.diagonal_fst _⟩
    let bc : SectionRestriction.BaseChange (inclusion f h) pair' pair :=
      ⟨G.product, G.cartesian, G.diagonal_eq⟩
    let aB := (f ∣_ V.1) ≫ V.1.ι ≫ aY
    let aB' := (f ∣_ V'.1) ≫ V'.1.ι ≫ aY
    have hb : inclusion f h ≫ aB = aB' := by
      dsimp only [aB, aB', inclusion]
      rw [← Category.assoc, ← morphismRestrict_homOfLE f V'.1 V.1 h]
      simp only [Category.assoc, Y.homOfLE_ι_assoc]
    have hn := ((SectionRestriction.coherence P).2.2.2.1
      _ _ aB aB' (inclusion f h) hb d pair pair' bc).2.2
    have hzero := Scheme.Hom.isPullback_normalConeToDeformationSpace pair.g pair.s
    have he : G.normal = SectionRestriction.normalBaseMap P aB aB' bc := by
      apply hzero.hom_ext
      · exact G.normal_eq.trans (hzero.lift_fst _ _ _).symm
      · exact G.normal_cartesian.w.trans (hzero.lift_snd _ _ _).symm
    let nbc : SectionRestriction.BaseChange (inclusion f h)
        (SectionRestriction.normalPair P aB' pair')
        (SectionRestriction.normalPair P aB pair) :=
      ⟨G.normal, G.normal_cartesian, G.zero_eq⟩
    have hnbc : SectionRestriction.normalBaseChange P aB aB' bc = nbc := by
      exact baseChange_ext _ _ he.symm
    rw [hnbc] at hn
    have hd : delta P f aY d V D.geometry = SectionRestriction.delta P aB pair := by
      apply (Dnc.existsUnique_dncInvariance P d pair.g aB pair.s pair.section_eq).unique
      · exact (Dnc.existsUnique_dncInvariance P d pair.g aB pair.s
          pair.section_eq).exists.choose_spec
      · exact (Classical.choose_spec (Dnc.existsUnique_dncInvariance P d pair.g aB
          pair.s pair.section_eq)).1
    have hd' : delta P f aY d V' D'.geometry = SectionRestriction.delta P aB' pair' := by
      apply (Dnc.existsUnique_dncInvariance P d pair'.g aB' pair'.s pair'.section_eq).unique
      · exact (Dnc.existsUnique_dncInvariance P d pair'.g aB' pair'.s
          pair'.section_eq).exists.choose_spec
      · exact (Classical.choose_spec (Dnc.existsUnique_dncInvariance P d pair'.g aB'
          pair'.s pair'.section_eq)).1
    rw [hd, hd']
    dsimp only [eN, eC, sectionExchange, sourceComparison, normalComparison,
      SectionRestriction.baseComparison, SectionRestriction.sectionEtale,
      SectionRestriction.normalPair, Dnc.sourceComparison, Dnc.normalComparison,
      Dnc.sourceEtale, pair, pair', nbc, bc] at hn ⊢
    simpa only [Iso.trans_assoc] using hn
  · let B := (f ⁻¹ᵁ V.1).toScheme
    let B' := (f ⁻¹ᵁ V'.1).toScheme
    let aB := (f ∣_ V.1) ≫ V.1.ι ≫ aY
    let aB' := (f ∣_ V'.1) ≫ V'.1.ι ≫ aY
    let g := pullback.fst (f ∣_ V.1) (f ∣_ V.1)
    let g' := pullback.fst (f ∣_ V'.1) (f ∣_ V'.1)
    let s := pullback.diagonal (f ∣_ V.1)
    let s' := pullback.diagonal (f ∣_ V'.1)
    let q := Scheme.Hom.normalConeProj g s
    let q' := Scheme.Hom.normalConeProj g' s'
    let := P.noetherian aB
    let := P.noetherian aB'
    let := Dnc.normalCompactifiable P d g aB s (pullback.diagonal_fst _)
    let := Dnc.normalCompactifiable P d g' aB' s' (pullback.diagonal_fst _)
    let : SmoothOfRelativeDimension d q :=
      (Scheme.Hom.normalConeData d (pullback.diagonal_fst _)).smoothOfRelativeDimension_proj
    let : SmoothOfRelativeDimension d q' :=
      (Scheme.Hom.normalConeData d (pullback.diagonal_fst _)).smoothOfRelativeDimension_proj
    let := SmoothOfRelativeDimension.smooth d q
    let : LocallyOfFiniteType q := inferInstance
    let := SmoothOfRelativeDimension.smooth d q'
    let : LocallyOfFiniteType q' := inferInstance
    let := Dnc.normalQuasiCompact d g s (pullback.diagonal_fst _)
    let := Dnc.normalQuasiCompact d g' s' (pullback.diagonal_fst _)
    let := Dnc.invertibleExponent P (q ≫ aB)
    let := Dnc.invertibleExponent P (q' ≫ aB')
    let := P.noetherian (q ≫ aB)
    let := P.noetherian (q' ≫ aB')
    obtain ⟨F, hF, e, he, hz⟩ := D.vectorModel
    obtain ⟨F', hF', e', he', hz'⟩ := D'.vectorModel
    let := hF
    let := hF'
    have hn := D.normalized F e he hz
    have hn' := D'.normalized F' e' he' hz'
    have hb := model_beta_compat P (B := B) (B' := B')
      (Q := s.ker.normalCone) (Q' := s'.ker.normalCone) aB aB' d q q'
      s.normalConeZeroSection s'.normalConeZeroSection (inclusion f h) G.normal
      G.normal_cartesian G.zero_eq F F' e e' he he' hz hz' D.betaEtale D'.betaEtale
      hn hn'
    have hnat := Dnc.pullComparison_naturality P (inclusion f h) D.betaEtale
    dsimp only [Etale.ordinaryFinitePullback] at hb
    dsimp only [beta, eN, normalComparison, sectionExchange, tate]
    simp only [Functor.mapIso_trans, Iso.trans_assoc, Iso.symm_self_id_assoc]
    rw [reassoc_of% hnat]
    apply Iso.ext
    simp only [Iso.trans_hom, Functor.mapIso_hom]
    have hbh := congrArg Iso.hom hb
    simp only [Iso.trans_hom, Functor.mapIso_hom] at hbh
    have hh := congrArg
      ((ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) B').mapDerivedCategory.map) hbh
    simp only [Functor.map_comp] at hh
    exact congrArg (fun x ↦ _ ≫ _ ≫ x) hh

end WeilConjectures.PurityFiniteSetting.OrientationRefinement
