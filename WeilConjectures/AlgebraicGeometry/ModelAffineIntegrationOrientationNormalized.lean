/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompositionModelOrientationDefinitions
import all WeilConjectures.AlgebraicGeometry.DiagonalDncChartNormalization

/-! # The canonical normalized affine family

The finite-coordinate family is the inverse diagonal orientation. Its ordered
normalization is proved through the prescribed reversed-coordinate isomorphism.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 8192
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

attribute [local implicit_reducible] diagonalTwist diagonalOrdinaryDualizing
  iteratedAffineLine iteratedAffineLineProj Etale.affineLinearBaseCoefficient

private theorem tower_ext {X B : Scheme.{u}} :
    ∀ (r : ℕ) (f g : X ⟶ iteratedAffineLine B r),
      f ≫ iteratedAffineLineProj B r = g ≫ iteratedAffineLineProj B r →
      (∀ i, f.appTop (iteratedAffineLine.coord B r i) =
        g.appTop (iteratedAffineLine.coord B r i)) → f = g := by
  intro r
  induction r with
  | zero => intro f g h _; simpa using h
  | succ r ih =>
    intro f g hp hc
    apply AffineSpace.hom_ext
    · apply ih
      · simpa only [iteratedAffineLineProj_succ, Category.assoc] using hp
      · intro i
        simpa only [iteratedAffineLine.coord_succ_succ,
          Scheme.Hom.comp_appTop, CommRingCat.comp_apply] using! hc i.succ
    · intro i
      cases i
      exact hc 0

private def orderedCoordinatesIso (B : Scheme.{u}) (r : ℕ) :
    DiagonalPasting.A r B ≅ iteratedAffineLine B r where
  hom := modelOrderedCoordinates B r
  inv := AffineSpace.homOfVector (iteratedAffineLineProj B r)
    (fun i ↦ iteratedAffineLine.coord B r i.down.rev)
  hom_inv_id := by
    apply AffineSpace.hom_ext
    · simp only [Category.assoc, AffineSpace.homOfVector_over,
        modelOrderedCoordinates, Scheme.Hom.toIteratedAffineLine_proj, Category.id_comp]
    · intro i
      simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
        AffineSpace.homOfVector_appTop_coord, modelOrderedCoordinates,
        Scheme.Hom.toIteratedAffineLine_appTop_coord, Fin.rev_rev,
        Scheme.Hom.id_appTop, CommRingCat.id_apply, ULift.up_down]
  inv_hom_id := by
    apply tower_ext r
    · simp only [Category.assoc, modelOrderedCoordinates,
        Scheme.Hom.toIteratedAffineLine_proj, AffineSpace.homOfVector_over,
        Category.id_comp]
    · intro i
      simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, modelOrderedCoordinates,
        Scheme.Hom.toIteratedAffineLine_appTop_coord, AffineSpace.homOfVector_appTop_coord,
        Fin.rev_rev, Scheme.Hom.id_appTop, CommRingCat.id_apply]

end WeilConjectures.PurityFiniteSetting


namespace WeilConjectures.PurityFiniteSetting

private theorem ordered_eq_inv (P : PurityFiniteSetting.{u})
    (B : Scheme.{u}) [IsAffine B] (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] (r : ℕ) :
    letI := projection_smooth B r
    P.modelOrderedGamma B aB r =
      (P.diagonalDualizingObject r (iteratedAffineLineProj B r) aB).inv := by
  rcases P with ⟨F, C, E, n, hn⟩
  cases n with
  | zero => exact False.elim (Nat.not_succ_le_zero 0 hn)
  | succ n => exact eq_of_heq (chartGamma_eq_inverseOrientation F C E n B aB r)

private theorem ordered_zero_formula (P : PurityFiniteSetting.{u})
    (B : Scheme.{u}) [IsAffine B] (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] :
    letI := projection_smooth B 0
    let C := (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) B).mapDerivedCategory
    let I := ((Etale.rightDerivedUpperShriekIsoOfIso P.Coefficient (Iso.refl B)) ≪≫
      Etale.leftDerivedUpperStarId (ModuleCat.{u + 1} P.Coefficient) B).app
        (Etale.ordinaryFiniteUnit P.Coefficient B)
    let J := P.diagonalDualizingComparison (𝟙 B)
    P.modelOrderedGamma B aB 0 = C.map I.inv ≫ J.inv := by
  let := P.noetherian aB
  let := projection_smooth B 0
  let t := Etale.projectiveLineTraceTransport P.diagonalExponent
    (pow_pos P.coefficients.prime.out.pos P.level) P.Coefficient
    P.diagonalExponent_annihilates
  let D := Etale.projectiveLineTraceDatum P.diagonalExponent
    (pow_pos P.coefficients.prime.out.pos P.level) P.Coefficient
    P.diagonalExponent_annihilates
  let I := ((Etale.rightDerivedUpperShriekIsoOfIso P.Coefficient (Iso.refl B)) ≪≫
    Etale.leftDerivedUpperStarId (ModuleCat.{u + 1} P.Coefficient) B).app
      (Etale.ordinaryFiniteUnit P.Coefficient B)
  let C := (ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} P.Coefficient) B).mapDerivedCategory
  let J := P.diagonalDualizingComparison (𝟙 B)
  have hm := P.chartProjectionOrientation_inv B aB 0 t D
  have hz := congrArg Iso.hom (P.chartAffineGamma_zero B aB t D)
  have he : (P.chartOrdinaryOrientation 0 (𝟙 B) aB).inv = I.inv := hm.trans hz
  calc
    _ = (P.diagonalDualizingObject 0 (𝟙 B) aB).inv := ordered_eq_inv P B aB 0
    _ = _ := by
      rw [(P.chartOrdinaryOrientation_spec 0 (𝟙 B) aB).2]
      simp only [Iso.trans_inv, Functor.mapIso_inv]
      rw [he]

private theorem ordered_zero (P : PurityFiniteSetting.{u}) :
    P.ModelGammaZeroNormalization := by
  intro B _ aB _ _
  let := P.noetherian aB
  let := projection_smooth B 0
  let I := ((Etale.rightDerivedUpperShriekIsoOfIso P.Coefficient (Iso.refl B)) ≪≫
    Etale.leftDerivedUpperStarId (ModuleCat.{u + 1} P.Coefficient) B).app
      (Etale.ordinaryFiniteUnit P.Coefficient B)
  let C := (ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} P.Coefficient) B).mapDerivedCategory
  let J := P.diagonalDualizingComparison (𝟙 B)
  have hG := ordered_zero_formula P B aB
  dsimp only at hG
  have h : P.modelOrderedGamma B aB 0 ≫
        (P.diagonalDualizingComparison (𝟙 B)).hom ≫
          (ProEtale.comparisonUpperStar
            (ModuleCat.{u + 1} P.Coefficient) B).mapDerivedCategory.map
            (((Etale.rightDerivedUpperShriekIsoOfIso P.Coefficient (Iso.refl B)).app
                (Etale.ordinaryFiniteUnit P.Coefficient B)).hom ≫
              ((Etale.leftDerivedUpperStarId (ModuleCat.{u + 1} P.Coefficient) B).app
                (Etale.ordinaryFiniteUnit P.Coefficient B)).hom) =
      𝟙 ((ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) B).mapDerivedCategory.obj
        (Etale.affineLinearBaseCoefficient P.Coefficient P.diagonalExponent
          P.diagonalExponent_annihilates B 0)) := by
    rw [hG]
    simp only [Iso.app_inv, Iso.trans_inv, NatTrans.comp_app,
      Category.assoc, Iso.inv_hom_id_assoc, ← Functor.map_comp]
    simp only [← Iso.app_inv, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id]
    have ho := congrArg (fun K =>
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) B).mapDerivedCategory.obj K)
      (compositionEtalePowerZero P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates B).symm
    cases ho
    rfl
  simpa only [iteratedAffineLine_zero, iteratedAffineLineProj_zero,
    diagonalTwist, diagonalTwistEtale, compositionEtalePowerZero, Functor.id_obj,
    Iso.app_hom, Iso.trans_hom, NatTrans.comp_app] using! h


end WeilConjectures.PurityFiniteSetting


namespace WeilConjectures.PurityFiniteSetting

private theorem pullComparison_naturality (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {K L : Etale.DerivedCategoryModule P.Coefficient Y} (a : K ⟶ L) :
    (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).leftDerivedFunctor.map
        ((ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory.map a) ≫
      (Dnc.pullComparison P f L).hom =
    (Dnc.pullComparison P f K).hom ≫
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.map
        ((Etale.ordinaryFinitePullback P.Coefficient f).map a) := by
  let e :=
    Functor.isoWhiskerLeft
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory
      (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} P.Coefficient) f) ≪≫
    ProEtale.mapDerivedCategoryComparisonUpperStarCompUpperStarIso
      (ModuleCat.{u + 1} P.Coefficient) f ≪≫
    Functor.isoWhiskerRight
      (Etale.leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} P.Coefficient) f).symm
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory
  exact e.hom.naturality a

private theorem ordinary_inverse_restriction (P : PurityFiniteSetting.{u})
    {U X Y : Scheme.{u}} (r : ℕ) (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [SmoothOfRelativeDimension r f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (j : U ⟶ X) [Etale j] [IsSeparated j] [LocallyOfFiniteType j] [QuasiCompact j]
    [SmoothOfRelativeDimension r (j ≫ f)]
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient)
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates) :
    letI := P.noetherian aY
    letI := P.noetherian (f ≫ aY)
    letI := P.noetherian ((j ≫ f) ≫ aY)
    letI := Dnc.compactifiable P f aY
    letI := Dnc.compactifiable P (j ≫ f) aY
    (Etale.ordinaryFinitePullback P.Coefficient j).map
        (P.chartOrdinaryOrientation r f aY).inv ≫
      (P.diagonalEtaleLocality N j f).hom =
      (Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates t j (P.diagonalExponent_isUnit (f ≫ aY)) r).hom ≫
        (P.chartOrdinaryOrientation r (j ≫ f) aY).inv := by
  let := P.noetherian aY
  let := P.noetherian (f ≫ aY)
  let := P.noetherian ((j ≫ f) ≫ aY)
  let := Dnc.compactifiable P f aY
  let := Dnc.compactifiable P (j ≫ f) aY
  have h := P.chartOrientation_etale_restriction r f aY j N t
  apply (cancel_mono (P.chartOrdinaryOrientation r (j ≫ f) aY).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← h, ← Functor.map_comp_assoc, Iso.inv_hom_id]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]

end WeilConjectures.PurityFiniteSetting

namespace WeilConjectures.PurityFiniteSetting

private theorem inverse_restriction_congr (P : PurityFiniteSetting.{u})
    {U X Y : Scheme.{u}} (r : ℕ) (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [SmoothOfRelativeDimension r f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (j : U ⟶ X) [Etale j] [IsSeparated j] [LocallyOfFiniteType j] [QuasiCompact j]
    (g : U ⟶ Y) [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [SmoothOfRelativeDimension r g] (w : j ≫ f = g)
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient)
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates) :
    letI := P.noetherian aY
    letI := P.noetherian (f ≫ aY)
    letI := P.noetherian (g ≫ aY)
    letI := Dnc.compactifiable P f aY
    letI := Dnc.compactifiable P g aY
    letI : HasCompactification (j ≫ f) := HasCompactification.of_eq w.symm
    (Etale.ordinaryFinitePullback P.Coefficient j).map
        (P.chartOrdinaryOrientation r f aY).inv ≫
      (P.diagonalEtaleLocality N j f ≪≫ P.diagonalDualizingCongr w).hom =
      (Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates t j (P.diagonalExponent_isUnit (f ≫ aY)) r).hom ≫
        (P.chartOrdinaryOrientation r g aY).inv := by
  subst g
  simp only [diagonalDualizingCongr, eqToIso_refl, Iso.refl_hom,
    Iso.trans_hom, Category.comp_id]
  exact ordinary_inverse_restriction P r f aY j N t

end WeilConjectures.PurityFiniteSetting


namespace WeilConjectures.PurityFiniteSetting

private theorem inverse_orientation_spec (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (r : ℕ) (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [SmoothOfRelativeDimension r f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY] :
    letI := P.noetherian aY
    letI := P.noetherian (f ≫ aY)
    letI := Dnc.compactifiable P f aY
    (P.diagonalDualizingObject r f aY).inv =
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.map
          (P.chartOrdinaryOrientation r f aY).inv ≫
        (P.diagonalDualizingComparison f).inv := by
  let := P.noetherian aY
  let := P.noetherian (f ≫ aY)
  let := Dnc.compactifiable P f aY
  rw [(P.chartOrdinaryOrientation_spec r f aY).2]
  rfl

end WeilConjectures.PurityFiniteSetting

namespace WeilConjectures.PurityFiniteSetting
private theorem normalization_square (P : PurityFiniteSetting.{u})
    (B : Scheme.{u}) [IsAffine B] (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] (r : ℕ)
    (c : DiagonalPasting.A r B ≅ iteratedAffineLine B r)
    (hc : c.hom ≫ iteratedAffineLineProj B r = DiagonalPasting.pr r B)
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient) :
    letI := DiagonalPasting.affineDimension r B
    letI := Dnc.compactifiable P (DiagonalPasting.pr r B) aB
    (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) c.hom).leftDerivedFunctor.map
        (P.modelOrderedGamma B aB r) ≫ (P.modelCoordinateDualizing B aB r c hc N).hom =
      (P.modelOrientationTwistPullback c.hom (iteratedAffineLineProj B r ≫ aB) r).hom ≫
        (P.diagonalDualizingObject r (DiagonalPasting.pr r B) aB).inv := by
  let := P.noetherian aB
  let := ProEtale.AffineSpacePurity.tower_noetherian P B aB r
  let := (ProEtale.AffineSpacePurity.projection_geometry B r).1
  let := (ProEtale.AffineSpacePurity.projection_geometry B r).2
  let := projection_smooth B r
  let := DiagonalPasting.affineDimension r B
  let := Dnc.compactifiable P (DiagonalPasting.pr r B) aB
  let : HasCompactification (c.hom ≫ iteratedAffineLineProj B r) :=
    HasCompactification.of_eq hc.symm
  let t := Etale.projectiveLineTraceTransport P.diagonalExponent
    (pow_pos P.coefficients.prime.out.pos P.level) P.Coefficient
    P.diagonalExponent_annihilates
  have h := inverse_restriction_congr P r (iteratedAffineLineProj B r) aB c.hom
    (DiagonalPasting.pr r B) hc N t
  rw [ordered_eq_inv]
  rw [inverse_orientation_spec P r (iteratedAffineLineProj B r) aB,
    inverse_orientation_spec P r (DiagonalPasting.pr r B) aB]
  unfold modelCoordinateDualizing modelOrientationTwistPullback
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Functor.map_comp,
    Category.assoc]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id, Category.comp_id]
  erw [reassoc_of% (pullComparison_naturality P c.hom
    (P.chartOrdinaryOrientation r (iteratedAffineLineProj B r) aB).inv)]
  rw [← Functor.map_comp_assoc]
  simp only [Iso.trans_hom, diagonalDualizingCongr] at h
  erw [h]

/-- The inverse diagonal orientation on each fixed finite-coordinate affine projection.
Source: composition proof, affine model normalization.
(blueprint: lem-pur-model-affine-integration-orientation-normalized). -/
def modelAffineCanonicalGamma (P : PurityFiniteSetting.{u}) : P.ModelAffineGamma :=
  fun B _ aB _ _ r ↦ by
    letI := DiagonalPasting.affineDimension r B
    exact (P.diagonalDualizingObject r (DiagonalPasting.pr r B) aB).symm

/-- The canonical family has exactly the ordered normalization and the rank-zero unit.
Source: latest blueprint, composition proof Step 1.
(blueprint: lem-pur-model-affine-integration-orientation-normalized).

Proof: invert the diagonal orientation on the finite-coordinate affine projection.
Construct the ordered coordinate isomorphism by reversing the iterated-line coordinates;
check its inverse laws on the projection and coordinate functions. The chart restriction
identity transports the inverse ordered orientation along this isomorphism, and naturality
of the site comparison gives the required normalization square. At rank zero, replace the
ordered comparison by its affine counit mate, use the exceptional-identity normalization,
and cancel the identity constraints. These calculations include the empty base. -/
theorem model_affine_integration_orientation_normalized (P : PurityFiniteSetting.{u}) :
    P.ModelGammaNormalization P.modelAffineCanonicalGamma ∧
      P.ModelGammaZeroNormalization := by
  refine ⟨?_, ordered_zero P⟩
  intro B _ aB _ _ r
  let c := orderedCoordinatesIso B r
  have hc : c.hom ≫ iteratedAffineLineProj B r = DiagonalPasting.pr r B :=
    Scheme.Hom.toIteratedAffineLine_proj _ _
  refine ⟨c, hc, rfl, ?_⟩
  intro N
  exact normalization_square P B aB r c hc N

end WeilConjectures.PurityFiniteSetting
