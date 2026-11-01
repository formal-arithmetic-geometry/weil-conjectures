/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.SectionRestriction.PuritySectionRestrictionData
import WeilConjectures.SmoothPurity.PurityFiniteSetting.SectionRestriction.PuritySectionRestrictionEtaleFunctorial
import WeilConjectures.SmoothPurity.PurityFiniteSetting.SectionRestriction.PuritySectionReesMapComposition
import WeilConjectures.SmoothPurity.PurityFiniteSetting.SectionRestriction.PuritySectionBaseComparisonLaws
import WeilConjectures.SmoothPurity.PurityFiniteSetting.SectionRestriction.PuritySectionFibreSquares
import WeilConjectures.SmoothPurity.PurityFiniteSetting.SectionRestriction.PuritySectionNormalizedSpecialization

/-! # Counit-normalized restriction coherence

Source: blueprint latest, orientation charts Step 3 and composition coherence Step 1
(blueprint: lem-pur-section-etale-restriction-coherence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting.SectionRestriction

private theorem deformation_id {B : Scheme.{u}} {d : ℕ} (X : Pair B d) :
    deformationMap (EtaleMap.id X) = 𝟙 _ := by
  open Scheme.AffineZariskiSite in
    apply colimit.hom_ext
    intro U
    dsimp only [deformationMap, SectionReesBaseChange.pairMap, EtaleMap.id,
      Scheme.IdealSheafData.deformationSpaceMap]
    rw [PullbackData.ι_comparison _ _ _ (le_refl U.1)]
    have he : (𝟙 X.V : X.V ⟶ X.V).appLE U.1 U.1 (le_refl U.1) = 𝟙 _ := by
      simp only [Scheme.Hom.appLE, Scheme.Hom.id_app, Category.id_comp]
      exact X.V.presheaf.map_id _
    simp only [Scheme.IdealSheafData.extendedReesPullbackData_map, he,
      CommRingCat.hom_id, Ideal.extendedReesAlgebraMap_id, CommRingCat.ofHom_id]
    dsimp only [familyPair]
    rw [show Spec.map (𝟙 (CommRingCat.of
      (X.s.ker.siteIdeal U).extendedReesAlgebra)) = 𝟙 _ from
        Scheme.Spec.map_id (.op _)]
    exact (Category.id_comp (colimit.ι
      (relativeGluingData X.s.ker.coequifibered_toReesPresheaf).functor U)).trans
        (Category.comp_id _).symm

private theorem restriction_functorial (P : PurityFiniteSetting.{u})
    (B : Scheme.{u}) (aB : B ⟶ Spec (.of P.field.k))
    [IsSeparated aB] [LocallyOfFiniteType aB] [QuasiCompact aB] (d : ℕ) :
    (∀ X : Pair B d, restriction P aB (EtaleMap.id X) = Iso.refl _) ∧
    (∀ (X'' X' X : Pair B d) (b : EtaleMap X'' X') (a : EtaleMap X' X),
      restriction P aB (b.comp a) = restriction P aB b ≪≫ restriction P aB a) := by
  obtain ⟨hi, hc⟩ := restrictionEtale_functorial P B aB d
  constructor
  · intro X
    apply Iso.ext
    simp only [restriction, hi X, Iso.trans_hom, Iso.symm_hom,
      Functor.mapIso_hom, Iso.refl_hom]
    dsimp only [invariant, sectionEtale]
    rw [(ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) B).mapDerivedCategory.map_id]
    simp only [Category.id_comp, Iso.hom_inv_id]
  · intro X'' X' X b a
    simp only [restriction, hc X'' X' X b a, Functor.mapIso_trans]
    apply Iso.ext
    simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc,
      Iso.inv_hom_id_assoc]

private theorem deformation_comp {B : Scheme.{u}} {d : ℕ} {X'' X' X : Pair B d}
    (b : EtaleMap X'' X') (a : EtaleMap X' X) :
    deformationMap (b.comp a) = deformationMap b ≫ deformationMap a := by
  simpa only [deformationMap, EtaleMap.comp, Category.id_comp] using
    rees_pairMap_comp X.s X'.s X''.s a.map b.map (𝟙 B) (𝟙 B)
      (a.section_eq.trans (Category.id_comp X.s).symm)
      (b.section_eq.trans (Category.id_comp X'.s).symm)

private theorem normal_mono {B : Scheme.{u}} {d : ℕ} (X : Pair B d) :
    Mono X.s.ker.normalConeToDeformationSpace := by
  have : IsClosedImmersion X.s.ker.normalConeToDeformationSpace :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion)
      (Scheme.Hom.isPullback_normalConeToDeformationSpace X.g X.s).flip inferInstance
  infer_instance

private theorem normal_zero (P : PurityFiniteSetting.{u})
    {B : Scheme.{u}} {d : ℕ}
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB]
    {X' X : Pair B d} (a : EtaleMap X' X) :
    X'.s.ker.normalConeToDeformationSpace ≫ deformationMap a =
      normalMap P aB a ≫ X.s.ker.normalConeToDeformationSpace :=
  (geometry P aB a).2.2.2.2.2.2.2.2.2.2.2

private theorem normal_id (P : PurityFiniteSetting.{u}) {B : Scheme.{u}} {d : ℕ}
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB]
    (X : Pair B d) : normalMap P aB (EtaleMap.id X) = 𝟙 _ := by
  have := normal_mono X
  apply (cancel_mono X.s.ker.normalConeToDeformationSpace).mp
  rw [← normal_zero P aB (EtaleMap.id X), deformation_id]
  dsimp only [familyPair, normalPair]
  rw [Category.comp_id, Category.id_comp]

private theorem normal_comp (P : PurityFiniteSetting.{u}) {B : Scheme.{u}} {d : ℕ}
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB]
    {X'' X' X : Pair B d} (b : EtaleMap X'' X') (a : EtaleMap X' X) :
    normalMap P aB (b.comp a) = normalMap P aB b ≫ normalMap P aB a := by
  have := normal_mono X
  apply (cancel_mono X.s.ker.normalConeToDeformationSpace).mp
  rw [← normal_zero P aB (b.comp a), deformation_comp,
    ← Category.assoc, normal_zero P aB b, Category.assoc,
    normal_zero P aB a, Category.assoc]

private theorem etaleMap_ext {B : Scheme.{u}} {d : ℕ} {X' X : Pair B d}
    {a b : EtaleMap X' X} (h : a.map = b.map) : a = b := by
  cases a
  cases b
  cases h
  rfl

private theorem composition_all (P : PurityFiniteSetting.{u}) : Composition P := by
  intro B aB _ _ _ d
  have hr := restriction_functorial P B aB d
  refine ⟨hr.1, hr.2, ?_, fun X ↦ ⟨deformation_id X, normal_id P aB X⟩⟩
  intro X'' X' X b a
  refine ⟨deformation_comp b a, normal_comp P aB b a, ?_, ?_⟩
  · unfold familyRestriction
    have hm : familyMap P aB (b.comp a) =
        (familyMap P aB b).comp (familyMap P aB a) :=
      etaleMap_ext (deformation_comp b a)
    rw [hm]
    exact (restriction_functorial P (AffineSpace (ULift.{u} (Fin 1)) B)
      ((AffineSpace (ULift.{u} (Fin 1)) B ↘ B) ≫ aB) d).2 _ _ _ _ _
  · have hm : normalEtaleMap P aB (b.comp a) =
        (normalEtaleMap P aB b).comp (normalEtaleMap P aB a) :=
      etaleMap_ext (normal_comp P aB b a)
    rw [hm]
    exact hr.2 _ _ _ _ _

private theorem rees_naturality {B B₀ : Scheme.{u}} {d : ℕ} {b : B₀ ⟶ B}
    {X' X : Pair B d} {X₀' X₀ : Pair B₀ d}
    (a : EtaleMap X' X) (a₀ : EtaleMap X₀' X₀)
    (sq : BaseChange b X₀ X) (sq' : BaseChange b X₀' X')
    (ha : a₀.map ≫ sq.map = sq'.map ≫ a.map) :
    deformationMap a₀ ≫ reesBaseMap sq = reesBaseMap sq' ≫ deformationMap a := by
  have h₁ := rees_pairMap_comp X.s X₀.s X₀'.s sq.map a₀.map b (𝟙 B₀)
    sq.section_eq (a₀.section_eq.trans (Category.id_comp X₀.s).symm)
  have h₂ := rees_pairMap_comp X.s X'.s X₀'.s a.map sq'.map (𝟙 B) b
    (a.section_eq.trans (Category.id_comp X.s).symm) sq'.section_eq
  dsimp only [deformationMap, reesBaseMap]
  rw [← h₁, ← h₂]
  simp only [Category.id_comp, Category.comp_id, ha]

private theorem normal_naturality (P : PurityFiniteSetting.{u})
    {B B₀ : Scheme.{u}} {d : ℕ}
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB]
    (aB₀ : B₀ ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB₀] [QuasiCompact aB₀]
    {b : B₀ ⟶ B} {X' X : Pair B d} {X₀' X₀ : Pair B₀ d}
    (a : EtaleMap X' X) (a₀ : EtaleMap X₀' X₀)
    (sq : BaseChange b X₀ X) (sq' : BaseChange b X₀' X')
    (ha : a₀.map ≫ sq.map = sq'.map ≫ a.map) :
    normalMap P aB₀ a₀ ≫ normalBaseMap P aB aB₀ sq =
      normalBaseMap P aB aB₀ sq' ≫ normalMap P aB a := by
  have := normal_mono X
  have hf : normalBaseMap P aB aB₀ sq ≫ X.s.ker.normalConeToDeformationSpace =
      X₀.s.ker.normalConeToDeformationSpace ≫ reesBaseMap sq :=
    (Scheme.Hom.isPullback_normalConeToDeformationSpace X.g X.s).lift_fst _ _ _
  have hf' : normalBaseMap P aB aB₀ sq' ≫ X'.s.ker.normalConeToDeformationSpace =
      X₀'.s.ker.normalConeToDeformationSpace ≫ reesBaseMap sq' :=
    (Scheme.Hom.isPullback_normalConeToDeformationSpace X'.g X'.s).lift_fst _ _ _
  apply (cancel_mono X.s.ker.normalConeToDeformationSpace).mp
  rw [Category.assoc, hf, ← Category.assoc, ← normal_zero P aB₀ a₀,
    Category.assoc, rees_naturality a a₀ sq sq' ha, ← Category.assoc, ← hf',
    Category.assoc, normal_zero P aB a, Category.assoc]

/-- Counit-normalized restriction of section invariants is coherent under composition,
base change and deformation, with the specified endpoint comparisons.
Source: orientation charts Steps 1--3 and composition coherence Step 1
(blueprint: lem-pur-section-etale-restriction-coherence).
Proof:
1. Set E = rho_a c_{g,a,A}. Etale dimension-zero permanence preserves the pure
   relative dimension. Pull back E by s' and use a s' = s; this is restrictionEtale.
   The canonical nu* comparison gives restriction between the actual pro-etale objects.
2. Compact-support associativity, conjugacy and mate pasting give the associator of c.
   Composition of rho and its naturality imply E_ab = Lb*(E_a) E_b. Pull back by the
   second section and use pullback composition. Identity normalization gives R_1 = 1.
3. Smooth tensor/exceptional pasting gives beta_ga L(u')*sigma_ag =
   sigma_a0g0 (beta_a tensor La0*beta_g). Substitute E sigma = eta tensor 1 and
   eta_a0 beta_a = L(u')*eta_a. Cancel the invertible sigma to obtain the base-change
   square for E, and pull back by the section to obtain BaseCompatibility.
4. Noetherian finite-type geometry and the flat extended-Rees pushout give geometry:
   t maps to t and f/t to a*(f)/t. The zero fibre is exactly the conormal-induced normal
   isomorphism; the one fibre is a. These formulas preserve identity and composition.
5. Apply steps 1--3 to the deformation pairs. Restrict at one and zero through the
   specified smooth adjunction-mate fibre maps. This gives the two endpoint equations.
6. Let kappa and kappa' be the unique family trivializations normalized at one.
   The composite (Lp*R_a)^(-1) kappa familyRestriction has the same normalization as
   kappa', so uniqueness gives kappa familyRestriction = Lp*R_a kappa'.
7. Read this equality at zero. DNC uniqueness identifies the endpoint readings with
   delta and delta'; it follows that R_n delta' = delta R_a.
8. Repeat these arguments after any further open or base restriction. Pasting of the
   same pullback constraints gives the same equations in either order. The normalized
   family is again unique. The empty base and d = 0 require no cancellation of a
   nonzero dimension; the rank-zero standard family has identity comparisons.
   At no point is a Tate orientation or a coefficient-line frame chosen. -/
theorem coherence (P : PurityFiniteSetting.{u}) :
    Composition P ∧ BaseCompatibility P ∧ Endpoints P ∧ NormalizedBase P ∧
      BasePasting P ∧ RankZero P := by
  have hb := section_base_comparison_laws P
  have hf := section_fibre_squares P
  have hn := section_normalized_specialization P hf.1 hf.2
  refine ⟨composition_all P, ?_, ?_, ?_, hb.1, hn.2.2⟩
  · intro B B₀ aB _ _ _ aB₀ _ _ _ b h_b d X' X X₀' X₀ a a₀ sq sq' ha
    exact ⟨hb.2 B B₀ aB aB₀ b h_b d X' X X₀' X₀ a a₀ sq sq' ha,
      rees_naturality a a₀ sq sq' ha, normal_naturality P aB aB₀ a a₀ sq sq' ha⟩
  · intro B aB _ _ _ d X' X a
    exact ⟨(hf.1 B aB d X' X a).1, (hf.1 B aB d X' X a).2,
      hn.1 B aB d X' X a⟩
  · intro B B₀ aB _ _ _ aB₀ _ _ _ b h_b d X X₀ sq
    exact ⟨(hf.2 B B₀ aB aB₀ b h_b d X X₀ sq).1,
      (hf.2 B B₀ aB aB₀ b h_b d X X₀ sq).2,
      hn.2.1 B B₀ aB aB₀ b h_b d X X₀ sq⟩

end WeilConjectures.PurityFiniteSetting.SectionRestriction
