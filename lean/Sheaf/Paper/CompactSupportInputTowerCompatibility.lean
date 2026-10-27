module

public import Sheaf.Paper.CompactSupportReductionTower
import all Sheaf.Paper.CompactSupportReductionTower
import all Sheaf.SixFunctors.ProEtale.IntegralReductionTransitionComparison
import all Sheaf.Paper.SfIntegralReductionTower
import Sheaf.Paper.CompactSupportCoefficientTransition
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! Compatibility of the compact-support input reduction with the completed tower. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
open AlgebraicGeometry.ProEtale.IntegralPresentation
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private theorem scalarComp_eqToIso
    {T : Scheme.{u}} {R S B : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ B) (χ : R ⟶ B) (h : φ ≫ ψ = χ)
    (hF : pbcRestrict ψ ⋙ pbcRestrict φ = pbcRestrict χ) :
    pbcRestrictComp φ ψ χ h = eqToIso hF := by
  subst χ
  change pbcRestrictComp φ ψ (φ ≫ ψ) rfl = Iso.refl _
  apply (pbcRestrictComp_exists φ ψ (φ ≫ ψ) rfl).unique
  · exact (pbcRestrictComp_exists φ ψ (φ ≫ ψ) rfl).exists.choose_spec
  · intro M U x
    rfl

private theorem eqIso_comp
    {A B C : Type*} [Category A] [Category B] [Category C]
    {F F' : A ⥤ B} (G : B ⥤ C) {H : A ⥤ C}
    (h : F = F') (h' : F' ⋙ G = H) (h'' : F ⋙ G = H) :
    eqToIso h'' = Functor.isoWhiskerRight (eqToIso h) G ≪≫ eqToIso h' := by
  subst F'
  subst H
  apply Iso.ext
  ext X
  simp

private theorem derivedComp_change
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    {F F' : A ⥤ B} (G : B ⥤ C) (H : A ⥤ C)
    [F.Additive] [F'.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (e : F ≅ F') (a : F ⋙ G ≅ H) (b : F' ⋙ G ≅ H)
    (h : a = Functor.isoWhiskerRight e G ≪≫ b) :
    (Functor.mapDerivedCategoryCompIso F G).symm ≪≫
        Functor.mapDerivedCategoryNatIso a =
      Functor.isoWhiskerRight (Functor.mapDerivedCategoryNatIso e) G.mapDerivedCategory ≪≫
        (Functor.mapDerivedCategoryCompIso F' G).symm ≪≫
          Functor.mapDerivedCategoryNatIso b := by
  apply Iso.ext
  rw [h]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapDerivedCategoryNatIso_trans]
  have hc := Functor.mapDerivedCategoryNatIso_isoWhiskerRight e G
  have hc' : (Functor.mapDerivedCategoryNatIso (Functor.isoWhiskerRight e G)).hom =
      (Functor.mapDerivedCategoryCompIso F G).hom ≫
        Functor.whiskerRight (Functor.mapDerivedCategoryNatIso e).hom G.mapDerivedCategory ≫
          (Functor.mapDerivedCategoryCompIso F' G).inv := by
    rw [← reassoc_of% hc]
    simp only [Iso.hom_inv_id, Category.comp_id]
  rw [hc']
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Functor.isoWhiskerRight_hom]

private theorem restrictedMate_change
    {A B C : Type*} [Category A] [Category B] [Category C]
    {L : A ⥤ B} {R : B ⥤ A} {L' : A ⥤ C} {R' : C ⥤ A}
    (adj : L ⊣ R) (adj' : L' ⊣ R') (S S' : C ⥤ B)
    (ρ : S ≅ S') (g : S ⋙ R ≅ R') (g' : S' ⋙ R ≅ R')
    (h : g = Functor.isoWhiskerRight ρ R ≪≫ g') (K : A) :
    R.map ((adj.homEquiv K _).symm
        (adj'.unit.app K ≫ g.inv.app (L'.obj K))) ≫ g.hom.app (L'.obj K) =
      R.map ((adj.homEquiv K _).symm
        (adj'.unit.app K ≫ g'.inv.app (L'.obj K))) ≫ g'.hom.app (L'.obj K) := by
  have hm : (adj.homEquiv K _).symm
        (adj'.unit.app K ≫ g.inv.app (L'.obj K)) ≫ ρ.hom.app (L'.obj K) =
      (adj.homEquiv K _).symm (adj'.unit.app K ≫ g'.inv.app (L'.obj K)) := by
    apply (adj.homEquiv K _).injective
    rw [Adjunction.homEquiv_naturality_right]
    simp only [Equiv.apply_symm_apply]
    rw [h]
    simp only [Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerRight_inv,
      Functor.whiskerRight_app, Category.assoc, ← R.map_comp,
      Iso.inv_hom_id_app, R.map_id]
    erw [Category.comp_id]
  rw [h] at hm ⊢
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, ← Category.assoc, ← R.map_comp, hm]

attribute [local irreducible] Functor.mapDerivedCategory HasDerivedCategory.standard
  completedIntegralCoefficientSheafUnrestricted scalarReductionExistence
  scalarReductionDerivedExistence scalarReductionDerivedExtension

private theorem ordinaryCompletedComp_eq
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R S T : Sheaf J RingCat.{u + 1}} (p : R ⟶ S) (q : S ⟶ T) (r : R ⟶ T)
    (h : p ≫ q = r)
    (hF : SheafOfModules.restrictScalars.{u + 1} q ⋙
      SheafOfModules.restrictScalars.{u + 1} p = SheafOfModules.restrictScalars.{u + 1} r) :
    normalizedDVRRestrictionCompIso p q ≪≫
        eqToIso (congrArg (fun f ↦ SheafOfModules.restrictScalars.{u + 1} f) h) =
      eqToIso hF := by
  change Iso.refl _ ≪≫ eqToIso _ = _
  simp only [Iso.refl_trans]

section
attribute [local semireducible] completedIntegralCoefficientSheafUnrestricted
private theorem completedProjection_comp (W : Scheme.{u})
    (D : FiniteFieldDatum.{0}) (hl : l ≠ D.p) (n : ℕ) :
    completedIntegralCoefficientProjection l E W D hl (n + 1) ≫
      normalizedDVRQuotient l E W n.le_succ =
        completedIntegralCoefficientProjection l E W D hl n := by
  exact limit.w (integralCoefficientSheafSystem l E W) (homOfLE n.le_succ).op
end

private theorem completedComp_change (W : Scheme.{u})
    (D : FiniteFieldDatum.{0}) (hl : l ≠ D.p) (n : ℕ) :
    letI := proEtaleCoefficientRestrictScalars_preservesFiniteLimits W
      (compactSupportLevelQuotient l E (n + 1) n n.le_succ)
    letI := proEtaleCoefficientRestrictScalars_preservesFiniteColimits W
      (compactSupportLevelQuotient l E (n + 1) n n.le_succ)
    normalizedDVRResCompletedComp l E W D hl n.le_succ =
      Functor.isoWhiskerRight
        (Functor.mapDerivedCategoryNatIso
          (eqToIso (compactSupportModuleRes_eq l E W n.le_succ)))
        (scalarReductionDerivedRestriction l E W (n + 1)) ≪≫
      compactSupportRestrictionComp l E W (n + 1) n n.le_succ := by
  letI := proEtaleCoefficientRestrictScalars_preservesFiniteLimits W
    (compactSupportLevelQuotient l E (n + 1) n n.le_succ)
  letI := proEtaleCoefficientRestrictScalars_preservesFiniteColimits W
    (compactSupportLevelQuotient l E (n + 1) n n.le_succ)
  let h := compactSupportModuleRes_eq l E W n.le_succ
  let h₀ := coefficientRestrictionComp l E W n.le_succ
  have h₁ : proEtaleCoefficientRestrictScalars W
      (compactSupportLevelQuotient l E (n + 1) n n.le_succ) ⋙
      scalarReductionRestriction l E W (n + 1) = scalarReductionRestriction l E W n :=
    (congrArg (fun F ↦ F ⋙ scalarReductionRestriction l E W (n + 1)) h).symm.trans h₀
  have he : pbcRestrictComp
      (completedIntegralCommRingProjectionUnrestricted l E W (n + 1))
      (compactSupportLevelSheafQuotient l E W (n + 1) n n.le_succ)
      (completedIntegralCommRingProjectionUnrestricted l E W n)
      (compactSupportProjection_comp l E W (n + 1) n n.le_succ) =
      eqToIso h₁ := by
    apply scalarComp_eqToIso
  have he₀ : normalizedDVRTransitionRestriction l E W D hl n = eqToIso h₀ := by
    exact ordinaryCompletedComp_eq
      (completedIntegralCoefficientProjection l E W D hl (n + 1))
      (normalizedDVRQuotient l E W n.le_succ)
      (completedIntegralCoefficientProjection l E W D hl n)
      (completedProjection_comp l E W D hl n) h₀
  rw [← normalizedDVRTransitionRestriction_comp]
  unfold compactSupportRestrictionComp pbcDerivedRestrictComp
  rw [he₀, he]
  exact derivedComp_change _ _ _ _ _ (eqIso_comp _ h h₁ h₀)

private theorem inputAdjacent (W : Scheme.{u})
    (K : DerivedCategory (scalarReductionSource l E W)) (n : ℕ) :
    (scalarReductionDerivedRestriction l E W (n + 1)).map
        (compactSupportReductionMap l E W (n + 1) n n.le_succ K) ≫
      (compactSupportRestrictionComp l E W (n + 1) n n.le_succ).hom.app
        ((scalarReductionDerivedExtension l E W n).obj K) =
      (sfDerivedReductionTransition l E W n).app K := by
  obtain ⟨D, hl⟩ := existsTestDatum l
  rw [sectionTransitionAdjoint l E W D hl n]
  letI := proEtaleCoefficientRestrictScalars_preservesFiniteLimits W
    (compactSupportLevelQuotient l E (n + 1) n n.le_succ)
  letI := proEtaleCoefficientRestrictScalars_preservesFiniteColimits W
    (compactSupportLevelQuotient l E (n + 1) n n.le_succ)
  exact (restrictedMate_change
    (derivedScalarExtensionRestrictionAdjunction l E W (n + 1)).choose
    (derivedScalarExtensionRestrictionAdjunction l E W n).choose
    (normalizedDVRRes l E W n.le_succ) _
    (Functor.mapDerivedCategoryNatIso (eqToIso (compactSupportModuleRes_eq l E W n.le_succ)))
    (normalizedDVRResCompletedComp l E W D hl n.le_succ)
    (compactSupportRestrictionComp l E W (n + 1) n n.le_succ)
    (completedComp_change l E W D hl n) K).symm

private def inputNativeTower (W : Scheme.{u})
    (M : coefficientSequenceRestrictedDerived.{u, u} l E W) :
    ℕᵒᵖ ⥤ DerivedCategory (scalarReductionSource l E W) where
  obj n := (pbcTowerEvaluation W
    (completedIntegralCommRingSheafUnrestricted l E W) n.unop).obj M
  map {m n} f := (pbcTowerTransition W
    (completedIntegralCommRingSheafUnrestricted l E W) m.unop n.unop
      (leOfHom f.unop)).app M
  map_id n := by
    have h : pbcTowerTransition W
        (completedIntegralCommRingSheafUnrestricted l E W) n.unop n.unop le_rfl = 𝟙 _ := by
      unfold pbcTowerTransition
      simp only [homOfLE_refl, op_id]
      erw [CategoryTheory.Functor.map_id, NatTrans.mapHomologicalComplex_id,
        Functor.whiskerRight_id, Localization.liftNatTrans_id]
    exact NatTrans.congr_app h M
  map_comp {r m n} f g := by
    have h : pbcTowerTransition W
        (completedIntegralCommRingSheafUnrestricted l E W) r.unop n.unop
          ((leOfHom g.unop).trans (leOfHom f.unop)) =
      pbcTowerTransition W (completedIntegralCommRingSheafUnrestricted l E W)
        r.unop m.unop (leOfHom f.unop) ≫
      pbcTowerTransition W (completedIntegralCommRingSheafUnrestricted l E W)
        m.unop n.unop (leOfHom g.unop) := by
      unfold pbcTowerTransition
      rw [Localization.comp_liftNatTrans]
      congr 1
      rw [← Functor.whiskerRight_comp, ← NatTrans.mapHomologicalComplex_comp,
        ← Functor.map_comp]
      rfl
    exact NatTrans.congr_app h M

/-- Restricting the direct quotient reduction to completed coefficients gives the
specified integral reduction tower, including its actual arrows.
Source: blueprint lem-coef-integral-compact-support, proof paragraphs 1--2; Stacks
Tags 06YY and 07A6 (blueprint: lem-coef-compact-support-input-tower-compatibility).

Proof: take the native derived coefficient system obtained by reducing K on the
ringed sequence site. Its finite evaluations identify with the derived reductions of
K. Its transitions and compactSupportReductionMap are adjuncts of the same smaller
reduction unit, under the scalar adjunction; injectivity of its Hom bijection identifies
them after quotient transport. Restrict this system to completed coefficients using
the evaluation-transition compatibility of the coefficient sequence calculus.
The ordinary restriction compositor
for the sequence quotient equals the direct quotient compositor: both act as the
identity on every underlying section. This equality passes to exact derived functors.
For adjacent levels, apply the scalar-extension/restriction Hom bijection. Both the
restricted quotient map and sfDerivedReductionTransition are adjuncts of the smaller
reduction unit followed by the inverse completed restriction compositor; their equality
is the normalized K-flat transition comparison (sectionTransitionAdjoint).
For equal indices, the native coefficient transition and the tower map are identities.
Induct on m-n: the native transitions compose by their cocycle, and the tower maps
compose by functoriality. The adjacent equality therefore identifies every map.
No boundedness, constructibility, or finite-type hypothesis is used. -/
theorem compactSupportInput_completed_tower (W : Scheme.{u})
    (K : DerivedCategory (scalarReductionSource l E W)) :
    ∀ (m n : ℕ) (h : n ≤ m),
      (scalarReductionDerivedRestriction l E W m).map
          (compactSupportReductionMap l E W m n h K) ≫
        (compactSupportRestrictionComp l E W m n h).hom.app
          ((scalarReductionDerivedExtension l E W n).obj K) =
        (sfIntegralReductionTower l E W K).map (homOfLE h).op := by
  classical
  obtain ⟨S, _hS⟩ := coefficientDerivedSystemEvaluationCalculus.{u, u} l E W
  let N := S.reduction.obj K
  let U := (coefficientSequenceDerivedRestriction l E W).obj N
  let T := inputNativeTower l E W U
  let e (n : ℕ) : T.obj (op n) ≅
      (sfDerivedReductionRestricted l E W n).obj K :=
    (coefficientRestrictedEvaluationIso l E W n).app N ≪≫
      (scalarReductionDerivedRestriction l E W n).mapIso ((S.reductionEvaluation n).app K)
  have he (m n : ℕ) (h : n ≤ m) :
      T.map (homOfLE h).op ≫ (e n).hom =
        (e m).hom ≫ (scalarReductionDerivedRestriction l E W m).map
          (compactSupportReductionMap l E W m n h K) ≫
        (compactSupportRestrictionComp l E W m n h).hom.app
          ((scalarReductionDerivedExtension l E W n).obj K) := by
    have ht := compactSupportCoefficientTransition_restricted l E W h N
    have hd := compactSupportReductionTransition l E W S.toCoefficientDerivedSystemReduction h K
    have hn := (compactSupportRestrictionComp l E W m n h).hom.naturality
      ((S.reductionEvaluation n).hom.app K)
    dsimp only [Functor.comp_map] at hn
    dsimp only [e, T, U, inputNativeTower, Iso.trans_hom, Iso.app_hom,
      Functor.mapIso_hom]
    rw [reassoc_of% ht]
    dsimp only [N, Functor.comp_obj] at hn ⊢
    erw [← hn]
    rw [← Functor.map_comp_assoc, hd, Functor.map_comp]
    simp only [Category.assoc]
    rfl
  let α : T ⟶ sfIntegralReductionTower l E W K := NatTrans.ofOpSequence
    (fun n ↦ (e n).hom) (by
      intro n
      rw [he, inputAdjacent]
      simp only [sfIntegralReductionTower, Functor.ofOpSequence_map_homOfLE_succ])
  intro m n h
  apply (cancel_epi (e m).hom).mp
  exact (he m n h).symm.trans (α.naturality (homOfLE h).op)

end WeilConjectures
