/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityTowerShriekData
import all WeilConjectures.CategoryTheory.Exact.ExactLocalizationInverseMate
import all WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.SemilinearEvaluationDerivedAdjunction

/-! # Evaluation of the tower open adjunction unit

Source: blueprint latest, integral direct-image proof, paragraph (3), and the
ordinary open-unit evaluation and termwise localization in SpTowerShriek.Open.
(blueprint: lem-sp-tower-open-adjunction-unit-evaluation)
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor HasDerivedCategory.standard

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.SpTowerShriek

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

section ExactUnits

variable {A B₀ : Type*} [Category A] [Category B₀] [Abelian A] [Abelian B₀]
  [HasDerivedCategory A] [HasDerivedCategory B₀]
  {L : A ⥤ B₀} {R₀ : B₀ ⥤ A} [L.Additive] [R₀.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [PreservesFiniteLimits R₀] [PreservesFiniteColimits R₀]

private def localize {F G : A ⥤ B₀} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (a : F ⟶ G) :
    F.mapDerivedCategory ⟶ G.mapDerivedCategory :=
  Localization.liftNatTrans DerivedCategory.Q (HomologicalComplex.quasiIso A (.up ℤ))
    (F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    F.mapDerivedCategory G.mapDerivedCategory
    (Functor.whiskerRight (NatTrans.mapHomologicalComplex a (.up ℤ)) DerivedCategory.Q)

private theorem localize_fac {F G : A ⥤ B₀} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (a : F ⟶ G) (K : CochainComplex A ℤ) :
    (localize a).app (DerivedCategory.Q.obj K) ≫ G.mapDerivedCategoryFactors.hom.app K =
      F.mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex a (.up ℤ)).app K) := by
  simp only [localize, Localization.liftNatTrans_app, Localization.Lifting.iso,
    Functor.whiskerRight_app, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

private theorem localize_unit (a : L ⊣ R₀) :
    (Functor.mapDerivedCategoryIdIso A).inv ≫ localize a.unit ≫
      (Functor.mapDerivedCategoryCompIso L R₀).hom =
        (exactLocalizationDerivedAdjunction a).unit := by
  apply Localization.natTrans_ext DerivedCategory.Q (HomologicalComplex.quasiIso A (.up ℤ))
  intro K
  apply (cancel_mono (R₀.mapDerivedCategory.map (L.mapDerivedCategoryFactors.hom.app K) ≫
    R₀.mapDerivedCategoryFactors.hom.app ((L.mapHomologicalComplex (.up ℤ)).obj K))).mp
  simp only [NatTrans.comp_app, Category.assoc]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_factors, localize_fac,
    ← Functor.mapDerivedCategoryIdIso_hom_app_Q_obj, Iso.inv_hom_id_app_assoc,
    CategoryTheory.exact_unit_app]
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  simp
  congr 1

private theorem localized_unit_evaluation (a : L ⊣ R₀) (a' : L' ⊣ R')
    (p : L ⋙ E₁ ≅ E₀ ⋙ L') (q : R₀ ⋙ E₀ ≅ E₁ ⋙ R')
    (hu : ∀ M, E₀.map (a.unit.app M) ≫ q.hom.app (L.obj M) ≫
      R'.map (p.hom.app M) = a'.unit.app (E₀.obj M)) (M : DerivedCategory A) :
    E₀.mapDerivedCategory.map ((exactLocalizationDerivedAdjunction a).unit.app M) ≫
      (Functor.mapDerivedCategorySquareIso q).hom.app (L.mapDerivedCategory.obj M) ≫
      R'.mapDerivedCategory.map ((Functor.mapDerivedCategorySquareIso p).hom.app M) =
      (exactLocalizationDerivedAdjunction a').unit.app (E₀.mapDerivedCategory.obj M) := by
  have hβ (K : A) : a'.unit.app (E₀.obj K) ≫ R'.map (p.inv.app K) =
      E₀.map (a.unit.app K) ≫ q.hom.app (L.obj K) := by
    rw [← hu K]
    simp only [Category.assoc, ← R'.map_comp, p.hom_inv_id_app]
    simp
  have hs : Functor.mapDerivedCategorySquareIso p.symm =
      (Functor.mapDerivedCategorySquareIso p).symm := by
    apply Iso.ext
    simp only [Functor.mapDerivedCategorySquareIso, Functor.mapDerivedCategoryNatIso_symm,
      Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, Category.assoc]
  have h : Functor.whiskerLeft E₀.mapDerivedCategory
        (exactLocalizationDerivedAdjunction a').unit ≫
      Functor.whiskerRight (Functor.mapDerivedCategorySquareIso p.symm).hom
        R'.mapDerivedCategory =
      Functor.whiskerRight (exactLocalizationDerivedAdjunction a).unit
        E₀.mapDerivedCategory ≫
      Functor.whiskerLeft L.mapDerivedCategory
        (Functor.mapDerivedCategorySquareIso q).hom := by
    apply Localization.natTrans_ext DerivedCategory.Q (HomologicalComplex.quasiIso A (.up ℤ))
    intro K
    exact CategoryTheory.mate_unit_Q a a' q p.symm hβ K
  have hM := congr_app h M
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    hs, Iso.symm_hom] at hM
  rw [← Category.assoc, ← hM]
  simp only [Category.assoc, ← R'.mapDerivedCategory.map_comp, Iso.inv_hom_id_app]
  erw [R'.mapDerivedCategory.map_id, Category.comp_id]

private theorem exact_adjunction_eq_local
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [Abelian.HasKInjectiveResolutions B]
    {L : A ⥤ B} {R : B ⥤ A} [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R] (a : L ⊣ R) :
    a.mapDerivedCategoryRightDerivedAdjunction.ofNatIsoRight
        R.rightDerivedFunctorIsoMapDerivedCategory = exactLocalizationDerivedAdjunction a := by
  apply Adjunction.ext
  apply Localization.natTrans_ext DerivedCategory.Q (HomologicalComplex.quasiIso A (.up ℤ))
  intro K
  let K' := (HomotopyCategory.quotient A (.up ℤ)).obj K
  have hs : (a.mapDerivedCategoryRightDerivedAdjunction.ofNatIsoRight
        R.rightDerivedFunctorIsoMapDerivedCategory).unit.app (DerivedCategory.Q.obj K) ≫
      R.mapDerivedCategory.map (L.mapDerivedCategoryFactorsh.hom.app K') ≫
      R.mapDerivedCategoryFactorsh.hom.app ((L.mapHomotopyCategory (.up ℤ)).obj K') =
    DerivedCategory.Qh.map ((a.mapHomotopyCategory (.up ℤ)).unit.app K') := by
    simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app,
      Category.assoc]
    rw [← R.rightDerivedFunctorIsoMapDerivedCategory.hom.naturality_assoc]
    have hu := (a.mapHomotopyCategory (.up ℤ)).derivedη_fac_app
      (HomotopyCategory.quasiIso A (.up ℤ))
      L.mapDerivedCategoryFactorsh.hom R.rightDerivedFunctorUnit K'
    change a.mapDerivedCategoryRightDerivedAdjunction.unit.app
      (DerivedCategory.Q.obj K) ≫
      R.rightDerivedFunctor.map (L.mapDerivedCategoryFactorsh.hom.app K') = _ at hu
    erw [reassoc_of% hu]
    have hf := congr_app R.rightDerivedFunctorIsoMapDerivedCategory_hom_fac
      ((L.mapHomotopyCategory (.up ℤ)).obj K')
    dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hf
    erw [reassoc_of% hf, Iso.inv_hom_id_app, Category.comp_id]
  have he : (exactLocalizationDerivedAdjunction a).unit.app (DerivedCategory.Q.obj K) ≫
      R.mapDerivedCategory.map (L.mapDerivedCategoryFactorsh.hom.app K') ≫
      R.mapDerivedCategoryFactorsh.hom.app ((L.mapHomotopyCategory (.up ℤ)).obj K') =
    DerivedCategory.Qh.map ((a.mapHomotopyCategory (.up ℤ)).unit.app K') := by
    rw [CategoryTheory.exact_unit_app]
    have hl := StrictTower.ConstantNormalization.factorsh_hom L K
    have hr := StrictTower.ConstantNormalization.factorsh_hom R
      ((L.mapHomologicalComplex (.up ℤ)).obj K)
    change L.mapDerivedCategoryFactorsh.hom.app K' = _ at hl
    change R.mapDerivedCategoryFactorsh.hom.app
      ((L.mapHomotopyCategory (.up ℤ)).obj K') = _ at hr
    rw [hl, hr]
    simp only [Category.assoc, ← R.mapDerivedCategory.map_comp_assoc,
      Iso.inv_hom_id_app]
    erw [R.mapDerivedCategory.map_id, Category.id_comp, Iso.inv_hom_id_app,
      Category.comp_id]
    change DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app K) =
      DerivedCategory.Qh.map ((a.mapHomotopyCategory (.up ℤ)).unit.app
        ((HomotopyCategory.quotient A (.up ℤ)).obj K))
    rw [Adjunction.mapHomotopyCategory_unit_app_quotient]
    rfl
  exact (cancel_mono (R.mapDerivedCategory.map (L.mapDerivedCategoryFactorsh.hom.app K') ≫
    R.mapDerivedCategoryFactorsh.hom.app ((L.mapHomotopyCategory (.up ℤ)).obj K'))).mp
    (by simpa only [Category.assoc] using hs.trans he.symm)

private theorem pull_evaluation_transport (b : Base l E)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (g : Geometry l E b f) (n : ℕ)
    (B' : ℕ → Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (τ' : ∀ k, B' (k + 1) ⟶ B' k)
    (hB : B' = B l E X) (hτ : HEq τ' (tau l E X))
    (F : S l E Y ⥤ WeilConjectures.SemilinearSections.Systems.{u + 1, u, u + 1}
      (Scheme.ProEt.topology X) B' τ')
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (hF : HEq g.pull F)
    (q : Σ L : WeilConjectures.SemilinearSections.Mod.{u + 1, u, u + 1}
        (Scheme.ProEt.topology Y) (B l E Y n) ⥤
      WeilConjectures.SemilinearSections.Mod.{u + 1, u, u + 1}
        (Scheme.ProEt.topology X) (B' n),
      Σ P : WeilConjectures.SemilinearSections.Mod.{u + 1, u, u + 1}
          (Scheme.ProEt.topology X) (B' n) ⥤
        WeilConjectures.SemilinearSections.Mod.{u + 1, u, u + 1}
          (Scheme.ProEt.topology Y) (B l E Y n), L ⊣ P)
    [q.1.Additive] [PreservesFiniteLimits q.1] [PreservesFiniteColimits q.1]
    (hq : HEq q
      (⟨proEtaleConstantRingPullback (R l E n) f,
        proEtaleConstantRingPushforward (R l E n) f,
        proEtaleConstantRingAdjunction (R l E n) f⟩ :
        Σ L : WeilConjectures.SemilinearSections.Mod.{u + 1, u, u + 1}
            (Scheme.ProEt.topology Y) (B l E Y n) ⥤
          WeilConjectures.SemilinearSections.Mod.{u + 1, u, u + 1}
            (Scheme.ProEt.topology X) (B l E X n),
        Σ P : WeilConjectures.SemilinearSections.Mod.{u + 1, u, u + 1}
            (Scheme.ProEt.topology X) (B l E X n) ⥤
          WeilConjectures.SemilinearSections.Mod.{u + 1, u, u + 1}
            (Scheme.ProEt.topology Y) (B l E Y n), L ⊣ P))
    (a : F ⋙ WeilConjectures.SemilinearSections.evaluation.{u + 1, u, u + 1}
      (Scheme.ProEt.topology X) B' τ' n ≅ ev l E Y n ⋙ q.1)
    (d : F.mapDerivedCategory ⋙
      WeilConjectures.SemilinearSections.e.{u + 1, u, u + 1}
        (Scheme.ProEt.topology X) B' τ' n ≅ Ev l E Y n ⋙ q.1.mapDerivedCategory)
    (ha : HEq (g.ordinaryPullEvaluation n) a) (hd : HEq (g.pullEvaluation n) d)
    (hm : d = Functor.mapDerivedCategorySquareIso a) :
    g.pullEvaluation n = Functor.mapDerivedCategorySquareIso (g.ordinaryPullEvaluation n) := by
  subst B'
  cases eq_of_heq hτ
  cases eq_of_heq hF
  cases eq_of_heq hq
  cases eq_of_heq ha
  cases eq_of_heq hd
  exact hm

private theorem pull_evaluation_model (b : Base l E)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (g : Geometry l E b f) (n : ℕ) :
    g.pullEvaluation n = Functor.mapDerivedCategorySquareIso (g.ordinaryPullEvaluation n) := by
  exact pull_evaluation_transport l E b g n
    g.generic.coefficients g.generic.coefficientTransition g.coefficients g.transitions
    g.generic.pull g.pull_eq
    ⟨(g.generic.inverseImage n).modules, g.generic.levelPush n, g.generic.levelAdjunction n⟩
    (g.levelAdjunction_eq n) (g.generic.ordinaryPullEvaluation n) (g.generic.pullEvaluation n)
    (g.ordinaryPullEvaluation_eq n) (g.pullEvaluation_eq n) (g.generic.pullEvaluation_model n)

/-- The specified derived open and inverse-image comparisons carry the tower unit
into the finite unit. No tensor or projection map occurs in this statement.
Source: blueprint latest, integral direct-image proof, paragraph (3), evaluation of
projection transposes; Open.unit_evaluation and Open.unit_termwise
(blueprint: lem-sp-tower-open-adjunction-unit-evaluation).
Proof: substitute Open.unit_termwise and the termwise definition of openEvaluation.
The inverse-image comparison is the localization of ordinaryPullEvaluation, by its
identification with the generic normalized comparison. On complexes, apply the
ordinary Open.unit_evaluation degree by degree. The factors for localization of
identities and compositions cancel by their naturality and associativity laws.
The finite adjunction is the right-derived localization of finiteOpenAdjunction,
transported along rightDerivedFunctorIsoMapDerivedCategory, so its unit is the
same termwise localized unit. Equality descends by the universal property of the
ordinary derived localization; no faithfulness of level evaluation is used. -/
theorem open_adjunction_unit_evaluation (b : Base l E)
    {U T : Scheme.{u}} {j : U ⟶ T} [IsOpenImmersion j]
    {g : Geometry l E b j} (o : Open l E b j g) (n : ℕ) (C : D l E U) :
    (Ev l E U n).map (o.derivedAdjunction.unit.app C) ≫
        (g.pullEvaluation n).hom.app ((openD l E b o).obj C) ≫
        (proEtaleConstantRingDerivedPullback (R l E n) j).map
          ((openEvaluation l E b o n).hom.app C) =
      (Adjunction.unit
        (((finiteOpenAdjunction l E b j n).mapDerivedCategoryRightDerivedAdjunction).ofNatIsoRight
          (proEtaleConstantRingPullback (R l E n) j).rightDerivedFunctorIsoMapDerivedCategory)).app
        ((Ev l E U n).obj C) := by
  let : Finite (R l E n) := b.finite n
  rw [exact_adjunction_eq_local]
  have hunit : o.derivedAdjunction.unit =
      (exactLocalizationDerivedAdjunction o.ordinaryAdjunction).unit := by
    rw [o.unit_termwise]
    exact localize_unit o.ordinaryAdjunction
  have hp : g.pullEvaluation n =
      Functor.mapDerivedCategorySquareIso (o.ordinaryPullEvaluation n) := by
    rw [pull_evaluation_model l E b g n]
    have h : g.ordinaryPullEvaluation n = o.ordinaryPullEvaluation n :=
      eq_of_heq ((g.ordinaryPullEvaluation_eq n).trans (o.ordinaryPullEvaluation_eq n).symm)
    rw [h]
  rw [hunit, hp]
  exact localized_unit_evaluation o.ordinaryAdjunction (finiteOpenAdjunction l E b j n)
    (o.evaluation n) (o.ordinaryPullEvaluation n) (o.unit_evaluation n) C

end ExactUnits

section Evaluation

variable {A B₀ A' B' : Type*}
  [Category A] [Category B₀] [Category A'] [Category B']
  [Abelian A] [Abelian B₀] [Abelian A'] [Abelian B']
  [HasDerivedCategory A] [HasDerivedCategory B₀]
  [HasDerivedCategory A'] [HasDerivedCategory B']
  {L : A ⥤ B₀} {R₀ : B₀ ⥤ A} {L' : A' ⥤ B'} {R' : B' ⥤ A'}
  {E₀ : A ⥤ A'} {E₁ : B₀ ⥤ B'}
  [L.Additive] [R₀.Additive] [L'.Additive] [R'.Additive]
  [E₀.Additive] [E₁.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [PreservesFiniteLimits R₀] [PreservesFiniteColimits R₀]
  [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
  [PreservesFiniteLimits R'] [PreservesFiniteColimits R']
  [PreservesFiniteLimits E₀] [PreservesFiniteColimits E₀]
  [PreservesFiniteLimits E₁] [PreservesFiniteColimits E₁]

end Evaluation

end AlgebraicGeometry.ProEtale.SpTowerShriek
