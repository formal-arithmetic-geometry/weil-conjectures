/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleContinuousCohomologyLimit
public import WeilConjectures.AlgebraicGeometry.MilnorTower
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.HomologySequence
public import WeilConjectures.CategoryTheory.Limits.TowerLimitShortComplex
import WeilConjectures.CategoryTheory.Abelian.CokernelToKernelShortExact
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Products
import WeilConjectures.AlgebraicGeometry.ProEtaleProductsExact
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence
import WeilConjectures.CategoryTheory.Finite.FiniteMittagLeffler
import WeilConjectures.CategoryTheory.DerivedLimitRoosAbelianGroups

/-!
# Continuous pro-étale cohomology

Source: Weil conjectures blueprint, latest, sec-proetale-coefficients,
`sk-prop-pe-continuous-cohomology`; Stacks Project, Tags 0CQD and 07KY.
(blueprint: proposition-continuous-cohomology-pro-etale-cohomology).

The `milnorTowerCokernel` in the statement is the canonical cokernel model for
`lim^1` of a tower of abelian groups. The derived-limit predicate in the
first clause is `IsDerivedLimit`.
-/

@[expose] public section

set_option autoImplicit false

universe t w w'

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.ProEt

attribute [local instance 30000] SheafOfModules.hasSheafify_coefficientUniverse
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse

namespace AlgebraicGeometry.ProEtale

/-- Module sheaves over the constant integer sheaf on the pro-étale site have K-injective
resolutions, because they form a Grothendieck abelian category. -/
noncomputable instance continuousCohomologyAbelianSheaves_hasKInjectiveResolutions
    (X : Scheme.{t}) :
    Abelian.HasKInjectiveResolutions (continuousCohomologyAbelianSheaves X) :=
  letI := SheafOfModules.isGrothendieckAbelianOfUniverses.{t + 1, t, t + 1, t + 1}
    (Scheme.ProEt.topology X)
    ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj
        (continuousCohomologyIntegerSheaf X))
  inferInstance

/-- Global sections `Γ(X, -)` of an abelian sheaf on the small pro-étale site: evaluation at
the terminal object `Scheme.ProEt.mk (𝟙 X)` of the underlying abelian sheaf. -/
noncomputable abbrev continuousCohomologySections (X : Scheme.{t}) :
    continuousCohomologyAbelianSheaves X ⥤ AddCommGrpCat.{t + 1} :=
  SheafOfModules.toSheaf _ ⋙ sheafToPresheaf _ _ ⋙
    (evaluation _ _).obj (op (Scheme.ProEt.mk (𝟙 X)))

/-- Derived global sections `RΓ(X, -)` on the small pro-étale site, applied to an abelian
sheaf placed in degree zero: the right derived functor of `continuousCohomologySections`
composed with the single-degree embedding.
Source: blueprint `sk-prop-pe-continuous-cohomology` (auxiliary; not a blueprint node). -/
noncomputable abbrev continuousCohomologyGlobalSections (X : Scheme.{t})
    [HasDerivedCategory.{w} (continuousCohomologyAbelianSheaves X)]
    [HasDerivedCategory.{w'} AddCommGrpCat.{t + 1}] :
    continuousCohomologyAbelianSheaves X ⥤ DerivedCategory AddCommGrpCat.{t + 1} :=
  DerivedCategory.singleFunctor _ 0 ⋙ (continuousCohomologySections X).rightDerivedFunctor

section Milnor

variable (X : Scheme.{t}) [HasDerivedCategory.{w} (continuousCohomologyAbelianSheaves X)]
  [HasDerivedCategory.{w'} AddCommGrpCat.{t + 1}]

local notation "Γ" => continuousCohomologySections X
local notation "RΓ" => continuousCohomologyGlobalSections X
local notation "H" => DerivedCategory.homologyFunctor AddCommGrpCat

omit [HasDerivedCategory.{w} (continuousCohomologyAbelianSheaves X)]
  [HasDerivedCategory.{w'} AddCommGrpCat.{t + 1}] in
/-- Global sections on the small pro-étale site preserve countable products. -/
private lemma continuousCohomologySections_preservesProducts :
    PreservesLimitsOfShape (Discrete ℕ) Γ := by
  have : PreservesLimitsOfShape (Discrete ℕ)
      (SheafOfModules.toSheaf _ ⋙ sheafToPresheaf (Scheme.ProEt.topology X) AddCommGrpCat.{t + 1} :
        continuousCohomologyAbelianSheaves X ⥤ _) := by
    change PreservesLimitsOfShape (Discrete ℕ)
      (SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _)
    infer_instance
  exact comp_preservesLimitsOfShape
    (SheafOfModules.toSheaf _ ⋙ sheafToPresheaf (Scheme.ProEt.topology X) AddCommGrpCat.{t + 1})
    ((evaluation _ _).obj _)

/-- Derived global sections on the small pro-étale site preserve countable products. -/
private lemma continuousCohomologyGlobalSections_preservesProducts :
    PreservesLimitsOfShape (Discrete ℕ) RΓ := by
  have : HasExactLimitsOfShape (Discrete ℕ) (continuousCohomologyAbelianSheaves X) :=
    Scheme.ProEt.products_exact.{t, 0, 0} X _ ℕ
  have : AB4StarOfSize.{0} AddCommGrpCat.{t + 1} := AB4StarOfSize_shrink.{0, t + 1} _
  have := continuousCohomologySections_preservesProducts X
  have : PreservesLimitsOfShape (Discrete ℕ) (Γ).rightDerivedFunctor :=
    Functor.preservesLimitsOfShape_discrete_rightDerivedFunctor _
  have : PreservesLimitsOfShape (Discrete ℕ)
      (DerivedCategory.singleFunctor (continuousCohomologyAbelianSheaves X) 0) :=
    preservesLimitsOfShape_of_natIso (DerivedCategory.singleFunctorIsoCompQ _ 0).symm
  exact comp_preservesLimitsOfShape _ _

omit [HasDerivedCategory.{w} (continuousCohomologyAbelianSheaves X)] in
/-- Cohomology of complexes of abelian groups commutes with countable products in the
derived category. -/
private lemma homologyFunctor_preservesProducts (q : ℤ) :
    PreservesLimitsOfShape (Discrete ℕ) (H q) := by
  have : AB4StarOfSize.{0} AddCommGrpCat.{t + 1} := AB4StarOfSize_shrink.{0, t + 1} _
  obtain ⟨_, _, h, _⟩ := derivedCategory_countableProducts_and_towerLimit AddCommGrpCat.{t + 1}
  exact h ℕ q

private instance isIso_piComparison_continuousCohomologyGlobalSections
    (K : ℕ → continuousCohomologyAbelianSheaves X) : IsIso (piComparison RΓ K) := by
  have := continuousCohomologyGlobalSections_preservesProducts X
  infer_instance

private instance isIso_piComparison_continuousCohomologyGlobalSections_homology
    (q : ℤ) (K : ℕ → continuousCohomologyAbelianSheaves X) :
    IsIso (piComparison (RΓ ⋙ H q) K) := by
  have := continuousCohomologyGlobalSections_preservesProducts X
  have := homologyFunctor_preservesProducts.{t, w'} q
  infer_instance

omit [HasDerivedCategory.{w'} AddCommGrpCat.{t + 1}] in
/-- For an epimorphic tower of abelian sheaves, `0 ⟶ lim F ⟶ ∏ Fₙ ⟶ ∏ Fₙ ⟶ 0` is exact. -/
private lemma towerLimitShortComplex_shortExact_of_epi
    (F : ℕᵒᵖ ⥤ continuousCohomologyAbelianSheaves X)
    (hF : ∀ n : ℕ, Epi (F.map (homOfLE (Nat.le_succ n)).op)) :
    (towerLimitShortComplex F).ShortExact :=
  towerLimitShortComplex_shortExact F (milnor_epimorphic.{0, t, w} X _ F hF).1

/-- The connecting map `H^(q-1)(X, ∏ Fₙ) ⟶ H^q(X, lim F)` kills the image of `1 - T`. -/
private lemma continuousCohomologyMilnorMap_condition (q : ℤ)
    (F : ℕᵒᵖ ⥤ continuousCohomologyAbelianSheaves X)
    (hF : ∀ n : ℕ, Epi (F.map (homOfLE (Nat.le_succ n)).op)) :
    towerTransitionEndomorphism (K := fun n : ℕ ↦ (F ⋙ RΓ ⋙ H (q - 1)).obj (op n))
        (fun n ↦ (F ⋙ RΓ ⋙ H (q - 1)).map (homOfLE (Nat.le_succ n)).op) ≫
      inv (piComparison (RΓ ⋙ H (q - 1)) (fun n : ℕ ↦ F.obj (op n))) ≫
        (Γ).rightDerivedHomologyδ (towerLimitShortComplex_shortExact_of_epi X F hF) (q - 1) q
          (by omega) = 0 := by
  have h := map_towerTransitionEndomorphism_comp_piComparison (RΓ ⋙ H (q - 1))
    (fun n : ℕ ↦ F.obj (op n)) (fun n ↦ F.map (homOfLE (Nat.le_succ n)).op)
  have h' : towerTransitionEndomorphism
      (K := fun n : ℕ ↦ (F ⋙ RΓ ⋙ H (q - 1)).obj (op n))
      (fun n ↦ (F ⋙ RΓ ⋙ H (q - 1)).map (homOfLE (Nat.le_succ n)).op) ≫
        inv (piComparison (RΓ ⋙ H (q - 1)) (fun n : ℕ ↦ F.obj (op n))) =
      inv (piComparison (RΓ ⋙ H (q - 1)) (fun n : ℕ ↦ F.obj (op n))) ≫
        (RΓ ⋙ H (q - 1)).map (towerLimitShortComplex F).g := by
    rw [IsIso.eq_inv_comp]
    exact ((reassoc_of% h) _).symm.trans (by simp [towerLimitShortComplex])
  have h0 : (RΓ ⋙ H (q - 1)).map (towerLimitShortComplex F).g ≫
      (Γ).rightDerivedHomologyδ (towerLimitShortComplex_shortExact_of_epi X F hF) (q - 1) q
        (by omega) = 0 :=
    (Γ).rightDerivedHomology_map_comp_δ _ _ _ _
  rw [← Category.assoc, h', Category.assoc, h0, comp_zero]

/-- The Milnor map `coker(1 - T on ∏ₙ H^(q-1)(X, Fₙ)) ⟶ H^q(X, lim F)`, induced by the
connecting map of `0 ⟶ lim F ⟶ ∏ Fₙ ⟶ ∏ Fₙ ⟶ 0`. -/
private noncomputable def continuousCohomologyMilnorMap (q : ℤ)
    (F : ℕᵒᵖ ⥤ continuousCohomologyAbelianSheaves X)
    (hF : ∀ n : ℕ, Epi (F.map (homOfLE (Nat.le_succ n)).op)) :
    milnorTowerCokernel (F ⋙ RΓ ⋙ H (q - 1)) ⟶ (H q).obj ((RΓ).obj (limit F)) :=
  cokernel.desc _ (inv (piComparison (RΓ ⋙ H (q - 1)) (fun n : ℕ ↦ F.obj (op n))) ≫
    (Γ).rightDerivedHomologyδ (towerLimitShortComplex_shortExact_of_epi X F hF) (q - 1) q
      (by omega)) (continuousCohomologyMilnorMap_condition X q F hF)

/-- The map `H^q(X, lim F) ⟶ lim H^q(X, Fₙ)` induced by the limit projections. -/
private noncomputable def continuousCohomologyLimitMap (q : ℤ)
    (F : ℕᵒᵖ ⥤ continuousCohomologyAbelianSheaves X) :
    (H q).obj ((RΓ).obj (limit F)) ⟶ limit (F ⋙ RΓ ⋙ H q) :=
  limit.lift _ ((RΓ ⋙ H q).mapCone (limit.cone F))

@[reassoc]
private lemma continuousCohomologyLimitMap_π (q : ℤ)
    (F : ℕᵒᵖ ⥤ continuousCohomologyAbelianSheaves X) (n : ℕᵒᵖ) :
    continuousCohomologyLimitMap X q F ≫ limit.π (F ⋙ RΓ ⋙ H q) n =
      (H q).map ((RΓ).map (limit.π F n)) :=
  limit.lift_π _ _

/-- The Milnor sequence `0 ⟶ coker(1 - T) ⟶ H^q(X, lim F) ⟶ lim H^q(X, Fₙ) ⟶ 0` is exact. -/
private lemma continuousCohomologyMilnor_shortExact (q : ℤ)
    (F : ℕᵒᵖ ⥤ continuousCohomologyAbelianSheaves X)
    (hF : ∀ n : ℕ, Epi (F.map (homOfLE (Nat.le_succ n)).op)) :
    ∃ h : continuousCohomologyMilnorMap X q F hF ≫ continuousCohomologyLimitMap X q F = 0,
      (ShortComplex.mk _ _ h).ShortExact := by
  have hS := towerLimitShortComplex_shortExact_of_epi X F hF
  let c₀ := piComparison (RΓ ⋙ H (q - 1)) (fun n : ℕ ↦ F.obj (op n))
  let c₁ := piComparison (RΓ ⋙ H q) (fun n : ℕ ↦ F.obj (op n))
  have hc₀ := map_towerTransitionEndomorphism_comp_piComparison (RΓ ⋙ H (q - 1))
    (fun n : ℕ ↦ F.obj (op n)) (fun n ↦ F.map (homOfLE (Nat.le_succ n)).op)
  have hc₁ := map_towerTransitionEndomorphism_comp_piComparison (RΓ ⋙ H q)
    (fun n : ℕ ↦ F.obj (op n)) (fun n ↦ F.map (homOfLE (Nat.le_succ n)).op)
  let v := (H q).map ((Γ).rightDerivedFunctor.map
    ((DerivedCategory.singleFunctor _ 0).map (towerLimitShortComplex F).f)) ≫ c₁
  have hdv : (inv c₀ ≫ (Γ).rightDerivedHomologyδ hS (q - 1) q (by omega)) ≫ v = 0 := by
    simp only [v, Category.assoc, (Γ).rightDerivedHomologyδ_comp_map_assoc, zero_comp,
      comp_zero]
  have hvw : v ≫ (towerLimitShortComplex (F ⋙ RΓ ⋙ H q)).g = 0 := by
    have h : c₁ ≫ (towerLimitShortComplex (F ⋙ RΓ ⋙ H q)).g =
        (H q).map ((Γ).rightDerivedFunctor.map
          ((DerivedCategory.singleFunctor _ 0).map (towerLimitShortComplex F).g)) ≫ c₁ :=
      hc₁.symm
    simp only [v, Category.assoc, h]
    rw [← Category.assoc, (Γ).rightDerivedHomology_map_comp_eq_zero, zero_comp]
  refine ShortComplex.shortExact_cokernelDesc_of_exact
    (continuousCohomologyMilnorMap_condition X q F hF) hdv hvw ?_ ?_ ?_
    (towerLimitShortComplex.isLimit (F ⋙ RΓ ⋙ H q)) _ ?_
  · refine ShortComplex.exact_of_iso ?_
      ((Γ).rightDerivedHomologySequence_exact₃ hS (q - 1) q (by omega))
    refine ShortComplex.isoMk (asIso c₀) (asIso c₀) (Iso.refl _) ?_ ?_
    · exact hc₀.symm
    · simp [c₀]
  · refine ShortComplex.exact_of_iso ?_
      ((Γ).rightDerivedHomologySequence_exact₁ hS (q - 1) q (by omega))
    refine ShortComplex.isoMk (asIso c₀) (Iso.refl _) (asIso c₁) ?_ ?_
    · simp [c₀]
    · simp [v]
  · refine ShortComplex.exact_of_iso ?_ ((Γ).rightDerivedHomologySequence_exact₂ hS q)
    refine ShortComplex.isoMk (Iso.refl _) (asIso c₁) (asIso c₁) ?_ ?_
    · simp [v]
    · exact hc₁.symm
  · apply Pi.hom_ext
    intro n
    have h1 : (towerLimitShortComplex (F ⋙ RΓ ⋙ H q)).f ≫
        Pi.π (fun b ↦ (RΓ ⋙ H q).obj (F.obj (op b))) n = limit.π (F ⋙ RΓ ⋙ H q) (op n) :=
      Pi.lift_comp_π _ n
    have h2 : (towerLimitShortComplex F).f ≫ Pi.π (fun n ↦ F.obj (op n)) n = limit.π F (op n) :=
      Pi.lift_comp_π _ n
    simp only [v, c₁, Category.assoc]
    rw [h1, continuousCohomologyLimitMap_π]
    erw [piComparison_comp_π]
    rw [← h2]
    simp only [Functor.map_comp]
    rfl

/-- The Milnor map is natural in the epimorphic tower. -/
private lemma continuousCohomologyMilnorMap_naturality (q : ℤ)
    (F G : ℕᵒᵖ ⥤ continuousCohomologyAbelianSheaves X)
    (hF : ∀ n : ℕ, Epi (F.map (homOfLE (Nat.le_succ n)).op))
    (hG : ∀ n : ℕ, Epi (G.map (homOfLE (Nat.le_succ n)).op)) (f : F ⟶ G) :
    milnorTowerCokernelMap (Functor.whiskerRight (Functor.whiskerRight f RΓ) (H (q - 1))) ≫
        continuousCohomologyMilnorMap X q G hG =
      continuousCohomologyMilnorMap X q F hF ≫ (H q).map ((RΓ).map (limMap f)) := by
  have hSF := towerLimitShortComplex_shortExact_of_epi X F hF
  have hSG := towerLimitShortComplex_shortExact_of_epi X G hG
  have hδ := (Γ).rightDerivedHomologyδ_naturality hSF hSG (towerLimitShortComplexMap f)
    (q - 1) q (by omega)
  have hc : Limits.Pi.map (fun n : ℕ ↦
        (Functor.whiskerRight (Functor.whiskerRight f RΓ) (H (q - 1))).app (op n)) ≫
        inv (piComparison (RΓ ⋙ H (q - 1)) (fun n : ℕ ↦ G.obj (op n))) =
      inv (piComparison (RΓ ⋙ H (q - 1)) (fun n : ℕ ↦ F.obj (op n))) ≫
        (H (q - 1)).map ((Γ).rightDerivedFunctor.map ((DerivedCategory.singleFunctor _ 0).map
          (towerLimitShortComplexMap f).τ₃)) := by
    rw [IsIso.comp_inv_eq, Category.assoc, IsIso.eq_inv_comp]
    exact (map_piMap_comp_piComparison (RΓ ⋙ H (q - 1)) (fun n : ℕ ↦ f.app (op n))).symm
  apply coequalizer.hom_ext
  simp only [milnorTowerCokernelMap, continuousCohomologyMilnorMap, cokernel.π_desc_assoc,
    Category.assoc]
  erw [cokernel.π_desc, cokernel.π_desc_assoc]
  rw [reassoc_of% hc, hδ]
  rfl

/-- The map to the limit of the cohomology groups is natural in the tower. -/
private lemma continuousCohomologyLimitMap_naturality (q : ℤ)
    (F G : ℕᵒᵖ ⥤ continuousCohomologyAbelianSheaves X) (f : F ⟶ G) :
    (H q).map ((RΓ).map (limMap f)) ≫ continuousCohomologyLimitMap X q G =
      continuousCohomologyLimitMap X q F ≫
        limMap (Functor.whiskerRight (Functor.whiskerRight f RΓ) (H q)) := by
  apply limit.hom_ext
  intro n
  rw [Category.assoc, continuousCohomologyLimitMap_π, Category.assoc]
  erw [limMap_π, continuousCohomologyLimitMap_π_assoc]
  rw [← Functor.map_comp, ← Functor.map_comp, limMap_π]
  simp

/-- Derived global sections turn an epimorphic tower into a derived limit. -/
private lemma continuousCohomology_isDerivedLimit
    (F : ℕᵒᵖ ⥤ continuousCohomologyAbelianSheaves X)
    (hF : ∀ n : ℕ, Epi (F.map (homOfLE (Nat.le_succ n)).op)) :
    IsDerivedLimit (K := fun n : ℕ ↦ (RΓ).obj (F.obj (op n)))
      (fun n : ℕ ↦ (RΓ).map (F.map (homOfLE (Nat.le_succ n)).op)) ((RΓ).obj (limit F)) := by
  have hS := towerLimitShortComplex_shortExact_of_epi X F hF
  let T := (Γ).rightDerivedSingleTriangle hS
  have hT := (Γ).rightDerivedSingleTriangle_distinguished hS
  let e := asIso (piComparison RΓ (fun n : ℕ ↦ F.obj (op n)))
  have hg : T.mor₂ ≫ e.hom = e.hom ≫ towerTransitionEndomorphism
      (fun n : ℕ ↦ (RΓ).map (F.map (homOfLE (Nat.le_succ n)).op)) :=
    map_towerTransitionEndomorphism_comp_piComparison RΓ _ _
  refine ⟨T.mor₁ ≫ e.hom, e.inv ≫ T.mor₃, ?_⟩
  exact (Pretriangulated.distinguished_iff_of_iso (Pretriangulated.Triangle.isoMk T
    (Pretriangulated.Triangle.mk (T.mor₁ ≫ e.hom) (towerTransitionEndomorphism _)
      (e.inv ≫ T.mor₃)) (Iso.refl _) e e (by simp) hg (by simp))).mp hT

end Milnor

/-- A tower of finite abelian groups is Mittag-Leffler, so `1 - T` on its product is
surjective. -/
private lemma isZero_milnorTowerCokernel_of_finite (M : ℕᵒᵖ ⥤ AddCommGrpCat.{t + 1})
    (hM : ∀ n : ℕᵒᵖ, Finite (M.obj n)) : IsZero (milnorTowerCokernel M) := by
  obtain ⟨_, _, e₁, _, _⟩ := derivedLimitRoosAbelianGroups.{t + 1}
  exact (finiteTower_mittagLeffler_vanishing M hM).2.of_iso (e₁ M).symm

/-- The comparison, Milnor exact sequence, naturality, and finite-level vanishing
for an epimorphic inverse system of abelian sheaves on the small pro-étale site.

Proof:
1. Epimorphic transitions make `1 - T` an epimorphism of sheaves (`milnor_epimorphic`), so
   `0 ⟶ lim F ⟶ ∏ Fₙ ⟶ ∏ Fₙ ⟶ 0` is short exact. Apply `RΓ` to its distinguished
   triangle. Since `RΓ` preserves countable products, this is a derived-limit triangle.
2. In its long exact cohomology sequence, cohomology commutes with countable products of
   abelian groups and turns `1 - T` into the transition endomorphism of the cohomology
   towers. The connecting map factors through `milnorTowerCokernel` and the cohomology
   of `lim F ⟶ ∏ Fₙ` lands in the kernel of `1 - T`, namely the limit. Exactness gives the
   short exact sequence; naturality of the connecting map gives the naturality squares.
3. For a tower of finite groups, `1 - T` is surjective (Mittag-Leffler), so its cokernel
   vanishes.
(blueprint: proposition-continuous-cohomology-pro-etale-cohomology,
proposition-continuous-cohomology-pro-etale-cohomology--1).
-/
theorem continuousCohomology
    (X : Scheme.{t})
    [HasDerivedCategory.{w} (continuousCohomologyAbelianSheaves X)]
    [HasDerivedCategory.{w'} AddCommGrpCat.{t + 1}]
    (F : ℕᵒᵖ ⥤ continuousCohomologyAbelianSheaves X)
    (ht : ∀ n : ℕ, Epi (F.map (homOfLE (Nat.le_succ n)).op)) :
    IsDerivedLimit
        (K := fun n : ℕ ↦
          (continuousCohomologyGlobalSections X).obj (F.obj (op n)))
        (fun n : ℕ ↦ (continuousCohomologyGlobalSections X).map
          (F.map (homOfLE (Nat.le_succ n)).op))
        ((continuousCohomologyGlobalSections X).obj (limit F)) ∧
      ∀ q : ℤ,
        ∃ (a : ∀ (F : ℕᵒᵖ ⥤ continuousCohomologyAbelianSheaves X)
            (_ : ∀ n : ℕ, Epi (F.map (homOfLE (Nat.le_succ n)).op)),
            milnorTowerCokernel
                (F ⋙ continuousCohomologyGlobalSections X ⋙
                  DerivedCategory.homologyFunctor AddCommGrpCat.{t + 1} (q - 1)) ⟶
              (DerivedCategory.homologyFunctor AddCommGrpCat.{t + 1} q).obj
                ((continuousCohomologyGlobalSections X).obj (limit F)))
          (b : ∀ (F : ℕᵒᵖ ⥤ continuousCohomologyAbelianSheaves X)
            (_ : ∀ n : ℕ, Epi (F.map (homOfLE (Nat.le_succ n)).op)),
            (DerivedCategory.homologyFunctor AddCommGrpCat.{t + 1} q).obj
                ((continuousCohomologyGlobalSections X).obj (limit F)) ⟶
              limit (F ⋙ continuousCohomologyGlobalSections X ⋙
                DerivedCategory.homologyFunctor AddCommGrpCat.{t + 1} q)),
          (∀ (F : ℕᵒᵖ ⥤ continuousCohomologyAbelianSheaves X)
            (hF : ∀ n : ℕ, Epi (F.map (homOfLE (Nat.le_succ n)).op)),
            ∃ h : a F hF ≫ b F hF = 0,
              (ShortComplex.mk (a F hF) (b F hF) h).ShortExact) ∧
          (∀ (F G : ℕᵒᵖ ⥤ continuousCohomologyAbelianSheaves X)
            (hF : ∀ n : ℕ, Epi (F.map (homOfLE (Nat.le_succ n)).op))
            (hG : ∀ n : ℕ, Epi (G.map (homOfLE (Nat.le_succ n)).op))
            (f : F ⟶ G),
            milnorTowerCokernelMap
                (Functor.whiskerRight
                  (Functor.whiskerRight f (continuousCohomologyGlobalSections X))
                  (DerivedCategory.homologyFunctor AddCommGrpCat.{t + 1} (q - 1))) ≫
                a G hG =
              a F hF ≫
                (DerivedCategory.homologyFunctor AddCommGrpCat.{t + 1} q).map
                  ((continuousCohomologyGlobalSections X).map (limMap f)) ∧
            (DerivedCategory.homologyFunctor AddCommGrpCat.{t + 1} q).map
                  ((continuousCohomologyGlobalSections X).map (limMap f)) ≫
                b G hG =
              b F hF ≫ limMap
                (Functor.whiskerRight
                  (Functor.whiskerRight f (continuousCohomologyGlobalSections X))
                  (DerivedCategory.homologyFunctor AddCommGrpCat.{t + 1} q))) ∧
          (∀ (F : ℕᵒᵖ ⥤ continuousCohomologyAbelianSheaves X)
            (hF : ∀ n : ℕ, Epi (F.map (homOfLE (Nat.le_succ n)).op)) (n : ℕᵒᵖ),
            b F hF ≫ limit.π
                (F ⋙ continuousCohomologyGlobalSections X ⋙
                  DerivedCategory.homologyFunctor AddCommGrpCat.{t + 1} q) n =
              (DerivedCategory.homologyFunctor AddCommGrpCat.{t + 1} q).map
                ((continuousCohomologyGlobalSections X).map (limit.π F n))) ∧
          (∀ (F : ℕᵒᵖ ⥤ continuousCohomologyAbelianSheaves X)
            (_ : ∀ n : ℕ, Epi (F.map (homOfLE (Nat.le_succ n)).op)),
            (∀ n : ℕᵒᵖ, Finite
              ((F ⋙ continuousCohomologyGlobalSections X ⋙
                DerivedCategory.homologyFunctor AddCommGrpCat.{t + 1} (q - 1)).obj n)) →
            IsZero (milnorTowerCokernel
              (F ⋙ continuousCohomologyGlobalSections X ⋙
                DerivedCategory.homologyFunctor AddCommGrpCat.{t + 1} (q - 1)))) :=
  ⟨continuousCohomology_isDerivedLimit X F ht, fun q ↦
    ⟨fun F hF ↦ continuousCohomologyMilnorMap X q F hF,
      fun F _ ↦ continuousCohomologyLimitMap X q F,
      fun F hF ↦ continuousCohomologyMilnor_shortExact X q F hF,
      fun F G hF hG f ↦ ⟨continuousCohomologyMilnorMap_naturality X q F G hF hG f,
        continuousCohomologyLimitMap_naturality X q F G f⟩,
      fun F _ n ↦ continuousCohomologyLimitMap_π X q F n,
      fun _ _ hfin ↦ isZero_milnorTowerCokernel_of_finite _ hfin⟩⟩

end AlgebraicGeometry.ProEtale
