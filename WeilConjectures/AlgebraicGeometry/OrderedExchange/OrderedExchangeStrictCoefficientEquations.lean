/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.OrderedExchange.OrderedExchangeCoefficientData
import all WeilConjectures.AlgebraicGeometry.Strict.Tower.StrictTowerExchangeMateNormalization
import all WeilConjectures.AlgebraicGeometry.OrderedExchange.ProEtaleConstantReductionModels
import all WeilConjectures.AlgebraicGeometry.Stratum.StratumCompletionUnitRestriction
import WeilConjectures.AlgebraicGeometry.Completed.CompletedReductionUnit
import WeilConjectures.AlgebraicGeometry.CompletedConstantAlgebraFlatQuotients

/-! # strictCoefficientEquations -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.OrderedExchange
variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
variable {X' X Y' Y : Scheme.{t}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y}

section DerivedSquares

variable {C₁ C₂ C₃ C₄ : Type*} [Category C₁] [Category C₂] [Category C₃] [Category C₄]
  [Abelian C₁] [Abelian C₂] [Abelian C₃] [Abelian C₄]
  [HasDerivedCategory C₁] [HasDerivedCategory C₂] [HasDerivedCategory C₃]
  [HasDerivedCategory C₄]

/-- The derived square induced by an isomorphism of exact composites, evaluated on the
localization of a complex. -/
private theorem mapDerivedCategorySquareIso_hom_app_Q
    {F₁ : C₁ ⥤ C₂} {F₂ : C₂ ⥤ C₄} {G₁ : C₁ ⥤ C₃} {G₂ : C₃ ⥤ C₄}
    [F₁.Additive] [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [F₂.Additive] [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
    [G₁.Additive] [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
    [G₂.Additive] [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
    (e : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂) (K : CochainComplex C₁ ℤ) :
    (Functor.mapDerivedCategorySquareIso e).hom.app (DerivedCategory.Q.obj K) ≫
        G₂.mapDerivedCategory.map (G₁.mapDerivedCategoryFactors.hom.app K) ≫
        G₂.mapDerivedCategoryFactors.hom.app ((G₁.mapHomologicalComplex (.up ℤ)).obj K) =
      F₂.mapDerivedCategory.map (F₁.mapDerivedCategoryFactors.hom.app K) ≫
        F₂.mapDerivedCategoryFactors.hom.app ((F₁.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app K) := by
  have hG := Functor.mapDerivedCategoryCompIso_fac G₁ G₂ K
  have hF := Functor.mapDerivedCategoryCompIso_fac F₁ F₂ K
  have hN := Functor.mapDerivedCategoryNatIso_fac e K
  have hcF : (Functor.mapHomologicalComplexCompIso (Iso.refl (F₁ ⋙ F₂)) (.up ℤ)).hom.app K =
      𝟙 _ := by
    ext i
    rfl
  have hcG : (Functor.mapHomologicalComplexCompIso (Iso.refl (G₁ ⋙ G₂)) (.up ℤ)).hom.app K =
      𝟙 _ := by
    ext i
    rfl
  rw [hcF] at hF
  erw [CategoryTheory.Functor.map_id, Category.comp_id] at hF
  rw [hcG] at hG
  erw [CategoryTheory.Functor.map_id, Category.comp_id] at hG
  simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Category.assoc]
  rw [hG, hN, ← hF]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]

/-- The universal counit of a derived reduction model is natural in chain maps. -/
private theorem complexCounit_naturality {B C : Type*} [Category B] [Abelian B]
    [Category C] [Abelian C] [HasDerivedCategory B] [HasDerivedCategory C]
    {F : B ⥤ C} [F.Additive] {P : CochainComplex B ℤ → Prop}
    (D : DerivedReductionModelData F P) {K K' : CochainComplex B ℤ} (φ : K ⟶ K') :
    D.reduction.map (DerivedCategory.Q.map φ) ≫ D.complexCounit K' =
      D.complexCounit K ≫ DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map φ) := by
  have h1 := (DerivedCategory.quotientCompQhIso B).inv.naturality φ
  have h2 := D.counit.naturality ((HomotopyCategory.quotient _ (.up ℤ)).map φ)
  have h3 := (F.mapHomotopyCategoryFactors (.up ℤ)).hom.naturality φ
  have h4 := (DerivedCategory.quotientCompQhIso C).hom.naturality
      ((F.mapHomologicalComplex (.up ℤ)).map φ)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj, Functor.id_map] at h1 h2 h3 h4
  unfold DerivedReductionModelData.complexCounit
  rw [← Functor.map_comp_assoc, h1, Functor.map_comp_assoc, reassoc_of% h2,
    ← Functor.map_comp_assoc, h3, Functor.map_comp_assoc, h4]
  simp only [Category.assoc]

end DerivedSquares

section OrdinaryPull

/-- The ordinary constant augmentation followed by `ordinaryRho` is the restricted completed
quotient unit, at every level. Source: Stacks 099M
(blueprint: def-weil-pbc-ordered-coefficient-comparison-data). -/
theorem ordinaryAugmentation_ordinaryRho (T : Scheme.{t})
    (N : reductionModules T (d.completedRing T)) (n : ℕ) :
    ((ordinaryAugmentation d T).app ((reductionRestrict T (exchangeScalar d T)).obj N)).app
        (op n) ≫ ((ordinaryRho d T).hom.app N).app (op n) =
      (reductionRestrict T (exchangeScalar d T)).map
        (((completedReductionModuleUnit d T).app N).app (op n)) := by
  ext U x
  change (((ordinaryRho d T).hom.app N).app (op n)).val.app U
      ((((ordinaryAugmentation d T).app
        ((reductionRestrict T (exchangeScalar d T)).obj N)).app (op n)).val.app U x) =
    (((completedReductionModuleUnit d T).app N).app (op n)).val.app U x
  have h1 : ((((ordinaryAugmentation d T).app
      ((reductionRestrict T (exchangeScalar d T)).obj N)).app (op n)).val.app U x) =
      reductionTensorSection T (quotient d T n)
        ((reductionRestrict T (exchangeScalar d T)).obj N) U 1 x :=
    (ordinaryAugmentation_existsUnique d T).exists.choose_spec _ n U x
  have h2 := (completedReductionModuleUnit_exists d T).exists.choose_spec N n U x
  rw [h1]
  exact ((ordinaryRho_existsUnique d T).exists.choose_spec N n U 1 x).trans h2.symm

theorem ordinaryAugmentation_eq_unit (T : Scheme.{t})
    (L : reductionModules T (exchangeConstantRing T A)) (n : ℕ) :
    ((ordinaryAugmentation d T).app L).app (op n) =
      (proEtaleRingExtensionAdjunction (quotient d T n)).unit.app L := by
  ext W x
  have h1 : (((ordinaryAugmentation d T).app L).app (op n)).val.app W x =
      reductionTensorSection T (quotient d T n) L W 1 x :=
    (ordinaryAugmentation_existsUnique d T).exists.choose_spec L n W x
  rw [h1]
  exact ((pbcScalarAdjunction_exists (quotient d T n)).exists.choose_spec L W x).symm

/-- The ordinary constant reduction/pullback comparison preserves the ordinary augmentation.
Source: Stacks 099M, 0D6D (blueprint: lem-sp-completion-mate-comparison). -/
theorem ordinaryAugmentation_ordinaryReductionPullIso {U V : Scheme.{t}} (u : U ⟶ V)
    (L : reductionModules V (exchangeConstantRing V A)) (n : ℕ) :
    (proEtaleRingModulePullback u (exchangeConstantRing V A) (exchangeConstantRing U A)
        (exchangeConstantIso u A)).map (((ordinaryAugmentation d V).app L).app (op n)) ≫
      ((ordinaryReductionPullIso d u).hom.app L).app (op n) =
    ((ordinaryAugmentation d U).app ((proEtaleRingModulePullback u (exchangeConstantRing V A)
        (exchangeConstantRing U A) (exchangeConstantIso u A)).obj L)).app (op n) := by
  rw [ordinaryAugmentation_eq_unit, ordinaryAugmentation_eq_unit]
  exact levelPullIso_unit d u n L

/-- The ordinary core of the compatibility of `rho` with pullback, at one tower level.
Source: Stacks 099M, 0D6D (blueprint: def-weil-pbc-ordered-coefficient-comparison-data). -/
theorem ordinaryRho_pull {U V : Scheme.{t}} (u : U ⟶ V)
    (M : reductionModules V (d.completedRing V)) (n : ℕ) :
    (reductionRestrict U (exchangeScalar d U)).map
        (((stratumModuleReductionIso d u).hom.app M).app (op n)) ≫
      ((ordinaryRho d U).inv.app ((stratumModulePull d u).obj M)).app (op n) ≫
      ((reductionModule d U).map ((exchangeOrdinaryResPull d u).hom.app M)).app (op n) =
    (exchangeOrdinaryResPull d u).hom.app
        (((completedReductionModuleTowerFunctor V d).obj M).obj (op n)) ≫
      (proEtaleRingModulePullback u (exchangeConstantRing V A) (exchangeConstantRing U A)
        (exchangeConstantIso u A)).map (((ordinaryRho d V).inv.app M).app (op n)) ≫
      ((ordinaryReductionPullIso d u).hom.app
        ((reductionRestrict V (exchangeScalar d V)).obj M)).app (op n) := by
  have hε : Epi ((reductionRestrict U (exchangeScalar d U)).map
      ((stratumModulePull d u).map (((completedReductionModuleUnit d V).app M).app (op n)))) := by
    have := stratumModuleUnit_epi d V M n
    infer_instance
  apply (cancel_epi ((reductionRestrict U (exchangeScalar d U)).map
    ((stratumModulePull d u).map (((completedReductionModuleUnit d V).app M).app (op n))))).1
  have hs := congrArg (fun k ↦ k.app (op n))
    ((stratumModuleReductionIso_exists d u).exists.choose_spec M)
  dsimp only [NatTrans.comp_app] at hs
  have hc : ((d.constantPullbackIso u).hom.app M).app (op n) = 𝟙 _ := rfl
  erw [hc, Category.id_comp] at hs
  have hρU := ordinaryAugmentation_ordinaryRho d U ((stratumModulePull d u).obj M) n
  have hρV := ordinaryAugmentation_ordinaryRho d V M n
  have hρU' : (reductionRestrict U (exchangeScalar d U)).map
      (((completedReductionModuleUnit d U).app ((stratumModulePull d u).obj M)).app (op n)) ≫
      ((ordinaryRho d U).inv.app ((stratumModulePull d u).obj M)).app (op n) =
      ((ordinaryAugmentation d U).app ((reductionRestrict U (exchangeScalar d U)).obj
        ((stratumModulePull d u).obj M))).app (op n) := by
    rw [← hρU, Category.assoc, Iso.hom_inv_id_app_app]
    erw [Category.comp_id]
  have hρV' : (reductionRestrict V (exchangeScalar d V)).map
      (((completedReductionModuleUnit d V).app M).app (op n)) ≫
      ((ordinaryRho d V).inv.app M).app (op n) =
      ((ordinaryAugmentation d V).app ((reductionRestrict V (exchangeScalar d V)).obj M)).app
        (op n) := by
    rw [← hρV, Category.assoc, Iso.hom_inv_id_app_app]
    erw [Category.comp_id]
  have hA := congrArg (fun k ↦ k.app (op n))
    ((ordinaryAugmentation d U).naturality ((exchangeOrdinaryResPull d u).hom.app M))
  dsimp only [NatTrans.comp_app] at hA
  have hE := (exchangeOrdinaryResPull d u).hom.naturality
    (((completedReductionModuleUnit d V).app M).app (op n))
  dsimp only [Functor.comp_map] at hE
  have hO := ordinaryAugmentation_ordinaryReductionPullIso d u
    ((reductionRestrict V (exchangeScalar d V)).obj M) n
  rw [← Functor.map_comp_assoc]
  erw [hs]
  rw [reassoc_of% hρU']
  erw [← hA, reassoc_of% hE]
  rw [← Functor.map_comp_assoc]
  erw [hρV', hO]
  rfl

/-- The universal counit of the constant reduction is natural in chain maps. -/
theorem reductionComplexCounit_naturality (T : Scheme.{t})
    {K K' : CochainComplex (reductionModules T (exchangeConstantRing T A)) ℤ} (φ : K ⟶ K') :
    (reduction d T).map (DerivedCategory.Q.map φ) ≫ reductionComplexCounit d T K' =
      reductionComplexCounit d T K ≫
        DerivedCategory.Q.map (((reductionModule d T).mapHomologicalComplex (.up ℤ)).map φ) := by
  exact complexCounit_naturality (reductionData d T) φ

section DerivedPull

private theorem orderedAbSheafify' (T : Scheme.{t}) :
    HasSheafify (ProEt.topology T) AddCommGrpCat.{t + 1} :=
  WeilConjectures.integralCoefficientAbSheafify.{t, 0} T

private theorem orderedAbLocallyBijective' (T : Scheme.{t}) :
    (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{t + 1} :=
  WeilConjectures.integralCoefficientAbLocallyBijective.{t, 0} T


private theorem scalarFlat (T : Scheme.{t}) :
    SheafOfModules.IsFlatOnSite.{t + 1, t, t + 1, t + 1}
      ((SheafOfModules.restrictScalars ((adicLisseForget T).map (exchangeScalar d T))).obj
        (SheafOfModules.unit ((adicLisseForget T).obj (d.completedRing T)))) := by
  let := d.noetherian
  have hc : ∀ n : ℕ, exchangeScalar d T ≫ (pbcCompletedComparison T d).inv ≫
      limit.π (adicLisseRingSystem T d.ideal) (op n) =
        (constantSheaf (ProEt.topology T) CommRingCat.{t + 1}).map
          (CommRingCat.ofHom (Ideal.Quotient.mk (d.ideal ^ (n + 1)))) := by
    intro n
    dsimp only [exchangeScalar]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    exact (adicDatumScalar_exists T
      { toCompleteCoefficientDatum := d.toCompleteCoefficientDatum,
        quotientFinite := d.quotientFinite }).exists.choose_spec n
  exact (completed_constant_algebra_flat_quotients T d.ideal _
    (pbcCompletedComparison T d) (exchangeScalar d T) hc).1

/-- Pullback with the completed coefficient transport preserves flat-term K-flat complexes. -/
private theorem stratumPull_flatKFlat' {U V : Scheme.{t}} (u : U ⟶ V)
    (P : CochainComplex (reductionModules V (d.completedRing V)) ℤ)
    (hP : P.IsKFlatIndependentCoefficients)
    (hflat : ∀ n, SheafOfModules.IsFlatOnSite (J := ProEt.topology V)
        (R := d.completedRing V) (P.X n)) :
    CochainComplex.IsKFlatIndependentCoefficients (R := d.completedRing U)
      (((stratumModulePull d u).mapHomologicalComplex (.up ℤ)).obj P) ∧
    ∀ n, SheafOfModules.IsFlatOnSite (J := ProEt.topology U) (R := d.completedRing U)
      ((((stratumModulePull d u).mapHomologicalComplex (.up ℤ)).obj P).X n) := by
  obtain ⟨I, hI⟩ := proEtaleAlgebraicInverseImage_exists u (d.completedRing V)
  rcases I with ⟨r, ra, rm, rz, ro, L, e, ea, ez, es⟩
  dsimp only at hI
  subst L
  let I : SheafOfModules.AlgebraicInverseImage
      (proEtaleSheafInverseImage u (Type (t + 1))) (d.completedRing V)
      ((proEtaleSheafInverseImage u CommRingCat.{t + 1}).obj (d.completedRing V)) :=
    ⟨r, ra, rm, rz, ro, proEtaleModuleInverseImage u (d.completedRing V), e, ea, ez, es⟩
  have : PreservesFiniteLimits (proEtaleSheafInverseImage u (Type (t + 1))) :=
    (AlgebraicGeometry.ProEtale.toposFunctorialityInverseImage u (𝟙 V)).2.2.2.1
  have hobj (M) : (stratumModulePull d u).obj M =
      SheafOfModules.changeOfRings.{t, t + 1, t + 1}
        (d.integralRingIso u).hom (I.modules.obj M) := rfl
  have hmap : ∀ {M N} (g : M ⟶ N), (stratumModulePull d u).map g =
      eqToHom (hobj M) ≫
        SheafOfModules.changeOfRingsHom.{t, t + 1, t + 1} (d.integralRingIso u).hom
          (I.modules.obj M) (I.modules.map g) ≫ eqToHom (hobj N).symm := by
    intro M N g
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
  exact SheafOfModules.isKFlat_ringedToposPullback
    (proEtaleSheafInverseImage u (Type (t + 1)))
    (proEtaleSheafDirectImage u (Type (t + 1)))
    (proEtaleSheafAdjunction u (Type (t + 1))) I (d.integralRingIso u).hom
    (stratumModulePull d u) hobj hmap P hP hflat

end DerivedPull

end OrdinaryPull

/-- Restriction of the strict reduction comparison `rho` is compatible with pullback.
Source: Stacks 099M, 0D6D (blueprint: def-weil-pbc-ordered-coefficient-comparison-data).
Proof plan (ordinary core `ordinaryRho_pull` is proved above): reduce to `Q L` for a
flat-term K-flat `L`; postcompose with the invertible map
`red(pull(resF L)) ≫ red(pullF(res L)) ≫ reductionComplexCounit`; expand both sides by
`RhoNormalization` (at `L` and at `pull L`), `StratumReductionFormula`,
`ReductionPullNormalized`, and `mapDerivedCategorySquareIso_hom_app_Q` for `alpha` and
`exchangeResPull`; both become `Π ≫ Q.map _` with the chain maps identified by
`ordinaryRho_pull`. The chain-map identity at degree `i` and level `n` is
`ordinaryRho_pull` at `L.X i`.
Attempted: all the normalization facts elaborate, but the kernel is too slow on the
concrete derived-category terms. Measurements for the square formula at
`exchangeModuleResPull` and a tower complex `Z`:
* `have := mapDerivedCategorySquareIso_hom_app_Q (exchangeModuleResPull d u) Z` alone costs
  55-65 s of kernel time. The same statement written directly in this file costs 4 s.
* The cost is not the argument check: kernel `isDefEq` of each argument type with its
  binder type, and a separate kernel check of each argument, are all under 0.3 s. Checking
  application prefixes grows from 2 s to 10 s once the concrete `Abelian` arguments are
  supplied. A subterm drill-down finds the expensive node in the instantiated statement:
  `G₂.mapDerivedCategory.map (G₁.mapDerivedCategoryFactors.hom.app K) ≫
  G₂.mapDerivedCategoryFactors.hom.app _` takes about 5 s, while each factor is cheap.
  This suggests that matching the middle object, `(G₁.mapHomologicalComplex _ ⋙ Q).obj K`
  against `Q.obj (G₁.mapHomologicalComplex _ |>.obj K)`, unfolds the concrete
  `HasDerivedCategory.standard` instances.
* Neither of these fixes helps: `attribute [-instance] SemilinearSections.moduleAbelian
  SemilinearSections.hasDerived flatConstantModulesAbelian`, which makes the `Abelian`
  instances agree up to proofs (61 s); and also passing `pbcTowers_hasDerivedCategory` and
  `exchangeTowers_hasDerived` explicitly (107 s).
* Rerunning the square-formula tactic proof on the concrete functors makes the kernel time
  out deterministically after 350 s.
Suggested route: state the whole argument as one generic lemma, with the categories,
instances, functors and isomorphisms as variables and the normalization equations as
hypotheses. Then close this goal with a single `exact`, so that no instantiated
intermediate statement (a `have` type or a `rw` motive) is re-checked by the kernel. -/
theorem rho_reductionTowerPullbackIso {U V : Scheme.{t}} (u : U ⟶ V) (M : d.derived V) :
    (exchangeTowerRes d U).map ((d.reductionTowerPullbackIso u).hom.app M) ≫
        (rho d U).hom.app ((d.pull u).obj M) ≫
        (reduction d U).map ((alpha d u).hom.app M) =
      (exchangeResPull d u).hom.app ((completedReductionTower V d).obj M) ≫
        (exchangeConstantPull (A := A) u).map ((rho d V).hom.app M) ≫
        (reductionPullIso d u).hom.app ((res d V).obj M) := by
  sorry

/-- The adjunct of a whiskered mate: transposing `s.app M ≫ H.map t` under the second
adjunction is `G` applied to the transpose of `t`, followed by the mate. -/
private theorem mate_homEquiv
    {A' B' C' D' : Type*} [Category A'] [Category B'] [Category C'] [Category D']
    {L : A' ⥤ B'} {R : B' ⥤ A'} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    {G : A' ⥤ C'} {H : B' ⥤ D'}
    (adj : L ⊣ R) (adj' : L' ⊣ R') (s : TwoSquare G L L' H)
    (M : A') (N : B') (t : L.obj M ⟶ N) :
    adj'.homEquiv _ _ (s.app M ≫ H.map t) =
      G.map (adj.homEquiv M N t) ≫ (mateEquiv adj adj' s).app N := by
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  have hu := unit_mateEquiv adj adj' s M
  dsimp only [Functor.id_obj] at hu
  rw [← Category.assoc, ← hu, Category.assoc]
  have hn := (mateEquiv adj adj' s).natTrans.naturality t
  dsimp only [Functor.comp_map] at hn
  rw [← hn, ← Category.assoc, ← G.map_comp]

/-- The restriction/direct-image comparison of strict towers is the mate of the
restriction/pullback comparison, in adjunct form.
Source: Stacks 0D6D, 0D6E (blueprint: lem-weil-pbc-strict-tower-exchange-mate-normalization). -/
theorem exchangeResPush_homEquiv {U V : Scheme.{t}} (u : U ⟶ V)
    (Z : DerivedCategory (d.towers V)) (W : DerivedCategory (d.towers U))
    (x : (d.towerPull u).obj Z ⟶ W) :
    (exchangeTowerAdjunction u (exchangeConstantRing V A) (exchangeConstantRing U A)
        (exchangeConstantIso u A)).homEquiv _ _
        ((exchangeResPull d u).inv.app Z ≫ (exchangeTowerRes d U).map x) =
      (exchangeTowerRes d V).map ((d.towerAdjunction u).homEquiv Z W x) ≫
        (exchangeResPush d u).hom.app W := by
  have heq := exactDerivedMate_eq (d.towerModuleAdjunction u)
    (exchangeTowerModuleAdjunction u (exchangeConstantRing V A)
      (exchangeConstantRing U A) (exchangeConstantIso u A))
    (exchangeModuleResPull d u).symm (exchangeModuleResPush d u)
    (exchangeModuleResPull_mate d u) (exchangeResPush d u)
    (exchangeResPush_existsUnique d u).choose_spec.1
  rw [heq, exactDerivedMate]
  have hm := mate_homEquiv (d.towerAdjunction u)
    (exchangeTowerAdjunction u (exchangeConstantRing V A)
      (exchangeConstantRing U A) (exchangeConstantIso u A))
    (TwoSquare.mk _ _ _ _
      (Functor.mapDerivedCategorySquareIso (exchangeModuleResPull d u).symm).hom) Z W x
  have hs : (Functor.mapDerivedCategorySquareIso (exchangeModuleResPull d u).symm).hom =
      (exchangeResPull d u).inv := by
    simp only [Functor.mapDerivedCategorySquareIso, exchangeResPull, Iso.trans_hom,
      Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, Category.assoc,
      Functor.mapDerivedCategoryNatIso_symm]
  rw [hs] at hm ⊢
  exact hm

/-- Restriction of the integral derived counit is the constant derived counit, conjugated by
`alpha` and `chi`. Source: Stacks 0D6D, 0D6E
(blueprint: lem-weil-pbc-ring-sheaf-change-adjunction). -/
theorem res_counit {U V : Scheme.{t}} (u : U ⟶ V) (K : d.derived U) :
    (res d U).map ((proEtaleRingDerivedAdjunction u (d.completedRing V) (d.completedRing U)
        (d.integralRingIso u)).counit.app K) =
      (alpha d u).hom.app ((d.push u).obj K) ≫ (pull (A := A) u).map ((chi d u).hom.app K) ≫
        (proEtaleRingDerivedAdjunction u (exchangeConstantRing V A) (exchangeConstantRing U A)
          (exchangeConstantIso u A)).counit.app ((res d U).obj K) := by
  let aS := proEtaleRingDerivedAdjunction u (d.completedRing V) (d.completedRing U)
    (d.integralRingIso u)
  let aR := proEtaleRingDerivedAdjunction u (exchangeConstantRing V A)
    (exchangeConstantRing U A) (exchangeConstantIso u A)
  have h := (proEtaleRingSheafChangeAdjunction u (exchangeConstantRing V A) (d.completedRing V)
    (exchangeConstantRing U A) (d.completedRing U) (exchangeScalar d V) (exchangeScalar d U)
    (exchangeConstantIso u A) (d.integralRingIso u) (exchangeScalar_comm d u)).2.2
      ((d.push u).obj K) K (aS.counit.app K)
  have h1 : aS.homEquiv ((d.push u).obj K) K (aS.counit.app K) = 𝟙 _ := by
    rw [Adjunction.homEquiv_unit]
    exact aS.right_triangle_components K
  erw [h1] at h
  erw [CategoryTheory.Functor.map_id, Category.id_comp] at h
  have h2 := congrArg (aR.homEquiv _ _).symm h
  rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit] at h2
  have h3 : (alpha d u).inv.app ((d.push u).obj K) ≫ (res d U).map (aS.counit.app K) =
      (pull (A := A) u).map ((chi d u).hom.app K) ≫ aR.counit.app ((res d U).obj K) := h2
  calc (res d U).map (aS.counit.app K)
      = (alpha d u).hom.app ((d.push u).obj K) ≫
          ((alpha d u).inv.app ((d.push u).obj K) ≫ (res d U).map (aS.counit.app K)) := by
        rw [Iso.hom_inv_id_app_assoc]
    _ = _ := by rw [h3]

/-- Restriction of the strict reduction comparison `rho` is compatible with the strict
projection formula maps. Source: Stacks 099M, 0D6E
(blueprint: def-weil-pbc-ordered-coefficient-comparison-data). -/
theorem rho_towerProjection {U V : Scheme.{t}} (u : U ⟶ V) (K : d.derived U) :
    (exchangeTowerRes d V).map (d.towerProjection u K) ≫
        (exchangeResPush d u).hom.app ((completedReductionTower U d).obj K) ≫
        (exchangeConstantPush (A := A) u).map ((rho d U).hom.app K) =
      (rho d V).hom.app ((d.push u).obj K) ≫
        (reduction d V).map ((chi d u).hom.app K) ≫
        projection d u ((res d U).obj K) := by
  have hP := rho_reductionTowerPullbackIso d u ((d.push u).obj K)
  have hc := res_counit d u K
  have hres := exchangeResPush_homEquiv d u
    ((completedReductionTower V d).obj ((d.push u).obj K)) ((completedReductionTower U d).obj K)
    ((d.reductionTowerPullbackIso u).hom.app ((d.push u).obj K) ≫
      (completedReductionTower U d).map ((proEtaleRingDerivedAdjunction u (d.completedRing V)
        (d.completedRing U) (d.integralRingIso u)).counit.app K))
  have hn := (rho d U).hom.naturality ((proEtaleRingDerivedAdjunction u (d.completedRing V)
    (d.completedRing U) (d.integralRingIso u)).counit.app K)
  have hR := (reductionPullIso d u).hom.naturality ((chi d u).hom.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn hR
  have hP' : (exchangeResPull d u).inv.app ((completedReductionTower V d).obj ((d.push u).obj K)) ≫
      (exchangeTowerRes d U).map ((d.reductionTowerPullbackIso u).hom.app ((d.push u).obj K)) ≫
      (rho d U).hom.app ((d.pull u).obj ((d.push u).obj K)) ≫
      (reduction d U).map ((alpha d u).hom.app ((d.push u).obj K)) =
    (exchangeConstantPull (A := A) u).map ((rho d V).hom.app ((d.push u).obj K)) ≫
      (reductionPullIso d u).hom.app ((res d V).obj ((d.push u).obj K)) := by
    rw [hP, Iso.inv_hom_id_app_assoc]
  unfold AdicCoefficientDatum.towerProjection projection
  rw [← reassoc_of% hres, ← Adjunction.homEquiv_naturality_right]
  erw [← Adjunction.homEquiv_naturality_left, ← Adjunction.homEquiv_naturality_left]
  apply congrArg
  simp only [Functor.map_comp, Category.assoc]
  erw [hn]
  rw [hc]
  simp only [Functor.map_comp]
  rw [reassoc_of% hP']
  erw [reassoc_of% hR]

/-- The second strict coefficient equation: restriction of the strict realization `H`
followed by `beta` is `rhoM` followed by the constant `H`.
Source: Stacks 099M, 0D6D, 0D6E
(blueprint: lem-weil-pbc-ordered-strict-coefficient-equations). -/
theorem exchangeRealizationH_beta (K : d.derived X) :
    (exchangeTowerRes d Y').map (exchangeRealizationH (f := f) (g := g) d K).hom ≫
        (beta (f := f) (g := g) d K).hom =
      (rhoM (f := f) (g := g) d K).hom ≫ (H (f := f) (g := g) d ((res d X).obj K)).hom := by
  let M := (d.push f).obj K
  have hP := rho_reductionTowerPullbackIso d g M
  have hQ := rho_towerProjection d f K
  have hP' : (exchangeResPull d g).hom.app ((completedReductionTower Y d).obj M) ≫
      (exchangeConstantPull (A := A) g).map ((rho d Y).hom.app M) =
    (exchangeTowerRes d Y').map ((d.reductionTowerPullbackIso g).hom.app M) ≫
      (rho d Y').hom.app ((d.pull g).obj M) ≫
      (reduction d Y').map ((alpha d g).hom.app M) ≫
      (reductionPullIso d g).inv.app ((res d Y).obj M) := by
    rw [reassoc_of% hP, Iso.hom_inv_id_app]
    erw [Category.comp_id]
  have hN := (exchangeResPull d g).hom.naturality (d.towerProjection f K)
  have hR := (reductionPullIso d g).inv.naturality ((chi d f).hom.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hN hR
  simp only [exchangeRealizationH, beta, rhoM, H, exchangeCornerB, Iso.trans_hom, Iso.symm_hom,
    Iso.app_hom, Functor.mapIso_hom, asIso_hom, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.map_comp, Category.id_comp, Category.comp_id, Category.assoc]
  rw [reassoc_of% hN]
  rw [← Functor.map_comp, ← Functor.map_comp, hQ]
  simp only [Functor.map_comp]
  rw [reassoc_of% hP', ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  rw [reassoc_of% hR]

/-- The third strict coefficient equation: restriction of the strict exchange `towerV'`
is the constant strict tower mate, conjugated by `beta` and `delta`.
Source: Stacks 099M, 0E48 (blueprint: lem-weil-pbc-ordered-strict-coefficient-equations).
Needs, beyond `rho_reductionTowerPullbackIso` and `rho_towerProjection`, the compatibility of
restriction with the ambient exchange `integralExchange` (via `alpha`, `chi` and the
composite pullback isomorphisms); not attempted in detail. -/
theorem towerV'_delta (sq : ChosenCartesianSquare g' f' f g) (K : d.derived X) :
    (exchangeTowerRes d Y').map (d.towerV' sq K) ≫ (delta (f' := f') (g' := g') d K).hom =
      (beta (f := f) (g := g) d K).hom ≫
        (exchangeConstantSquare (A := A) sq).exchangeTowerMate.app
          ((reduction d X).obj ((res d X).obj K)) := by
  sorry

set_option linter.unusedVariables false in
/-- strictCoefficientEquations: the indicated part of the ordered comparison argument.
Source: blueprint completed-exchange-coherence, second proof paragraph;
Stacks Tags 099M, 099N, 0A07 and 0E48.
(blueprint: lem-weil-pbc-ordered-strict-coefficient-equations).
Proof: the diagonal exact-adjunction comparison identifies the completed strict
exchange with the reduction of the ambient mate. The perfect quotient projection
maps are invertible, so conjugating gives the first formula. For the second,
transpose the projection formula map under the ordinary ringed adjunction.
Restriction identifies its counit with the constant counit, and quotient balancing
sends each pure tensor to the same tensor. Apply the derived pullback and tensor
comparison to this equation on the single strict quotient diagram. Tensor descent
makes it an equality of derived tower morphisms. For the third, transpose the
restricted strict exchange under the constant tower adjunction. Scalar restriction
identifies both units and counits, and coefficient inverse image respects
composition. The transpose is therefore the transpose defining the constant mate.
Bijectivity of the adjunction correspondence gives the equation. Naturality for
rho then gives exactly beta and delta at the reduced complete input. No claim of
faithfulness of derived evaluation functors is used. -/
theorem strictCoefficientEquations (sq : ChosenCartesianSquare g' f' f g) :
    ∀ (K : d.derived X) (hK : d.TowerComplete X K),
      (d.towerV' sq K =
        (exchangeRealizationH (f := f) (g := g) d K).inv ≫
          (completedReductionTower Y' d).map ((d.integralExchange sq).app K) ≫
          (exchangeRealizationHPrime (f' := f') (g' := g') d K).hom) ∧
      ((exchangeTowerRes d Y').map
          (exchangeRealizationH (f := f) (g := g) d K).hom ≫
            (beta (f := f) (g := g) d K).hom =
        (rhoM (f := f) (g := g) d K).hom ≫
          (H (f := f) (g := g) d ((res d X).obj K)).hom) ∧
      ((exchangeTowerRes d Y').map (d.towerV' sq K) ≫
          (delta (f' := f') (g' := g') d K).hom =
        (beta (f := f) (g := g) d K).hom ≫
          (exchangeConstantSquare (A := A) sq).exchangeTowerMate.app
            ((reduction d X).obj ((res d X).obj K))) := by
  intro K _
  refine ⟨?_, exchangeRealizationH_beta d K, towerV'_delta d sq K⟩
  simp only [AdicCoefficientDatum.towerV', AdicCoefficientDatum.towerV,
    exchangeRealizationH, exchangeRealizationHPrime, AdicCoefficientDatum.towerH,
    AdicCoefficientDatum.towerH', Iso.trans_inv, Iso.trans_hom,
    Category.assoc]
  rfl

end AlgebraicGeometry.Scheme.OrderedExchange
