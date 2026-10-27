/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N8
-/
module

public import Sheaf.Paper.ProEtaleConstantReductionTower
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
import all Sheaf.Paper.StrictTowerExchangeMateNormalization
import all Sheaf.CategoryTheory.FlatScalarTowerLimitSquare

/-! # Coefficient normalization of the raw ordered completed exchange

Source: main-20261015 blueprint, proper base change, completed-exchange-coherence,
second proof paragraph; strict coefficient supplement, Stacks Tags 099M, 099N,
0A07 and 0E48 (blueprint: def-weil-pbc-ordered-coefficient-comparison-data).

The maps below retain their ordinary-section, universal-derived-counit and completion-unit
normalizations. The ambient constant and completed module categories remain distinct.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.OrderedExchange

-- Prefer the concrete pro-etale site and module instances to abstract corner projections.
attribute [local instance 0] SheafOfModules.RingedTensorCorner.category
  SheafOfModules.RingedTensorCorner.derived

private theorem orderedAbSheafify (T : Scheme.{t}) :
    HasSheafify (ProEt.topology T) AddCommGrpCat.{t + 1} :=
  WeilConjectures.integralCoefficientAbSheafify.{t, 0} T

private theorem orderedAbLocallyBijective (T : Scheme.{t}) :
    (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{t + 1} :=
  WeilConjectures.integralCoefficientAbLocallyBijective.{t, 0} T


set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem orderedRestrictLimits (T : Scheme.{t})
    {R B : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ B) :
    PreservesLimitsOfShape ℕᵒᵖ (reductionRestrict T φ) := by
  let := orderedAbSheafify T
  let := orderedAbLocallyBijective T
  let r := reductionRestrict T φ
  let F := SheafOfModules.forget.{t + 1} (reductionModuleRing T R) ⋙
    PresheafOfModules.toPresheaf (reductionModuleRing T R).obj
  let e : SheafOfModules.forget.{t + 1} (reductionModuleRing T B) ⋙
      PresheafOfModules.toPresheaf (reductionModuleRing T B).obj ≅ r ⋙ F := Iso.refl _
  have : PreservesLimitsOfShape ℕᵒᵖ (r ⋙ F) :=
    preservesLimitsOfShape_of_natIso e
  have : ReflectsLimitsOfShape ℕᵒᵖ F := reflectsLimitsOfShape_of_reflectsIsomorphisms
  exact preservesLimitsOfShape_of_reflects_of_preserves r F

set_option backward.isDefEq.respectTransparency.types true in
private theorem uniqueLimitComparison {C E : Type*} [Category C] [Category E]
    [HasLimitsOfShape ℕᵒᵖ C] [HasLimitsOfShape ℕᵒᵖ E]
    (r : C ⥤ E) [PreservesLimitsOfShape ℕᵒᵖ r] :
    ∃! e : lim ⋙ r ≅ (Functor.whiskeringRight ℕᵒᵖ C E).obj r ⋙ lim,
      ∀ (Z : ℕᵒᵖ ⥤ C) (n : ℕ),
        e.hom.app Z ≫ limit.π (Z ⋙ r) (op n) = r.map (limit.π Z (op n)) := by
  refine ⟨preservesLimitNatIso (J := ℕᵒᵖ) r, ?_, ?_⟩
  · intro Z n
    exact preservesLimitIso_hom_π r Z (op n)
  · intro e he
    apply Iso.ext
    apply NatTrans.ext
    funext Z
    apply limit.hom_ext
    intro n
    exact (he Z n.unop).trans (preservesLimitIso_hom_π r Z n).symm

private theorem unitIsoComparison {C : Type*} [Category C] {M N M' N' : C}
    (j : M ⟶ N) (j' : M' ⟶ N') (a : M ≅ M') (p : N ≅ N')
    (h : j ≫ p.hom = a.hom ≫ j') : j' ≫ p.inv = a.inv ≫ j :=
  a.eq_inv_comp.mpr
    ((Category.assoc a.hom j' p.inv).symm.trans (p.comp_inv_eq.mpr h.symm))

private theorem mappedUnitIsoComparison {C E : Type*} [Category C] [Category E]
    (r : C ⥤ E) {M N Z : C} {M' N' : E}
    (j : M ⟶ N) (j' : M' ⟶ N') (a : r.obj M ≅ M') (p : r.obj N ≅ N')
    (h : r.map j ≫ p.hom = a.hom ≫ j') (f : N ⟶ Z) :
    j' ≫ p.inv ≫ r.map f = a.inv ≫ r.map (j ≫ f) := by
  rw [← Category.assoc, unitIsoComparison _ _ a p h,
    Category.assoc, Functor.map_comp]

attribute [local irreducible] completedAdicChangeData completedAdicDerivedChange
  HasDerivedCategory.standard Functor.mapDerivedCategory
  Functor.mapDerivedCategoryFactors Functor.mapDerivedCategoryFactorsh
  completedAdicChange reductionChange reductionDerivedChange reductionHomotopy
  completedReductionTower reduction

attribute [local instance 3000] orderedAbSheafify orderedAbLocallyBijective
  reductionModulesHasDerivedCategory reductionTowerHasDerivedCategory
  reductionRingModulesHasDerivedCategory

-- Normalize the two ordinary presentations of scalar restriction before matching complexes.
set_option allowUnsafeReducibility true in
attribute [local reducible] reductionRestrict completedReductionComplexTowerFunctor

variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)

/-- Derived restriction along the existing compatible-residue coefficient map.
Source: Stacks 099M (blueprint: def-weil-pbc-ordered-coefficient-comparison-data). -/
abbrev res (T : Scheme.{t}) := reductionDerivedRestrict T (exchangeScalar d T)

/-- The canonical balancing isomorphism on the single ordinary strict quotient diagram.
Source: Stacks 099M (blueprint: def-weil-pbc-ordered-coefficient-comparison-data).
Proof: flatness of the completed ring over the constant ring identifies its finite
quotients with the specified finite constant sheaves. On pure tensors the comparison
sends s tensor x to s tensor x. Balancing and sheafification make this an isomorphism,
natural in modules and quotient coefficients. The section formulas specify it uniquely
and ensure compatibility with all quotient transitions, including identity transitions. -/
theorem ordinaryRho_existsUnique (T : Scheme.{t}) :
    ∃! e : reductionRestrict T (exchangeScalar d T) ⋙ reductionModule d T ≅
        completedReductionModuleTowerFunctor T d ⋙ exchangeTowerModuleRes d T,
      ∀ (M : reductionModules T (d.completedRing T)) (n : ℕ) (U : T.ProEtᵒᵖ)
        (s : (d.finiteRing T n).obj.obj U) (x : M.val.obj U),
        ((e.hom.app M).app (op n)).val.app U
            (reductionTensorSection T (quotient d T n)
              ((reductionRestrict T (exchangeScalar d T)).obj M) U s x) =
          reductionTensorSection T (d.projection T n) M U s x := by
  sorry

/-- Ordinary strict balancing, with its prescribed tensor normalization.
Source: Stacks 099M (blueprint: def-weil-pbc-ordered-coefficient-comparison-data). -/
def ordinaryRho (T : Scheme.{t}) :
    reductionRestrict T (exchangeScalar d T) ⋙ reductionModule d T ≅
      completedReductionModuleTowerFunctor T d ⋙ exchangeTowerModuleRes d T :=
  (ordinaryRho_existsUnique d T).exists.choose

attribute [local irreducible] ordinaryRho reductionModule completedReductionModuleTowerFunctor
  completedReductionCoefficient constantSheaf AdicCoefficients.coefficientRing
  SheafOfModules.monoidalCategory

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The complex-level normalization of the specified rho comparison.
Source: Stacks 099M, 06YY
(blueprint: def-weil-pbc-ordered-coefficient-comparison-data). -/
def RhoNormalization (T : Scheme.{t})
    (e : completedReductionTower T d ⋙ exchangeTowerRes d T ≅
        res d T ⋙ reduction d T) : Prop :=
  ∀ P : CochainComplex (reductionModules T (d.completedRing T)) ℤ,
        CochainComplex.IsKFlatIndependentCoefficients.{t + 1, t, t + 1}
          (R := d.completedRing T) P →
        (∀ n : ℤ, SheafOfModules.IsFlatOnSite.{t + 1, t, t + 1, t + 1}
          (R := d.completedRing T) (P.X n)) →
        e.hom.app (DerivedCategory.Q.obj P) ≫
            (reduction d T).map
              ((reductionRestrict T (exchangeScalar d T)).mapDerivedCategoryFactors.hom.app P) ≫
            reductionComplexCounit d T
              (((reductionRestrict T (exchangeScalar d T)).mapHomologicalComplex (.up ℤ)).obj P) =
          (exchangeTowerRes d T).map (completedReductionTowerComplexCounit T d P) ≫
            (exchangeTowerModuleRes d T).mapDerivedCategoryFactors.hom.app
              ((completedReductionComplexTowerFunctor T d).obj P) ≫
            DerivedCategory.Q.map
              ((NatIso.mapHomologicalComplex (ordinaryRho d T).symm (.up ℤ)).hom.app P)

attribute [local irreducible] RhoNormalization

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The derived strict-tower comparison is fixed on K-flat representatives before evaluation.
Source: Stacks 099M, 06YY
(blueprint: def-weil-pbc-ordered-coefficient-comparison-data).
Proof: flatness makes restriction preserve flat-term K-flat representatives. Apply
ordinaryRho to one such representative and conjugate by the two universal reduction
counits and exact-restriction factorization maps. The formula descends through resolving
quasi-isomorphisms, giving the isomorphism. Every derived object has a representative
of this kind, so the formula determines the natural isomorphism uniquely. -/
theorem rho_existsUnique (T : Scheme.{t}) :
    ∃! e : completedReductionTower T d ⋙ exchangeTowerRes d T ≅
        res d T ⋙ reduction d T,
      RhoNormalization d T e := by
  sorry

/-- The specified comparison rho, natural on all ambient inputs.
Source: Stacks 099M (blueprint: def-weil-pbc-ordered-coefficient-comparison-data). -/
def rho (T : Scheme.{t}) :
    completedReductionTower T d ⋙ exchangeTowerRes d T ≅ res d T ⋙ reduction d T :=
  (rho_existsUnique d T).exists.choose

/-- The chosen rho retains its complex-level normalization.
Source: Stacks 099M, 06YY
(blueprint: def-weil-pbc-ordered-coefficient-comparison-data).
Proof: use the existence clause of the unique normalized comparison. -/
theorem rho_normalization (T : Scheme.{t}) : RhoNormalization d T (rho d T) :=
  (rho_existsUnique d T).exists.choose_spec

/-- The actual ordinary limit/scalar comparison, fixed by all its projections.
Source: Stacks 0A07 (blueprint: def-weil-pbc-ordered-coefficient-comparison-data).
Proof: restriction leaves the underlying additive sheaf unchanged. Its right-adjoint
limit comparison is the identity on compatible families. Every projection commutes
with it, giving its inverse and uniqueness by the limit universal property. -/
theorem ordinaryLambda_existsUnique (T : Scheme.{t}) :
    ∃! e : completedTowerLimit T (d.completedRing T) ⋙
          reductionRestrict T (exchangeScalar d T) ≅
        exchangeTowerModuleRes d T ⋙ completedTowerLimit T (exchangeConstantRing T A),
      ∀ (Z : d.towers T) (n : ℕ),
        e.hom.app Z ≫ limit.π ((exchangeTowerModuleRes d T).obj Z) (op n) =
          (reductionRestrict T (exchangeScalar d T)).map (limit.π Z (op n)) := by
  let := orderedAbSheafify T
  let := orderedAbLocallyBijective T
  have := orderedRestrictLimits T (exchangeScalar d T)
  exact uniqueLimitComparison (reductionRestrict T (exchangeScalar d T))

/-- The identity on compatible families, with its projection equations retained.
Source: Stacks 0A07 (blueprint: def-weil-pbc-ordered-coefficient-comparison-data). -/
def ordinaryLambda (T : Scheme.{t}) :
    completedTowerLimit T (d.completedRing T) ⋙ reductionRestrict T (exchangeScalar d T) ≅
      exchangeTowerModuleRes d T ⋙ completedTowerLimit T (exchangeConstantRing T A) :=
  (ordinaryLambda_existsUnique d T).exists.choose

attribute [local irreducible] ordinaryLambda Functor.rightDerivedFunctor
  Functor.rightDerivedFunctorUnit

/-- The universal right-derived limit unit at a cochain complex.
Source: Stacks 0A07 (blueprint: def-weil-pbc-ordered-coefficient-comparison-data). -/
def limitComplexUnit (T : Scheme.{t})
    (R : Sheaf (ProEt.topology T) CommRingCat.{t + 1})
    (P : CochainComplex (exchangeTowers T R) ℤ) :
    DerivedCategory.Q.obj
        (((completedTowerLimit T R).mapHomologicalComplex (.up ℤ)).obj P) ⟶
      (completedRlim T R).obj (DerivedCategory.Q.obj P) :=
  (DerivedCategory.quotientCompQhIso _).inv.app
      (((completedTowerLimit T R).mapHomologicalComplex (.up ℤ)).obj P) ≫
    DerivedCategory.Qh.map
      (((completedTowerLimit T R).mapHomotopyCategoryFactors (.up ℤ)).inv.app P) ≫
    (completedTowerLimit T R).rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ _).obj P) ≫
    (completedRlim T R).map ((DerivedCategory.quotientCompQhIso _).hom.app P)

attribute [local irreducible] limitComplexUnit

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The complex-level normalization of the specified lambda comparison.
Source: Stacks 0A07
(blueprint: def-weil-pbc-ordered-coefficient-comparison-data). -/
def LambdaNormalization (T : Scheme.{t})
    (e : completedRlim T (d.completedRing T) ⋙ res d T ≅
        exchangeTowerRes d T ⋙ rlim (A := A) T) : Prop :=
  ∀ P : CochainComplex (d.towers T) ℤ,
        (res d T).map (limitComplexUnit T (d.completedRing T) P) ≫
            e.hom.app (DerivedCategory.Q.obj P) ≫
            (rlim (A := A) T).map
              ((exchangeTowerModuleRes d T).mapDerivedCategoryFactors.hom.app P) =
          (reductionRestrict T (exchangeScalar d T)).mapDerivedCategoryFactors.hom.app
              (((completedTowerLimit T (d.completedRing T)).mapHomologicalComplex (.up ℤ)).obj P) ≫
            DerivedCategory.Q.map
              ((NatIso.mapHomologicalComplex (ordinaryLambda d T) (.up ℤ)).hom.app P) ≫
            limitComplexUnit T (exchangeConstantRing T A)
              (((exchangeTowerModuleRes d T).mapHomologicalComplex (.up ℤ)).obj P)

attribute [local irreducible] LambdaNormalization

attribute [local irreducible] SheafOfModules.fullyFaithfulForget
  SheafOfModules.instAddCommGroupHom

private def orderedDerivedComplexUnit
    {C E : Type*} [Category C] [Category E] [Abelian C] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory E]
    [Abelian.HasKInjectiveResolutions C] (F : C ⥤ E) [F.Additive] :
    F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ F.rightDerivedFunctor :=
  Functor.whiskerLeft (F.mapHomologicalComplex (.up ℤ))
      (DerivedCategory.quotientCompQhIso E).inv ≫
    Functor.whiskerRight (F.mapHomotopyCategoryFactors (.up ℤ)).inv DerivedCategory.Qh ≫
    Functor.whiskerLeft (HomotopyCategory.quotient C (.up ℤ)) F.rightDerivedFunctorUnit ≫
    Functor.whiskerRight (DerivedCategory.quotientCompQhIso C).hom F.rightDerivedFunctor

private theorem orderedDerivedComplexUnit_isIso
    {C E : Type*} [Category C] [Category E] [Abelian C] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory E]
    [Abelian.HasKInjectiveResolutions C] (F : C ⥤ E) [F.Additive]
    (P : CochainComplex C ℤ) [P.IsKInjective] :
    IsIso ((orderedDerivedComplexUnit F).app P) := by
  dsimp only [orderedDerivedComplexUnit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app]
  infer_instance

private theorem orderedScalarComparison
    {C E C' E' : Type*}
    [Category C] [Category E] [Category C'] [Category E']
    [Abelian C] [Abelian E] [Abelian C'] [Abelian E']
    [HasDerivedCategory C] [HasDerivedCategory E]
    [HasDerivedCategory C'] [HasDerivedCategory E']
    [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions C']
    (F : C ⥤ E) (F' : C' ⥤ E') (r : C' ⥤ C) (s : E' ⥤ E)
    [F.Additive] [F'.Additive] [r.Additive] [s.Additive]
    [PreservesFiniteLimits r] [PreservesFiniteColimits r]
    [PreservesFiniteLimits s] [PreservesFiniteColimits s]
    [r.PreservesKInjectiveComplexes] (c : F' ⋙ s ≅ r ⋙ F) :
    ∃! e : F'.rightDerivedFunctor ⋙ s.mapDerivedCategory ≅
        r.mapDerivedCategory ⋙ F.rightDerivedFunctor,
      ∀ P : CochainComplex C' ℤ,
        s.mapDerivedCategory.map ((orderedDerivedComplexUnit F').app P) ≫
          e.hom.app (DerivedCategory.Q.obj P) ≫
          F.rightDerivedFunctor.map (r.mapDerivedCategoryFactors.hom.app P) =
        s.mapDerivedCategoryFactors.hom.app
            ((F'.mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex c (.up ℤ)).hom.app P) ≫
          (orderedDerivedComplexUnit F).app
            ((r.mapHomologicalComplex (.up ℤ)).obj P) := by
  let a : (F' ⋙ s).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ (F'.rightDerivedFunctor ⋙ s.mapDerivedCategory) :=
    Functor.whiskerLeft (F'.mapHomologicalComplex (.up ℤ))
        s.mapDerivedCategoryFactors.inv ≫
      Functor.whiskerRight (orderedDerivedComplexUnit F') s.mapDerivedCategory
  let b : (F' ⋙ s).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ (r.mapDerivedCategory ⋙ F.rightDerivedFunctor) :=
    Functor.whiskerRight (NatIso.mapHomologicalComplex c (.up ℤ)).hom DerivedCategory.Q ≫
      Functor.whiskerLeft (r.mapHomologicalComplex (.up ℤ)) (orderedDerivedComplexUnit F) ≫
      Functor.whiskerRight r.mapDerivedCategoryFactors.inv F.rightDerivedFunctor
  obtain ⟨e, he⟩ := CategoryTheory.FlatScalarTowerLimit.normalized_iso _ _ _ a b
    (by
      intro P hP
      have := hP
      have := orderedDerivedComplexUnit_isIso F' P
      dsimp only [a, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
      infer_instance)
    (by
      intro P hP
      have := hP
      have := orderedDerivedComplexUnit_isIso F
        ((r.mapHomologicalComplex (.up ℤ)).obj P)
      dsimp only [b, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
      infer_instance)
  have hn (P : CochainComplex C' ℤ) := he P
  dsimp only [a, b, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app] at hn
  have hn' (P : CochainComplex C' ℤ) :
      s.mapDerivedCategory.map ((orderedDerivedComplexUnit F').app P) ≫
        e.hom.app (DerivedCategory.Q.obj P) ≫
        F.rightDerivedFunctor.map (r.mapDerivedCategoryFactors.hom.app P) =
      s.mapDerivedCategoryFactors.hom.app
          ((F'.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex c (.up ℤ)).hom.app P) ≫
        (orderedDerivedComplexUnit F).app
          ((r.mapHomologicalComplex (.up ℤ)).obj P) := by
    apply (cancel_epi (s.mapDerivedCategoryFactors.inv.app _)).mp
    simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
    have h := congrArg
      (fun k ↦ k ≫ F.rightDerivedFunctor.map (r.mapDerivedCategoryFactors.hom.app P)) (hn P)
    simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app] at h
    erw [F.rightDerivedFunctor.map_id, Category.comp_id] at h
    simp only [Category.assoc]
    exact h
  refine ⟨e, hn', ?_⟩
  intro e' he'
  apply Iso.ext
  apply CategoryTheory.FlatScalarTowerLimit.derived_ext
  intro P hP
  have := hP
  have := orderedDerivedComplexUnit_isIso F' P
  apply (cancel_epi (s.mapDerivedCategory.map ((orderedDerivedComplexUnit F').app P))).mp
  apply (cancel_mono (F.rightDerivedFunctor.map (r.mapDerivedCategoryFactors.hom.app P))).mp
  simpa only [Category.assoc] using (he' P).trans (hn' P).symm


attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Restriction commutes with derived strict limit on arbitrary towers, with the
K-injective comparison fixed by its ordinary compatible-family map and universal units.
Source: Stacks 0A07 (blueprint: def-weil-pbc-ordered-coefficient-comparison-data).
Proof: flat scalar extension is an exact left adjoint to restriction. Termwise
restriction therefore preserves K-injectives on the small diagram site. On a
K-injective tower, apply ordinaryLambda and the invertible derived units. This
defines a natural isomorphism. Universality extends its equation to every complex;
K-injective resolutions prove uniqueness. No finite-reduction condition is used. -/
theorem lambda_existsUnique (T : Scheme.{t}) :
    ∃! e : completedRlim T (d.completedRing T) ⋙ res d T ≅
        exchangeTowerRes d T ⋙ rlim (A := A) T,
      LambdaNormalization d T e := by
  have := exchangeTowerModuleRes_kinjective d T
  have h := orderedScalarComparison
    (completedTowerLimit T (exchangeConstantRing T A))
    (completedTowerLimit T (d.completedRing T))
    (exchangeTowerModuleRes d T) (reductionRestrict T (exchangeScalar d T))
    (ordinaryLambda d T)
  unfold LambdaNormalization
  simpa only [orderedDerivedComplexUnit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, limitComplexUnit] using h

/-- The canonical restriction/derived-limit comparison on actual strict towers.
Source: Stacks 0A07 (blueprint: def-weil-pbc-ordered-coefficient-comparison-data). -/
def lambda (T : Scheme.{t}) :
    completedRlim T (d.completedRing T) ⋙ res d T ≅ exchangeTowerRes d T ⋙ rlim (A := A) T :=
  (lambda_existsUnique d T).exists.choose

/-- The chosen lambda retains its complex-level normalization.
Source: Stacks 0A07
(blueprint: def-weil-pbc-ordered-coefficient-comparison-data).
Proof: use the existence clause of the unique normalized comparison. -/
theorem lambda_normalization (T : Scheme.{t}) : LambdaNormalization d T (lambda d T) :=
  (lambda_existsUnique d T).exists.choose_spec

variable {U V : Scheme.{t}} (u : U ⟶ V)

/-- The ambient direct-image/scalar comparison, with its universal unit normalization.
Source: Stacks 0E48 (blueprint: def-weil-pbc-ordered-coefficient-comparison-data). -/
def chi : d.push u ⋙ res d V ≅ res d U ⋙ push (A := A) u :=
  proEtaleRingRestrictionDerivedDirectImage u
    (exchangeConstantRing V A) (d.completedRing V)
    (exchangeConstantRing U A) (d.completedRing U)
    (exchangeScalar d V) (exchangeScalar d U) (exchangeConstantIso u A)
    (d.integralRingIso u) (exchangeScalar_comm d u)

/-- The ambient pullback/scalar comparison is exact descent of the ordinary normalized mate.
Source: Stacks 0D6D (blueprint: def-weil-pbc-ordered-coefficient-comparison-data). -/
def alpha : d.pull u ⋙ res d U ≅ res d V ⋙ pull (A := A) u :=
  proEtaleRingRestrictionDerivedPullback u
    (exchangeConstantRing V A) (d.completedRing V)
    (exchangeConstantRing U A) (d.completedRing U)
    (exchangeScalar d V) (exchangeScalar d U) (exchangeConstantIso u A)
    (d.integralRingIso u) (exchangeScalar_comm d u)

/-- The quotient-tower complete category over completed coefficients.
Source: Stacks 099M (blueprint: def-weil-pbc-ordered-coefficient-comparison-data). -/
abbrev AComplete (T : Scheme.{t}) := ObjectProperty.FullSubcategory (d.TowerComplete T)

/-- The inclusion of the full completed-coefficient complete category.
Source: Stacks 099M (blueprint: def-weil-pbc-ordered-coefficient-comparison-data). -/
abbrev inclusion (T : Scheme.{t}) := ObjectProperty.ι (d.TowerComplete T)

/-- Restriction identifies the two complete predicates and is an equivalence on the full
complete categories; it does not assert an ambient equivalence.
Source: Stacks 099M, 099I
(blueprint: def-weil-pbc-ordered-coefficient-comparison-data).
Proof: on the small site apply the flat ringed-ideal complete equivalence. Its finite
reduction comparison identifies the strict quotient diagrams by rho. The specified
limit comparison lambda respects quotient units. The Koszul reconstruction identifies
unit-invertibility with local derived completeness on both sides. Consequently the
ambient restriction functor, restricted to these full subcategories, is an equivalence. -/
theorem restriction_complete (T : Scheme.{t}) :
    (∀ K : d.derived T, d.TowerComplete T K ↔ IsComplete d T ((res d T).obj K)) ∧
      ∃ e : AComplete d T ≌ Complete d T,
        Nonempty (e.functor ⋙ ObjectProperty.ι (IsComplete d T) ≅
          inclusion d T ⋙ res d T) := by
  sorry

/-- The scalar comparison for completed pullback is fixed by the actual completion units.
Source: Stacks 099M, 099N
(blueprint: def-weil-pbc-ordered-coefficient-comparison-data).
Proof: completed pullback is the reflection of ordinary pullback. Restriction identifies
the complete categories and their units by rho and lambda. The ordinary comparison
alpha therefore extends uniquely across the completed pullback unit. The two hom-set
bijections give inverse extensions, so this is an isomorphism. Naturality and uniqueness
hold on the full complete category, not only on constructible or bounded objects. -/
theorem phi_existsUnique :
    ∃! e : inclusion d V ⋙ d.completedPull u ⋙ res d U ≅
        inclusion d V ⋙ res d V ⋙ completePull d u,
      ∀ K : AComplete d V,
        (res d U).map (d.ordinaryToCompleted u K.obj) ≫ e.hom.app K =
          (alpha d u).hom.app K.obj ≫
            (unit d U).app ((pull (A := A) u).obj ((res d V).obj K.obj)) := by
  sorry

/-- The completed pullback/scalar isomorphism, retaining its completion-unit equation.
Source: Stacks 099N (blueprint: def-weil-pbc-ordered-coefficient-comparison-data). -/
def phi : inclusion d V ⋙ d.completedPull u ⋙ res d U ≅
    inclusion d V ⋙ res d V ⋙ completePull d u := (phi_existsUnique d u).exists.choose


variable {X' X Y' Y : Scheme.{t}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- The specified completed-coefficient source reconstruction.
Source: Stacks 099M (blueprint: def-weil-pbc-ordered-coefficient-comparison-data). -/
def sourceReconstruction (K : d.derived X) :=
  (completedRlim Y' (d.completedRing Y')).mapIso
    ((d.reductionTowerPullbackIso g).app ((d.push f).obj K))

/-- The source comparison s a is exactly the ordered projection-formula comparison.
Source: blueprint completed-exchange-coherence, paragraph 2
(blueprint: def-weil-pbc-ordered-coefficient-comparison-data). -/
def sourceA (K : d.derived X) :=
  (completedRlim Y' (d.completedRing Y')).mapIso
    (d.towerH (f := f) (f' := f') (g := g) (g' := g') K)

/-- The specified direct-image/limit comparison c a.
Source: Stacks 0A07 (blueprint: def-weil-pbc-ordered-coefficient-comparison-data). -/
def targetA (K : d.derived X) :=
  (d.directImageRlimIso f').app
    ((d.towerPull g').obj ((completedReductionTower X d).obj K))

/-- The left corner comparison includes the image of the same strict reduction rho.
Source: Stacks 0E48 (blueprint: def-weil-pbc-ordered-coefficient-comparison-data). -/
def beta (K : d.derived X) :=
  (exchangeCornerB d f g).app ((completedReductionTower X d).obj K) ≪≫
    (exchangeConstantPull (A := A) g).mapIso
      ((exchangeConstantPush (A := A) f).mapIso ((rho d X).app K))

/-- The right corner comparison includes the image of that same strict reduction rho.
Source: Stacks 0E48 (blueprint: def-weil-pbc-ordered-coefficient-comparison-data). -/
def delta (K : d.derived X) :=
  (exchangeCornerD d g' f').app ((completedReductionTower X d).obj K) ≪≫
    (exchangeConstantPush (A := A) f').mapIso
      ((exchangeConstantPull (A := A) g').mapIso ((rho d X).app K))

/-- The scalar comparison at M uses finite reduction, ordinary pullback and chi f.
Source: Stacks 099M, 0E48
(blueprint: def-weil-pbc-ordered-coefficient-comparison-data). -/
def rhoM (K : d.derived X) :=
  (rho d Y').app ((d.pull g).obj ((d.push f).obj K)) ≪≫
    (reduction d Y').mapIso ((alpha d g).app ((d.push f).obj K)) ≪≫
    (reduction d Y').mapIso ((pull (A := A) g).mapIso ((chi d f).app K))

/-- The pulled-back strict reduction comparison retains its full diagram, not just levels.
Source: Stacks 099M, 0E48
(blueprint: def-weil-pbc-ordered-coefficient-comparison-data). -/
def rhoPull (K : d.derived X) :=
  (exchangeResPull d g').app ((completedReductionTower X d).obj K) ≪≫
    (exchangeConstantPull (A := A) g').mapIso ((rho d X).app K)

/-- The source scalar identification, with phi evaluated at the complete direct image.
Source: Stacks 099N (blueprint: def-weil-pbc-ordered-coefficient-comparison-data). -/
def iotaS (K : d.derived X) (hK : d.TowerComplete X K) :=
  (phi d g).app ⟨(d.push f).obj K, d.push_complete f K hK⟩ ≪≫
    (completePull d g).mapIso ((chi d f).app K)

/-- The target scalar identification is chi followed by direct image of phi.
Source: Stacks 099N (blueprint: def-weil-pbc-ordered-coefficient-comparison-data). -/
def iotaT (K : d.derived X) (hK : d.TowerComplete X K) :=
  (chi d f').app ((d.completedPull g').obj K) ≪≫
    (push (A := A) f').mapIso ((phi d g').app ⟨K, hK⟩)


/-- Ordinary scalar restriction commutes with constant diagrams by identity components.
Source: Stacks 0E48 (blueprint: def-weil-pbc-ordered-coefficient-comparison-data). -/
def ordinaryScalarDiagonal (T : Scheme.{t}) :
    d.constantTower T ⋙ exchangeTowerModuleRes d T ≅
      reductionRestrict T (exchangeScalar d T) ⋙ (Functor.const ℕᵒᵖ) :=
  NatIso.ofComponents
    (fun _ ↦ NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ by simp))
    (fun _ ↦ by ext n; simp)

/-- Exact descent of the identity scalar/diagonal comparison.
Source: Stacks 0E48 (blueprint: def-weil-pbc-ordered-coefficient-comparison-data). -/
def scalarDiagonal (T : Scheme.{t}) :
    d.derivedConstantTower T ⋙ exchangeTowerRes d T ≅ res d T ⋙ diagonal (A := A) T :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (ordinaryScalarDiagonal d T) ≪≫
      Functor.mapDerivedCategoryCompIso _ _

/-- Restriction respects the strict quotient unit, not just its evaluations.
Source: Stacks 099M (blueprint: def-weil-pbc-ordered-coefficient-comparison-data).
Proof: on an ordinary flat-term K-flat model both augmentations send x to 1 tensor x
in the same strict quotient diagram. ordinaryRho preserves this formula. Descent by
the universal counits gives the first equality before derived limit. Apply lambda,
its diagonal normalization and the diagonal adjunction unit to obtain the second. -/
theorem rho_unit (T : Scheme.{t}) (K : d.derived T) :
    (exchangeTowerRes d T).map ((completedReductionAugmentation d T).app K) ≫
        (rho d T).hom.app K =
      (scalarDiagonal d T).hom.app K ≫ (augmentation d T).app ((res d T).obj K) ∧
    (res d T).map (d.completionUnit T K) ≫
        (lambda d T).hom.app ((completedReductionTower T d).obj K) ≫
        (rlim (A := A) T).map ((rho d T).hom.app K) =
      (unit d T).app ((res d T).obj K) := by
  sorry

/-- The completed Hom bijections agree under chi and phi; hence so do their units,
counits and all adjunction conjugates of direct-image identity and composition.
Source: Stacks 099N, 07A6
(blueprint: def-weil-pbc-ordered-coefficient-comparison-data).
Proof: the ordinary restricted adjunction has the normalized transpose formula of
proEtaleRingSheafChangeAdjunction. Precompose with the completed pullback unit.
The defining phi equation identifies this with precomposition by the constant
completion unit. On complete targets both unit precompositions are bijective by
reflection. This proves equality of the completed Hom bijections, fixing both units
and counits. Adjunction conjugation is a bijection computed from those units and
counits. Therefore the direct-image identity and composition conjugates agree too. -/
theorem completedHom_normalization {U V : Scheme.{t}} (u : U ⟶ V)
    (K : d.derived V) (hK : d.TowerComplete V K)
    (L : d.derived U) (_hL : d.TowerComplete U L)
    (a : (d.completedPull u).obj K ⟶ L) :
    (proEtaleRingDerivedAdjunction u (exchangeConstantRing V A) (exchangeConstantRing U A)
        (exchangeConstantIso u A)).homEquiv _ _
      ((unit d U).app ((pull (A := A) u).obj ((res d V).obj K)) ≫
        (phi d u).inv.app ⟨K, hK⟩ ≫ (res d U).map a) =
      (res d V).map ((proEtaleRingDerivedAdjunction u (d.completedRing V) (d.completedRing U)
        (d.integralRingIso u)).homEquiv _ _ (d.ordinaryToCompleted u K ≫ a)) ≫
        (chi d u).hom.app L := by
  have hphi := (phi_existsUnique d u).exists.choose_spec (⟨K, hK⟩ : AComplete d V)
  change (res d U).map (d.ordinaryToCompleted u K) ≫
    (phi d u).hom.app ⟨K, hK⟩ = (alpha d u).hom.app K ≫
      (unit d U).app ((pull (A := A) u).obj ((res d V).obj K)) at hphi
  have heq := mappedUnitIsoComparison (res d U) (d.ordinaryToCompleted u K) _
    ((alpha d u).app K) ((phi d u).app ⟨K, hK⟩) hphi a
  exact (congrArg
    ((proEtaleRingDerivedAdjunction u (exchangeConstantRing V A) (exchangeConstantRing U A)
      (exchangeConstantIso u A)).homEquiv _ _) heq).trans
    ((proEtaleRingSheafChangeAdjunction u
      (exchangeConstantRing V A) (d.completedRing V)
      (exchangeConstantRing U A) (d.completedRing U)
      (exchangeScalar d V) (exchangeScalar d U) (exchangeConstantIso u A)
      (d.integralRingIso u) (exchangeScalar_comm d u)).2.2 K L
        (d.ordinaryToCompleted u K ≫ a))


/-- Source functor for the normalized equation, on the full derived-complete category.
Source: blueprint completed-exchange-coherence, paragraph 2
(blueprint: def-weil-pbc-ordered-coefficient-comparison-data). -/
def normalizedSource := inclusion d X ⋙ d.push f ⋙ d.completedPull g ⋙ res d Y'

/-- Target functor for the normalized equation in constant coefficients.
Source: blueprint completed-exchange-coherence, paragraph 2
(blueprint: def-weil-pbc-ordered-coefficient-comparison-data). -/
def normalizedTarget := inclusion d X ⋙ res d X ⋙ completePull d g' ⋙ push (A := A) f'

/-- The restricted raw ordered construction followed by the specified target comparison.
Source: blueprint completed-exchange-coherence, paragraph 2
(blueprint: def-weil-pbc-ordered-coefficient-comparison-data). -/
def rawComponent (sq : ChosenCartesianSquare g' f' f g) (K : AComplete d X) :
    (normalizedSource (f := f) (g := g) d).obj K ⟶
      (normalizedTarget (g' := g') (f' := f') d).obj K :=
  (res d Y').map (d.completedExchange sq K.obj) ≫
    (iotaT (g' := g') (f' := f') d K.obj K.property).hom

/-- The specified constant strict mate, conjugated by s, t and the source scalar map.
Source: Stacks 099M, 0E48
(blueprint: def-weil-pbc-ordered-coefficient-comparison-data). -/
def constantComponent (sq : ChosenCartesianSquare g' f' f g) (K : AComplete d X) :
    (normalizedSource (f := f) (g := g) d).obj K ⟶
      (normalizedTarget (g' := g') (f' := f') d).obj K :=
  (iotaS (f := f) (g := g) d K.obj K.property).hom ≫
    (S (f := f) (g := g) d ((res d X).obj K.obj)).hom ≫
    (rlim (A := A) Y').map ((exchangeConstantSquare (A := A) sq).exchangeTowerMate.app
      ((reduction d X).obj ((res d X).obj K.obj))) ≫
    (T (f' := f') (g' := g') d ((res d X).obj K.obj)).inv

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Both displayed composites are natural for every morphism of complete inputs.
Source: Stacks 0E48 (blueprint: def-weil-pbc-ordered-coefficient-comparison-data).
Proof: the raw strict exchange is the composite H inverse, reduction of the ambient
mate, H prime. All its terms are natural in the ambient input. The scalar comparisons
are natural isomorphisms defined by ordinary sections or universal model comparisons.
Their completed extensions are natural by uniqueness under the completion unit. The
constant mate and its reconstruction and direct-limit comparisons are natural as well.
Compose these naturality equations. Fullness allows every morphism between complete
objects, with no boundedness or finite-origin restriction. -/
theorem normalized_naturality (sq : ChosenCartesianSquare g' f' f g)
    (K L : AComplete d X) (a : K ⟶ L) :
    (normalizedSource (f := f) (g := g) d).map a ≫ rawComponent d sq L =
      rawComponent d sq K ≫ (normalizedTarget (g' := g') (f' := f') d).map a ∧
    (normalizedSource (f := f) (g := g) d).map a ≫ constantComponent d sq L =
      constantComponent d sq K ≫ (normalizedTarget (g' := g') (f' := f') d).map a := by
  let piA (U V : Scheme.{t}) (u : U ⟶ V) :
      d.push u ⋙ completedReductionTower V d ≅
        completedReductionTower U d ⋙ d.towerPush u :=
    NatIso.ofComponents (fun K ↦ asIso (d.towerProjection u K))
      (fun {K L} a ↦ (d.towerProjection_properties u K).2.1 L a)
  let e : d.push f ⋙ d.completedPull g ⟶ d.completedPull g' ⋙ d.push f' :=
    Functor.whiskerRight (Functor.isoWhiskerRight (piA X Y f) (d.towerPull g)).hom
        (completedRlim Y' (d.completedRing Y')) ≫
      Functor.whiskerRight (exchangeStrictNatTrans d sq)
        (completedRlim Y' (d.completedRing Y')) ≫
      Functor.whiskerLeft (completedReductionTower X d ⋙ d.towerPull g')
        (d.directImageRlimIso f').inv
  let it : inclusion d X ⋙ d.completedPull g' ⋙ d.push f' ⋙ res d Y' ≅
      normalizedTarget (g' := g') (f' := f') d :=
    Functor.isoWhiskerLeft (inclusion d X ⋙ d.completedPull g') (chi d f') ≪≫
      Functor.isoWhiskerRight (phi d g') (push (A := A) f')
  constructor
  · exact (Functor.whiskerLeft (inclusion d X)
      (Functor.whiskerRight e (res d Y')) ≫ it.hom).naturality a
  · let aj := exchangeTowerAdjunction f (exchangeConstantRing Y A)
      (exchangeConstantRing X A) (exchangeConstantIso f A)
    let ar := proEtaleRingDerivedAdjunction f (exchangeConstantRing Y A)
      (exchangeConstantRing X A) (exchangeConstantIso f A)
    let pi0 := (mateEquiv ar aj
      (TwoSquare.mk _ _ _ _ (reductionPullIso d f).hom)).natTrans
    have hpi (M : D (A := A) X) : pi0.app M = projection d f M := by
      apply (aj.homEquiv _ _).symm.injective
      change (aj.homEquiv _ _).symm (pi0.app M) =
        (aj.homEquiv _ _).symm ((aj.homEquiv _ _)
          ((reductionPullIso d f).hom.app ((push (A := A) f).obj M) ≫
            (reduction d X).map (ar.counit.app M)))
      rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit]
      exact mateEquiv_counit ar aj
        (TwoSquare.mk _ _ _ _ (reductionPullIso d f).hom) M
    let p0 : push (A := A) f ⋙ reduction d Y ≅
        reduction d X ⋙ exchangeConstantPush (A := A) f :=
      NatIso.ofComponents (fun M ↦ asIso (projection d f M)) (by
        intro M N b
        simpa only [asIso_hom, ← hpi] using pi0.naturality b)
    let h0 := Functor.isoWhiskerLeft (push (A := A) f) (reductionPullIso d g).symm ≪≫
      Functor.isoWhiskerRight p0 (exchangeConstantPull (A := A) g)
    let s0 := Functor.isoWhiskerRight h0 (rlim (A := A) Y')
    let t0 := Functor.isoWhiskerLeft (reduction d X)
      (Functor.isoWhiskerLeft (exchangeConstantPull (A := A) g')
        (directLimitIso (A := A) f'))
    let rec0 : completePull d g' ≅
        reduction d X ⋙ exchangeConstantPull (A := A) g' ⋙ rlim (A := A) X' :=
      Functor.isoWhiskerRight (reductionPullIso d g').symm (rlim (A := A) X')
    let tt := Functor.isoWhiskerRight rec0 (push (A := A) f') ≪≫ t0
    let pushed : AComplete d X ⥤ AComplete d Y :=
      ObjectProperty.lift (d.TowerComplete Y) (inclusion d X ⋙ d.push f)
        (fun M ↦ d.push_complete f M.obj M.property)
    let src : normalizedSource (f := f) (g := g) d ≅
        inclusion d X ⋙ res d X ⋙ push (A := A) f ⋙ completePull d g :=
      Functor.isoWhiskerLeft pushed (phi d g) ≪≫
        Functor.isoWhiskerRight (Functor.isoWhiskerLeft (inclusion d X) (chi d f))
          (completePull d g)
    let cc := src.hom ≫
      Functor.whiskerLeft (inclusion d X ⋙ res d X) s0.hom ≫
      Functor.whiskerLeft (inclusion d X ⋙ res d X ⋙ reduction d X)
        (Functor.whiskerRight
          (exchangeConstantSquare (A := A) sq).exchangeTowerMate (rlim (A := A) Y')) ≫
      Functor.whiskerLeft (inclusion d X ⋙ res d X) tt.inv
    exact cc.naturality a

/-- The raw ordered exchange as an actual natural transformation after scalar restriction.
Source: blueprint completed-exchange-coherence, paragraph 2
(blueprint: def-weil-pbc-ordered-coefficient-comparison-data). -/
def rawNormalized (sq : ChosenCartesianSquare g' f' f g) :
    normalizedSource (f := f) (g := g) d ⟶ normalizedTarget (g' := g') (f' := f') d where
  app K := rawComponent d sq K
  naturality K L a := (normalized_naturality d sq K L a).1

/-- The specified constant-coefficient ordered expression as a natural transformation.
Source: Stacks 099M, 0E48
(blueprint: def-weil-pbc-ordered-coefficient-comparison-data). -/
def constantNormalized (sq : ChosenCartesianSquare g' f' f g) :
    normalizedSource (f := f) (g := g) d ⟶ normalizedTarget (g' := g') (f' := f') d where
  app K := constantComponent d sq K
  naturality K L a := (normalized_naturality d sq K L a).2

end AlgebraicGeometry.Scheme.OrderedExchange
