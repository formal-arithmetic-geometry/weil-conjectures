/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedIntegralTower.CondensedNormalizedTowers
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.Algebra.Homology.System.SystemDerivedEvaluation
public import WeilConjectures.AlgebraicGeometry.CondensedIntegralCriterion
public import WeilConjectures.AlgebraicGeometry.CondensedIntegralTower.NormalizedAdjunctionConstruction
public import WeilConjectures.AlgebraicGeometry.CondensedIntegralTower.NormalizedAdjunctionCoordinates
public import WeilConjectures.AlgebraicGeometry.CondensedIntegralTower.NormalizedCompletionDetection
public import WeilConjectures.AlgebraicGeometry.CondensedIntegralTower.NormalizedCounitEffectivity
public import WeilConjectures.AlgebraicGeometry.CondensedIntegralTower.NormalizedFiniteConstructibility
public import WeilConjectures.AlgebraicGeometry.CondensedIntegralTower.NormalizedProjectionCompatibility
public import WeilConjectures.CategoryTheory.Adjunction.FullSubcategoryAdjunctionEquivalence

/-! # Derived normalized coefficient-tower equivalence

Source: latest blueprint, `sk-lem-sp-tower/sk-lem-sp-tower-equivalence.md` and
`sk-prop-sp-integral-adjunction-bijection.md` (blueprint: det-sp-normalized-equivalence).
The statement uses the current condensed coefficient ring pulled back from the point.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.Obj
open AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedIntegralTower

namespace AlgebraicGeometry.ProEtale.CondensedIntegralTower

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})

/-- The exact ordinary level evaluation in internal module coordinates.
Source: coefficient-tower evaluation (blueprint: det-sp-normalized-equivalence). -/
def ordinaryInternalEvaluation (n : ℕ) : Towers l E T ⥤
    Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (finiteRing l E n) T) :=
  SheafOfModules.systemEvaluation.{u + 1, u, u + 1} (rings l E T) n ⋙
    (CategoryTheory.InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
      (Scheme.ProEt.topology T) (condensedRingObj (finiteRing l E n) T)).inverse

/-- Exact level evaluation is additive, since it preserves finite products.
Source: exact evaluation (blueprint: det-sp-normalized-equivalence). -/
instance ordinaryInternalEvaluation_additive (n : ℕ) :
    (ordinaryInternalEvaluation l E T n).Additive :=
  let e := CategoryTheory.InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    (Scheme.ProEt.topology T) (condensedRingObj (finiteRing l E n) T)
  letI := Functor.additive_of_preserves_binary_products e.inverse
  inferInstanceAs ((SheafOfModules.systemEvaluation.{u + 1, u, u + 1}
    (rings l E T) n ⋙ e.inverse).Additive)

/-- The ordinary inverse-limit projection, as the scalar transpose of the evaluated
ordinary tensor/limit counit. Source: ringed-system adjunction
(blueprint: det-sp-normalized-equivalence). -/
def ordinaryLimitProjection (D : Model l E T) (n : ℕ) :
    D.ordinaryLimit ⟶ ordinaryInternalEvaluation l E T n ⋙
      Mod.comap ((upperStarFromPoint T).map (quotient l E n)) :=
  Functor.whiskerLeft D.ordinaryLimit
      (Mod.extendRestrictAdjunction ((upperStarFromPoint T).map (quotient l E n))).unit ≫
    Functor.whiskerRight
      (Functor.whiskerLeft D.ordinaryLimit (ordinaryInternalLevels l E T D.ordinary n).inv)
      (Mod.comap ((upperStarFromPoint T).map (quotient l E n))) ≫
    Functor.whiskerRight (Functor.whiskerRight D.ordinaryAdjunction.counit
      (ordinaryInternalEvaluation l E T n))
      (Mod.comap ((upperStarFromPoint T).map (quotient l E n)))

/-- Evaluation of localization, with its canonical section-equivalence comparison.
Source: exact level evaluation (blueprint: det-sp-normalized-equivalence). -/
def internalEvaluationFactor (n : ℕ) (I : CochainComplex (Towers l E T) ℤ) :
    (evaluation l E T n).obj (DerivedCategory.Q.obj I) ≅
      DerivedCategory.Q.obj
        (((ordinaryInternalEvaluation l E T n).mapHomologicalComplex (.up ℤ)).obj I) :=
  let e := CategoryTheory.InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    (Scheme.ProEt.topology T) (condensedRingObj (finiteRing l E n) T)
  letI := Functor.additive_of_preserves_binary_products e.inverse
  e.inverse.mapDerivedCategory.mapIso
      ((SheafOfModules.systemEvaluation.{u + 1, u, u + 1}
        (rings l E T) n).mapDerivedCategoryFactors.app I) ≪≫
    e.inverse.mapDerivedCategoryFactors.app
      (((SheafOfModules.systemEvaluation.{u + 1, u, u + 1}
        (rings l E T) n).mapHomologicalComplex (.up ℤ)).obj I)

/-- The derived scalar transpose of the evaluated counit. Its representative
normalization below identifies it with the actual total-limit projection.
Source: Counit paragraph (blueprint: det-sp-normalized-equivalence). -/
def derivedLimitProjection (D : Model l E T) (adj : D.red ⊣ D.rlim) (n : ℕ) :
    D.rlim ⟶ evaluation l E T n ⋙
      (Mod.comap ((upperStarFromPoint T).map (quotient l E n))).mapDerivedCategory :=
  Functor.whiskerLeft D.rlim
      (Mod.derivedExtendMapDerivedCategoryAdjunction
        ((upperStarFromPoint T).map (quotient l E n))).unit ≫
    Functor.whiskerRight (Functor.whiskerLeft D.rlim (D.levels n).inv)
      (Mod.comap ((upperStarFromPoint T).map (quotient l E n))).mapDerivedCategory ≫
    Functor.whiskerRight (Functor.whiskerRight adj.counit (evaluation l E T n))
      (Mod.comap ((upperStarFromPoint T).map (quotient l E n))).mapDerivedCategory

/-- The canonical reduction/limit adjunction, its completion unit, arbitrary normalized
counit, and bounded constructible restriction. All fields are conclusions, not hypotheses.
Source: latest blueprint, sk-lem-sp-tower-equivalence, Adjunction, Unit, Counit and
Restriction paragraphs (blueprint: det-sp-normalized-equivalence). -/
structure NormalizedEquivalence (D : Model l E T) where
  /-- The ambient unbounded reduction/total-limit adjunction. -/
  adjunction : D.red ⊣ D.rlim
  /-- Derivation carries the ordinary adjunction unit to this unit. -/
  derivedUnit : ∀ P : CochainComplex (AdicCompletion.Modules l E T) ℤ,
    DerivedCategory.Q.map
        ((D.ordinaryAdjunction.mapHomologicalComplex (.up ℤ)).unit.app P) ≫
      D.limitUnit.app ((D.ordinaryRed.mapHomologicalComplex (.up ℤ)).obj P) =
    adjunction.unit.app (DerivedCategory.Q.obj P) ≫ D.rlim.map (D.redCounit.app P)
  /-- These are the actual derived projections of the ordinary limit, normalized
  by the universal total right-derived comparison on representatives. -/
  projections : ∀ (n : ℕ) (I : CochainComplex (Towers l E T) ℤ),
    D.limitUnit.app I ≫
      (derivedLimitProjection l E T D adjunction n).app (DerivedCategory.Q.obj I) ≫
      (Mod.comap ((upperStarFromPoint T).map (quotient l E n))).mapDerivedCategory.map
        (internalEvaluationFactor l E T n I).hom ≫
      (Mod.comap ((upperStarFromPoint T).map (quotient l E n))).mapDerivedCategoryFactors.hom.app
        (((ordinaryInternalEvaluation l E T n).mapHomologicalComplex (.up ℤ)).obj I) =
    DerivedCategory.Q.map
      ((NatTrans.mapHomologicalComplex (ordinaryLimitProjection l E T D n) (.up ℤ)).app I)
  /-- The unit is the canonical augmented Roos completion map. -/
  completionUnit : ∀ (K : Integral l E T)
    (P : CochainComplex (AdicCompletion.Modules l E T) ℤ)
    (e : DerivedCategory.Q.obj P ≅ K),
    (HomologicalComplex.quasiIso (AdicCompletion.Modules l E T) (.up ℤ)).kFlat P →
      ∃ c : D.rlim.obj (D.red.obj K) ≅ DerivedCategory.Q.obj (AdicCompletion.roos l E T P),
        adjunction.unit.app K ≫ c.hom = AdicCompletion.completionMap l E T K P e
  /-- The unit is invertible exactly for derived-complete objects. -/
  unit_iff : ∀ M : Integral l E T,
    IsIso (adjunction.unit.app M) ↔ IsDerivedComplete l E T M
  /-- Every normalized tower has invertible counit, including unbounded towers. -/
  counit : ∀ C : DerivedTowers l E T,
    (∀ (m n : ℕ) (h : m ≤ n), IsIso ((D.reduction h).app C)) →
      IsIso (adjunction.counit.app C)
  /-- The level components of the counit are the canonical derived reductions. -/
  counitLevels : ∀ C : DerivedTowers l E T,
    (∀ (m n : ℕ) (h : m ≤ n), IsIso ((D.reduction h).app C)) →
      ∀ m : ℕ, IsIso ((D.levels m).inv.app (D.rlim.obj C) ≫
        (evaluation l E T m).map (adjunction.counit.app C))
  /-- Bounded constructible objects are complete under the integral criterion. -/
  constructibleComplete : IsNoetherian T →
    ∀ M : Dbc l E T, IsDerivedComplete l E T M.obj
  /-- In the integral local-structure setting, restriction to bounded constructible
  normalized towers is an equivalence. The geometric assumptions are confined to
  this field; completeness above needs only Noetherianity. -/
  restriction : ∀ (k : Type u) [Field k], (Finite k ∨ IsAlgClosed k) →
    IsUnit (l : k) → ∀ a : T ⟶ AlgebraicGeometry.Spec (CommRingCat.of k),
    IsSeparated a → LocallyOfFiniteType a → QuasiCompact a →
    ∃ e : Dbc l E T ≌ NormalizedTowers l E T D,
      e.functor ⋙ (Normalized l E T D).ι =
        (constantModelBoundedConstructible (DerivedNakayama.integerRing l E) T).ι ⋙ D.red ∧
      e.inverse ⋙
          (constantModelBoundedConstructible (DerivedNakayama.integerRing l E) T).ι =
        (Normalized l E T D).ι ⋙ D.rlim ∧
      (∀ M : Dbc l E T,
        HEq ((constantModelBoundedConstructible (DerivedNakayama.integerRing l E) T).ι.map
          (e.unitIso.hom.app M)) (adjunction.unit.app M.obj)) ∧
      (∀ C : NormalizedTowers l E T D,
        HEq ((Normalized l E T D).ι.map (e.counitIso.hom.app C))
          (adjunction.counit.app C.obj))

private theorem evaluation_detects_isIso
    {C C' : DerivedTowers l E T} (f : C ⟶ C')
    (h : ∀ n : ℕ, IsIso ((evaluation l E T n).map f)) : IsIso f := by
  apply (SheafOfModules.systemDerivedEvaluation_isIso_iff (rings l E T) f).2
  intro n
  let e := CategoryTheory.InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    (Scheme.ProEt.topology T) (condensedRingObj (finiteRing l E n) T)
  let := Functor.additive_of_preserves_binary_products e.inverse
  have hi : IsIso (e.inverse.mapDerivedCategory.map
      ((SheafOfModules.derivedSystemEvaluation (rings l E T) n).map f)) := h n
  exact isIso_of_reflects_iso _ e.inverse.mapDerivedCategory

private theorem limit_isComplete (D : Model l E T) (adj : D.red ⊣ D.rlim)
    (hη : ∀ M : Integral l E T,
      IsIso (adj.unit.app M) ↔ IsDerivedComplete l E T M)
    (C : DerivedTowers l E T) (hε : IsIso (adj.counit.app C)) :
    IsDerivedComplete l E T (D.rlim.obj C) := by
  let := hε
  apply (hη _).mp
  have : IsIso (adj.unit.app (D.rlim.obj C) ≫ D.rlim.map (adj.counit.app C)) := by
    rw [adj.right_triangle_components]
    exact ⟨⟨𝟙 _, by simp⟩⟩
  exact IsIso.of_isIso_comp_right _ (D.rlim.map (adj.counit.app C))

private theorem constructible_isComplete (hT : IsNoetherian T) (M : Dbc l E T) :
    IsDerivedComplete l E T M.obj := by
  have := hT
  have h : IsDerivedComplete l E T M.obj ∧
      constantModelBoundedConstructible (DerivedNakayama.quotientRing l E 1) T
        ((AdicCompletion.derivedReduction l E T 0).obj M.obj) :=
    ((condensed_integral_criterion l E T M.obj).out 0 1).mp M.property
  exact h.1

/-- Derived reduction and total inverse limit give the normalized equivalence on
pulled-back condensed integral coefficients.
Source: latest blueprint, sk-lem-sp-tower-equivalence and the normalization paragraph
of sk-prop-sp-integral-adjunction-bijection; Bhatt--Scholze Lemma 3.5.7
(blueprint: det-sp-normalized-equivalence).

Proof, following the blueprint paragraphs:
1. Construct the native universal tensor/limit pair, its normalized derived Hom
correspondence, actual projections and Roos completion comparison.
2. Specialize the Hom correspondence to the identity to obtain the unit equation.
A native K-flat representative and representative independence identify unit
invertibility with derived completeness.
3. Finite counit effectivity gives the canonical counit comparison isomorphisms.
Cancel the level isomorphisms and use conservative exact evaluations to get the
unbounded counit isomorphism.
4. Over Noetherian T, the integral criterion (1) implies (2) gives completeness
of every bounded constructible integral object.
5. In the stated geometric field setting, finite constructibility puts reduction
in the normalized constructible tower category and makes the first uniformizer
reduction of each normalized tower limit bounded constructible.
6. The right triangle identity and counit invertibility make the unit at each
limit invertible. Hence it is derived complete. Finite type gives Noetherianity;
the integral criterion (2) implies (1) gives integral bounded constructibility.
7. Restrict the adjunction to these full subcategories. Invertible ambient unit
and counit yield an equivalence retaining the original components. -/
theorem normalized_equivalence_statement :
    ∃ D : Model l E T, Nonempty (NormalizedEquivalence l E T D) := by
  obtain ⟨D, adj, hh, hc⟩ := normalized_adjunction_construction l E T
  have hp := normalized_projections_of_hom l E T D adj hh
  have hu := (derivedHomNormalized_iff_unit l E T D adj).mp hh
  have hη := normalized_unit_iff l E T D adj hc
  have hlevels := normalized_counit_effectivity l E T D adj hp
  have hε (C : DerivedTowers l E T)
      (hC : ∀ (m n : ℕ) (h : m ≤ n), IsIso ((D.reduction h).app C)) :
      IsIso (adj.counit.app C) := by
    apply evaluation_detects_isIso l E T
    intro n
    have := hlevels C hC n
    exact IsIso.of_isIso_comp_left ((D.levels n).inv.app (D.rlim.obj C)) _
  refine ⟨D, ⟨{
    adjunction := adj
    derivedUnit := hu
    projections := hp
    completionUnit := hc
    unit_iff := hη
    counit := hε
    counitLevels := hlevels
    constructibleComplete := constructible_isComplete l E T
    restriction := ?_ }⟩⟩
  intro k _ hk hl a hs hf hq
  obtain ⟨hF, hfinite⟩ := normalized_finite_constructibility l E T D adj hε
    k hk hl a hs hf hq
  have hT : IsNoetherian T :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian a
      toCompactSpace := QuasiCompact.compactSpace_of_compactSpace a }
  have hG (C : NormalizedTowers l E T D) :
      constantModelBoundedConstructible (DerivedNakayama.integerRing l E) T
        (D.rlim.obj C.obj) := by
    have := hT
    apply ((condensed_integral_criterion l E T (D.rlim.obj C.obj)).out 1 0).mp
    exact ⟨limit_isComplete l E T D adj hη C.obj (hε C.obj C.property.2), hfinite C⟩
  exact adj.fullSubcategoryEquivalence
    (constantModelBoundedConstructible (DerivedNakayama.integerRing l E) T)
    (Normalized l E T D) hF hG
    (fun M ↦ (hη M.obj).mpr (constructible_isComplete l E T hT M))
    (fun C ↦ hε C.obj C.property.2)

end AlgebraicGeometry.ProEtale.CondensedIntegralTower
