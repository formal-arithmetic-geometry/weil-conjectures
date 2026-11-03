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

/-- Derived reduction and total inverse limit give the normalized equivalence on
pulled-back condensed integral coefficients.
Source: latest blueprint, sk-lem-sp-tower-equivalence and the normalization paragraph
of sk-prop-sp-integral-adjunction-bijection; Bhatt--Scholze Lemma 3.5.7
(blueprint: det-sp-normalized-equivalence).

Proof, following the seven DAG steps:
1. Apply lem-sp-ringed-quotient-diagram-adjunction to the actual quotient rings.
K-flat tensor representatives compute reduction with its quotient-induced transitions;
the right adjoint is total inverse limit after exact scalar restriction.
2. Write ell = u pi^e with u a unit and e positive. The ell-power tower is the cofinal
subtower indexed by en of the uniformizer-power tower. Exact countable products and
lem-fix-cofinal-roos-restriction identify the augmented Roos maps, so the adjunction
unit is completion and is invertible exactly on derived-complete objects.
3. For any normalized tower, lem-coef-normalized-dvr-effectivity makes each canonical
scalar transpose of the actual limit projection invertible. These are the evaluated
counit components; jointly conservative evaluations make the whole counit invertible.
4. Under Noetherianity alone, (1) implies (2) in sk-prop-integral-criterion,
giving derived completeness of every Dbc object.
5. For k finite or algebraically closed, ell invertible in k, and T separated of
finite type over k, det-sp-reduction-tower-normalized applies in the
sk-lem-int-integral-heart setting. It supplies constructibility and common
cohomological and Tor intervals for the reduction tower. Such T is Noetherian,
so step 4 applies without another hypothesis.
6. lem-sp-integral-constructible-completed-transport reconstructs every normalized
constructible tower as a bounded constructible complete integral complex.
7. Restrict the adjunction to the two full subcategories. The same natural unit and
counit retain the ambient triangle identities and are isomorphisms there, hence give
mutually inverse equivalences. -/
theorem normalized_equivalence_statement :
    ∃ D : Model l E T, Nonempty (NormalizedEquivalence l E T D) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedIntegralTower
