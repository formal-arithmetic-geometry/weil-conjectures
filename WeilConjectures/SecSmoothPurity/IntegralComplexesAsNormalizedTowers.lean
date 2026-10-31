/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothPurityReductionTowerNormalized
public import WeilConjectures.AlgebraicGeometry.SmoothPurityNormalizedTowers
public import WeilConjectures.AlgebraicGeometry.IntegralConstructibleTriangulated
public import WeilConjectures.AlgebraicGeometry.IntegralDirectImageTowerData
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Integral complexes as normalized coefficient towers

Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-lem-sp-tower/_section.md`, node `sk-lem-sp-tower`, order 2955
(blueprint: sk-lem-sp-tower).

The reduction functor is the canonical derived reduction in `SpReductionTower`; its
right adjoint is total derived inverse limit in the coefficient-tower category.  The
unit of that adjunction is fixed by the representative equation
`SpTowerDerivedLimit.derived_normalization`: on a K-flat representative it is the
derived image of the ordinary unit `x ↦ (1 ⊗ x)_n` into the inverse limit, i.e. the
derived completion map `M → R lim_n M/ℓ^n` (blueprint: sk-def-pe-derived-completion).
The source presentation
uses section modules, which are canonically equivalent to modules over the pulled-back
condensed integral coefficient ring via `spIntegralInternalization`.  The constructible
source subcategory below is the bounded constructible predicate transported through
that equivalence, so no completeness condition is included in its definition.

Proof obligations follow the two blueprint paragraphs.  First, the ringed-diagram
adjunction gives reduction left adjoint to total derived inverse limit and identifies
its unit with the derived completion map.  Second, for a Noetherian scheme, the
integral criterion and the finite-level Roos calculation identify the normalized
constructible finite-Tor towers with bounded constructible integral complexes; the
restricted unit and counit are isomorphisms and hence give the equivalence.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
open AlgebraicGeometry
open AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})

/-- Restriction of the completed finite-level coefficient actions to the pulled-back
integral section ring.  This is the `(D,R)`-specialized form of
`IntegralDirectImageTower.completedRestriction`, so the limit below is tied to the
given reduction datum.  Source: blueprint, strict tower restriction in clause (2)
(blueprint: sk-lem-sp-tower). -/
abbrev spCompletedRestriction (D : SpCoefficientTowersAbelian l E T)
    (R : SpReductionTower l E T D) :=
  SheafOfModules.restrictScalars.{u + 1} ((sheafCompose (Scheme.ProEt.topology T)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map R.coefficient.hom)

/-- The strict inverse tower after the actual finite scalar actions are restricted to
the integral ring.  Source: blueprint, strict tower restriction in clause (2)
(blueprint: sk-lem-sp-tower). -/
def spRestrictedTower (D : SpCoefficientTowersAbelian l E T)
    (R : SpReductionTower l E T D) :
    spCoefficientTowers l E T ⥤ (ℕᵒᵖ ⥤ spIntegralSectionModules l E T) :=
  (Functor.ofOpSequence
    (X := fun n : ℕ ↦ spCompletedEvaluation l E T D n ⋙
      spCompletedRestriction l E T D R)
    (fun n ↦ Functor.whiskerRight (spCompletedTransition l E T D n)
      (spCompletedRestriction l E T D R))).flip

/-- The ordinary inverse limit of the restricted strict tower.  Source: blueprint,
clause (2) (blueprint: sk-lem-sp-tower). -/
def spOrdinaryLimit (D : SpCoefficientTowersAbelian l E T)
    (R : SpReductionTower l E T D) :
    spCoefficientTowers l E T ⥤ spIntegralSectionModules l E T :=
  spRestrictedTower l E T D R ⋙ Limits.lim

instance spReductionOrdinaryAdditive (D : SpCoefficientTowersAbelian l E T)
    (R : SpReductionTower l E T D) : R.ordinary.Additive := R.additive

/-- Data specifying the canonical total right derived inverse limit of the actual
restricted strict tower.  The ordinary and derived representative normalizations
are included so that this is the prescribed limit, rather than an unconstrained
right adjoint.  Source: blueprint, clause (2), with the
`IntegralDirectImageTower.restrictedTower/ordinaryLimit/Limit` pattern (blueprint:
sk-lem-sp-tower). -/
structure SpTowerDerivedLimit (D : SpCoefficientTowersAbelian l E T)
    (R : SpReductionTower l E T D) where
  [additive : (spOrdinaryLimit l E T D R).Additive]
  ordinaryAdjunction : R.ordinary ⊣ spOrdinaryLimit l E T D R
  /-- On a section `x`, the ordinary unit is the normalization `1 ⊗ x`. -/
  ordinary_normalization : ∀ (P : spIntegralSectionModules l E T) (n : ℕ)
    (U : T.ProEtᵒᵖ) (x : P.val.obj U),
    (limit.π ((spRestrictedTower l E T D R).obj (R.ordinary.obj P)) (op n)).val.app U
        ((ordinaryAdjunction.unit.app P).val.app U x) =
      (((R.level n).inv.app P).val.app U)
        (SheafOfModules.systemModelTmul ((D.scalar
          (spIntegralReductionScalar l E T R.coefficient n)).model) P U 1 x)
  derived : spDerivedCoefficientTowers l E T D ⥤
    DerivedCategory (spIntegralSectionModules l E T)
  unit : (spOrdinaryLimit l E T D R).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
    spTowerLocalization l E T D ⋙ derived
  universal : derived.IsRightDerivedFunctor unit
    (HomologicalComplex.quasiIso (spCoefficientTowers l E T) (.up ℤ))
  computes : ∀ I : CochainComplex (spCoefficientTowers l E T) ℤ,
    I.IsKInjective → IsIso (unit.app I)
  adjunction : R.red ⊣ derived
  /-- The derived representative equation transports the ordinary normalized unit
  through the specified reduction counit.  Since that counit is invertible on K-flat
  representatives (`R.computes`), this determines `adjunction.unit`: it is the derived
  completion map `M → R lim_n M/ℓ^n` (blueprint: sk-def-pe-derived-completion). -/
  derived_normalization : ∀ (P : CochainComplex (spIntegralSectionModules l E T) ℤ),
    adjunction.homEquiv (DerivedCategory.Q.obj P)
        ((spTowerLocalization l E T D).obj
          ((R.ordinary.mapHomologicalComplex (.up ℤ)).obj P))
        ((R.counit.app P) ≫
          (spTowerLocalization l E T D).map (𝟙 _)) =
      DerivedCategory.Q.map
        ((ordinaryAdjunction.mapHomologicalComplex (.up ℤ)).unit.app P) ≫ unit.app
          ((R.ordinary.mapHomologicalComplex (.up ℤ)).obj P)

/-- The adjunction and its constructible restriction asserted by
`sk-lem-sp-tower`.  The two functors are fixed by the canonical reduction tower and
by the total derived inverse-limit construction; the adjunction unit, the displayed
derived-completion map, is fixed by `limitData.derived_normalization`.  Source:
blueprint, node sk-lem-sp-tower (blueprint: sk-lem-sp-tower). -/
structure SpTowerAdjunction (D : SpCoefficientTowersAbelian l E T)
    (R : SpReductionTower l E T D) where
  /-- The canonical total derived inverse limit, its adjunction and its normalized unit. -/
  limitData : SpTowerDerivedLimit l E T D R
  /-- On a Noetherian scheme the adjunction restricts to the claimed equivalence. -/
  restriction : IsNoetherian T →
    ∃ e :
      ((constantModelBoundedConstructible (spIntegralCondensed l E) T).inverseImage
          (spIntegralInternalization l E T)).FullSubcategory ≌
        (spNormalizedConstructibleTorTowers l E T D).FullSubcategory,
      e.functor ⋙ (spNormalizedConstructibleTorTowers l E T D).ι =
          ((constantModelBoundedConstructible (spIntegralCondensed l E) T).inverseImage
            (spIntegralInternalization l E T)).ι ⋙ R.red ∧
        e.inverse ⋙
            ((constantModelBoundedConstructible (spIntegralCondensed l E) T).inverseImage
              (spIntegralInternalization l E T)).ι =
          (spNormalizedConstructibleTorTowers l E T D).ι ⋙ limitData.derived

/-- Let `E/ℚ_l` be finite and `T` a scheme.  Derived reduction
`M ↦ (M/ℓ^n)_n` is left adjoint to total derived inverse limit.  Its unit is the
canonical derived-completion map `M → R limₙ M/ℓⁿ`.  If `T` is Noetherian, the
adjunction restricts to an equivalence between bounded constructible integral
complexes and normalized constructible coefficient towers.

Proof plan from the blueprint.  (1) Apply the ringed-diagram adjunction to the
pulled-back integral coefficient ring and its finite quotient tower, using
`lem-sp-ringed-quotient-diagram-adjunction`; this supplies `adjunction` and its
quotient unit.  (2) Use `det-sp-reduction-tower-normalized` and
`lem-fix-condensed-integral-criterion` to identify reductions of integral
constructible complexes with normalized constructible towers and to identify the
unit with derived completion.  (3) For a normalized tower, use
`lem-sp-ell-coefficient-fiber`, `lem-weil-proetale-countable-products-exact`, and
`lem-sp-perfect-reduction-roos-comparison` to compare the finite-free/Roos model
with the actual level reduction.  (4) The error triangle and finite-tail cone,
`lem-sp-normalized-quotient-error-triangle` and `lem-sp-roos-finite-tail-cone`,
show that every counit component is an isomorphism; the nilpotent shift gives the
finite geometric contraction.  (5) The same Roos comparison with the uniformizer
and `lem-sp-cofinal-finite-reduction-constructibility` give bounded constructible
cohomology and a common Tor interval for the inverse limit, so the condensed
integral criterion places it in the source subcategory.  (6) Evaluations are jointly
conservative, hence the unit and counit restrict to inverse equivalences. -/
theorem sp_lem_sp_tower (D : SpCoefficientTowersAbelian l E T)
    (R : SpReductionTower l E T D) :
    Nonempty (SpTowerAdjunction l E T D R) := by
  sorry

end AlgebraicGeometry.ProEtale
