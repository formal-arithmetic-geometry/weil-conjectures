/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.CompleteExchangeMap
import WeilConjectures.SixFunctors.ProEtale.FiniteReductionExchangeIso
import WeilConjectures.SixFunctors.ProEtale.CompletedExchangeFromTower
public import WeilConjectures.SixFunctors.ClassicalDefinition
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.SixFunctors.BaseChange.Square
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!
# The completed exchange map is an isomorphism

Source: literature/blueprint/latest/blueprint/sec-proper-base-change/
sk-prop-pbc-complete/det-pbc-complete-exchange-iso.md; Stacks Project, Tag 0D6J.
(blueprint: det-pbc-complete-exchange-iso).

Positive exponent n+1 is represented by the natural index n in the existing reduction
functor. Classicality is tested on the cohomology sheaves of that actual finite-coefficient
reduction, through the existing section-action equivalence. Its lower bound may depend on n.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale.CompleteDerivedCompletion

attribute [local instance] AdicCompletion.ringMonoidalObject AdicCompletion.ringCommutative
  AdicCompletion.modulesDerived AdicCompletion.finiteRingMonoidalObject
  AdicCompletion.finiteRingCommutative AdicCompletion.finiteModulesDerived

/-- Proper base change makes both the exchange on the actual derived reduction tower and
its completed exchange invertible, when each finite reduction is bounded below and classical.
Source: blueprint `det-pbc-complete-exchange-iso`, statement and eleven-step DAG proof;
Stacks Project, Tag 0D6J (blueprint: det-pbc-complete-exchange-iso).

Proof:
1. For every level n, the evaluation at n of the tower exchange on red(K) is invertible by
   `finiteReductionExchange_isIso` (blueprint: det-pbc-complete-exchange-iso-finite-reduction;
   steps 1-10 of the node's former plan: section-action and normalized finite-discrete transports,
   finite-level proper base change, identification of the evaluated tower exchange).
2. Joint conservativity of the actual derived-tower evaluations, assertion (2) of
   `completeDerivedCompletion` (blueprint: det-pbc-complete-derived-completion), makes the tower
   exchange invertible.
3. The completed exchange is the R lim image of the tower exchange between the two endpoint
   isomorphisms, hence invertible by `completedExchange_isIso_of_tower`
   (blueprint: det-pbc-complete-exchange-iso-completion). No completeness of K and no lower
   bound uniform in n is used.
-/
theorem completedExchange_isIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {p' : X' ⟶ Y'}
    {p : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare g' p' p g) [IsProper p]
    (K : DerivedCategory (AdicCompletion.Modules l E X))
    (hK : ∀ n : ℕ,
      (∃ b : ℤ, ((AdicCompletion.derivedReduction l E X n).obj K).IsGE b) ∧
      ∀ q : ℤ, IsClassicalModuleSheaf
        ((InternalAbelianSheafModule.sectionModuleEquivalence (Scheme.ProEt.topology X)
          (AdicCompletion.finiteRing l E X n)).functor.obj
            ((DerivedCategory.homologyFunctor _ q).obj
              ((AdicCompletion.derivedReduction l E X n).obj K)))) :
    IsIso ((towerExchange l E sq.toCommSq).app ((red l E X).obj K)) ∧
      IsIso (completedExchangeMap l E sq.toCommSq K) := by
  let a := (towerExchange l E sq.toCommSq).app ((red l E X).obj K)
  have ha : IsIso a := by
    apply ((completeDerivedCompletion l E Y' Y' (𝟙 Y')).2.2.1 a).mpr
    intro n
    exact finiteReductionExchange_isIso l E sq K hK n
  have hb := completedExchange_isIso_of_tower l E sq K ha
  exact ⟨ha, hb⟩

end AlgebraicGeometry.ProEtale.CompleteDerivedCompletion
