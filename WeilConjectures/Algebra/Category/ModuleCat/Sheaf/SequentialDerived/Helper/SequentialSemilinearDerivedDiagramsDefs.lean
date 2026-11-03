/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.Algebra.Homology.System.SystemDerivedTransition
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-! # Sequential semilinear derived diagram definitions

Source: latest blueprint, sec-smooth-purity/sk-lem-sp-tower/
lem-coef-integral-finite-extension.proof.md, paragraph 4; the general sequential
lemma formulated in the DAG (blueprint: def-sf-sequential-semilinear-derived-helper-definitions).

The strict category, componentwise abelian structure, exact evaluations and
localized transitions are the existing `SheafOfModules.StrictRingSystem` API.
Index `n : ℕ` denotes the positive index `n+1`. The functor `B` records the ring
maps and their composites; it imposes no condition on the adjacent ring maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace SheafOfModules.SequentialDerived.Helper

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [siteSmall : EssentiallySmall.{w} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w})

/-- A common lower cohomological bound on all evaluations.
Source: the sequential lemma, paragraph 2
(blueprint: def-sf-sequential-semilinear-derived-helper-definitions). -/
def _root_.SheafOfModules.SequentialDerived.Helper.HasCommonLowerBound
    (M : DerivedCategory (StrictRingSystem B)) : Prop :=
  ∃ a : ℤ, ∀ n : ℕ, ((derivedSystemEvaluation B n).obj M).IsGE a

/-- The derived exact restriction along the adjacent coefficient map.
Source: the sequential lemma, paragraph 1
(blueprint: def-sf-sequential-semilinear-derived-helper-definitions). -/
abbrev adjacentRestriction (n : ℕ) :=
  (systemRestriction B (Nat.le_succ n)).mapDerivedCategory

/-- The product of the vertex Hom groups, with the standard cohomological shift.
Source: the sequential lemma, definition of P^r
(blueprint: def-sf-sequential-semilinear-derived-helper-definitions). -/
abbrev vertexHom (M N : DerivedCategory (StrictRingSystem B)) (r : ℤ) :=
  ∀ n : ℕ, (derivedSystemEvaluation B n).obj M ⟶
    ((derivedSystemEvaluation B n).obj N)⟦r⟧

/-- The product of the adjacent-edge Hom groups. Restriction is applied after shift.
Source: the sequential lemma, definition of Q^r
(blueprint: def-sf-sequential-semilinear-derived-helper-definitions). -/
abbrev edgeHom (M N : DerivedCategory (StrictRingSystem B)) (r : ℤ) :=
  ∀ n : ℕ, (derivedSystemEvaluation B (n + 1)).obj M ⟶
    (adjacentRestriction B n).obj (((derivedSystemEvaluation B n).obj N)⟦r⟧)

/-- The shifted transition, transported through the canonical shift comparison.
Source: the sequential lemma, t^N_n[r]
(blueprint: def-sf-sequential-semilinear-derived-helper-definitions). -/
def shiftedTransition (N : DerivedCategory (StrictRingSystem B)) (r : ℤ) (n : ℕ) :
    ((derivedSystemEvaluation B (n + 1)).obj N)⟦r⟧ ⟶
      (adjacentRestriction B n).obj (((derivedSystemEvaluation B n).obj N)⟦r⟧) :=
  ((systemDerivedTransition B (Nat.le_succ n)).app N)⟦r⟧' ≫
    ((adjacentRestriction B n).commShiftIso r).inv.app
      ((derivedSystemEvaluation B n).obj N)

/-- The vertex-edge difference V(f_n) t^M_n - t^N_n[r] f_(n+1).
Source: the sequential lemma, displayed definition of d^r
(blueprint: def-sf-sequential-semilinear-derived-helper-definitions). -/
def difference (M N : DerivedCategory (StrictRingSystem B)) (r : ℤ)
    (f : vertexHom B M N r) : edgeHom B M N r :=
  fun n ↦ (systemDerivedTransition B (Nat.le_succ n)).app M ≫
      (adjacentRestriction B n).map (f n) -
    f (n + 1) ≫ shiftedTransition B N r n

/-- Evaluation on maps, followed by the canonical identification N = N[0].
Source: the sequential lemma, the arrow labelled (e_n)
(blueprint: def-sf-sequential-semilinear-derived-helper-definitions). -/
def evaluateHom (M N : DerivedCategory (StrictRingSystem B)) (f : M ⟶ N) :
    vertexHom B M N 0 :=
  fun n ↦ (derivedSystemEvaluation B n).map f ≫
    (shiftFunctorZero (DerivedCategory (systemLevel B n)) ℤ).inv.app
      ((derivedSystemEvaluation B n).obj N)

/-- The natural contravariant/covariant action on adjacent-edge Hom groups.
Source: the sequential lemma, naturality of its exact sequence
(blueprint: def-sf-sequential-semilinear-derived-helper-definitions). -/
def edgeMap {M M' N N' : DerivedCategory (StrictRingSystem B)}
    (f : M' ⟶ M) (g : N ⟶ N') (r : ℤ) (x : edgeHom B M N r) :
    edgeHom B M' N' r :=
  fun n ↦ (derivedSystemEvaluation B (n + 1)).map f ≫ x n ≫
    (adjacentRestriction B n).map (((derivedSystemEvaluation B n).map g)⟦r⟧')


end SheafOfModules.SequentialDerived.Helper
