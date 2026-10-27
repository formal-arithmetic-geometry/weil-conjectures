/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q87
-/
module

public import Sheaf.AlgebraicGeometry.RigRegularFormalGeometry

/-! # Ordered formal resolution towers

Source: Temkin, Non-embedded Desingularization, §§2.2.2–2.2.5, 2.3.3–2.3.4,
2.4.8–2.4.12 and 3.1.5 (blueprint: def-per-formal-resolution-rule).
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A cartesian square of adic formal schemes, tested on all Noetherian adic formal
schemes and ideal-preserving formal morphisms. The test category is formal schemes:
using all locally ringed spaces here would incorrectly forget the adic topology.
Source: Temkin §§2.2.5, 2.4.8 (blueprint: def-per-formal-resolution-rule). -/
def IsAdicFormalPullback {A B C D : NoetherianAdicFormalScheme.{u}}
    (f : A.space ⟶ B.space) (g : A.space ⟶ C.space)
    (h : B.space ⟶ D.space) (k : C.space ⟶ D.space) : Prop :=
  f ≫ h = g ≫ k ∧ B.ideal.comap f = A.ideal ∧ C.ideal.comap g = A.ideal ∧
  D.ideal.comap h = B.ideal ∧ D.ideal.comap k = C.ideal ∧
  (∀ x : A.space, IsLocalHom (f.hom.stalkMap x).hom ∧
    IsLocalHom (g.hom.stalkMap x).hom) ∧
  ∀ (T : NoetherianAdicFormalScheme.{u}) (a : T.space ⟶ B.space)
    (b : T.space ⟶ C.space), B.ideal.comap a = T.ideal →
    C.ideal.comap b = T.ideal →
    (∀ t : T.space, IsLocalHom (a.hom.stalkMap t).hom ∧
      IsLocalHom (b.hom.stalkMap t).hom) → a ≫ h = b ≫ k →
    ∃! l : T.space ⟶ A.space, A.ideal.comap l = T.ideal ∧
      (∀ t : T.space, IsLocalHom (l.hom.stalkMap t).hom) ∧ l ≫ f = a ∧ l ≫ g = b

/-- A finite formal blowup tower retaining every center ideal and its order, even when
its blowup is an isomorphism. All levels retain the extended ideal of definition.
Source: Temkin §§2.2.2, 2.4.8 (blueprint: def-per-formal-resolution-rule). -/
structure FormalBlowupTower (X : NoetherianAdicFormalScheme.{u}) where
  length : ℕ
  level : Fin (length + 1) → NoetherianAdicFormalScheme.{u}
  initial : (level 0).space ≅ X.space
  initial_ideal : X.ideal.comap initial.hom = (level 0).ideal
  transition : ∀ (i j : Fin (length + 1)), i ≤ j → ((level j).space ⟶ (level i).space)
  transition_id : ∀ i, transition i i le_rfl = 𝟙 (level i).space
  transition_comp : ∀ i j k (hij : i ≤ j) (hjk : j ≤ k),
    transition j k hjk ≫ transition i j hij = transition i k (hij.trans hjk)
  transition_ideal : ∀ i j (hij : i ≤ j),
    (level i).ideal.comap (transition i j hij) = (level j).ideal
  center : ∀ i : Fin length, FormalIdeal (level i.castSucc).space
  blowup : ∀ i : Fin length,
    IsFormalBlowup (transition i.castSucc i.succ (le_of_lt i.castSucc_lt_succ)) (center i)

/-- The actual composite map from a level to the initial input.
Source: Temkin §2.4.8 (blueprint: def-per-formal-resolution-rule). -/
def FormalBlowupTower.toBase {X : NoetherianAdicFormalScheme.{u}}
    (A : FormalBlowupTower X) (i : Fin (A.length + 1)) : (A.level i).space ⟶ X.space :=
  A.transition 0 i (Fin.zero_le i) ≫ A.initial.hom

/-- Every center is nonempty and regular, lies over the original singular locus, and
is a coherent open ideal; the terminal formal affine chart rings are regular.
Source: Temkin §§2.4.8–2.4.10, Theorem 3.1.5, and ILO VIII Remark 2.3.11
(blueprint: def-per-formal-resolution-rule). -/
def FormalBlowupTower.IsStrongResolution {X : NoetherianAdicFormalScheme.{u}}
    (A : FormalBlowupTower X) : Prop :=
  (∀ i : Fin A.length, (A.center i).IsCoherent ∧ (A.center i).IsOpen ∧
    (A.center i).IsRegularCenter ∧
    (∃ x : (A.level i.castSucc).space, A.center i x ≠ ⊤) ∧
    ∀ x : (A.level i.castSucc).space, A.center i x ≠ ⊤ →
      (A.toBase i.castSucc).hom.base x ∈ X.singularLocus) ∧
  (A.level ⟨A.length, Nat.lt_succ_self A.length⟩).IsRegular

/-- Contracted formal pullback with exactly the empty centers removed. The order
embedding lists retained stages; `count` records the uncontracted levels. Cartesian
squares and ideal identities preserve the actual extended ideals and all nonempty
stages, including those inducing isomorphisms.
Source: Temkin §§2.2.3–2.2.5, 2.3.3, 2.4.8
(blueprint: def-per-formal-resolution-rule). -/
structure FormalResolutionComparison {X Y : NoetherianAdicFormalScheme.{u}}
    (h : Y.space ⟶ X.space) (A : FormalBlowupTower X) (B : FormalBlowupTower Y) where
  count : Fin (A.length + 1) →o Fin (B.length + 1)
  count_zero : count 0 = 0
  count_last : count ⟨A.length, Nat.lt_succ_self A.length⟩ =
    ⟨B.length, Nat.lt_succ_self B.length⟩
  retainedStage : Fin B.length ↪o Fin A.length
  count_before : ∀ k, count (retainedStage k).castSucc = k.castSucc
  count_after : ∀ k, count (retainedStage k).succ = k.succ
  deleted_level : ∀ i, i ∉ Set.range retainedStage → count i.succ = count i.castSucc
  levelMap : ∀ i, (B.level (count i)).space ⟶ (A.level i).space
  cartesian : ∀ i,
    IsAdicFormalPullback (levelMap i) (B.toBase (count i)) (A.toBase i) h
  naturality : ∀ i j (hij : i ≤ j),
    B.transition (count i) (count j) (count.monotone hij) ≫ levelMap i =
      levelMap j ≫ A.transition i j hij
  retained_ideal : ∀ k,
    (B.center k).comap (eqToHom (congrArg (fun j ↦ (B.level j).space) (count_before k))) =
      (A.center (retainedStage k)).comap (levelMap (retainedStage k).castSucc)
  deleted_iff_unit : ∀ i, i ∉ Set.range retainedStage ↔
    ∀ x : (B.level (count i.castSucc)).space,
      ((A.center i).comap (levelMap i.castSucc)) x = ⊤

/-- One rule on all rig-regular locally principal formal pairs, with regular pullback
compatibility and the length-zero normalization on the empty space. Existence of
comparisons is a proposition, so no extra coherence choices are imposed on the rule.
No independence of the distinguished ideal is required.
Source: Temkin Theorem 3.1.5, strong clause, §3.4.1
(blueprint: def-per-formal-resolution-rule). -/
structure RigRegularFormalResolutionRule where
  tower : ∀ X : RigRegularFormalInput.{u}, FormalBlowupTower X.formalScheme
  resolves : ∀ X, (tower X).IsStrongResolution
  compatible : ∀ (X Y : RigRegularFormalInput.{u})
    (h : Y.formalScheme.space ⟶ X.formalScheme.space), IsRegularFormalMap h →
    Nonempty (FormalResolutionComparison h (tower X) (tower Y))
  empty : ∀ X : RigRegularFormalInput.{u},
    IsEmpty X.formalScheme.space → (tower X).length = 0

end AlgebraicGeometry
