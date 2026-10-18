/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Properties
public import WeilConjectures.Blowup.Gluing
public import WeilConjectures.Compactification.FiniteTypeExtension
public import Sheaf.AlgebraicGeometry.IsRegularScheme

/-!
# Ordinary resolution towers and smooth contraction comparisons

Source: Illusie–Laszlo–Orgogozo, Exposé VIII, 2.1.4–2.1.9, 2.3.1,
2.3.4 and Remark 2.3.5(i), printed pp. 87–88, 91–92
(blueprint: def-trf-ordinary-resolution-rule).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A reduced finite-type rational scheme. The lift of the rational field only fixes
its size; no separation or dimension condition is imposed.
Source: ILO VIII, 2.3.10 (blueprint: def-trf-ordinary-resolution-rule). -/
structure RationalResolutionInput where
  scheme : Scheme.{u}
  structureMap : scheme ⟶ Spec (.of (ULift.{u} ℚ))
  reduced : IsReduced scheme
  finiteType : LocallyOfFiniteType structureMap
  quasiCompact : QuasiCompact structureMap

/-- A finite ordinary blowup tower with its centers. All transition maps are included
with their composition law, so that levelwise pullback and contraction are literal data.
The initial isomorphism expresses `S₀ = S` independently of chosen scheme models.
Source: ILO VIII, 2.1.4 (blueprint: def-trf-ordinary-resolution-rule). -/
structure OrdinaryBlowupTower (S : Scheme.{u}) where
  length : ℕ
  level : Fin (length + 1) → Scheme.{u}
  initial : level ⟨0, Nat.zero_lt_succ length⟩ ≅ S
  transition : ∀ (i j : Fin (length + 1)), i ≤ j → (level j ⟶ level i)
  transition_id : ∀ i, transition i i le_rfl = 𝟙 (level i)
  transition_comp : ∀ i j k (hij : i ≤ j) (hjk : j ≤ k),
    transition j k hjk ≫ transition i j hij = transition i k (hij.trans hjk)
  center : ∀ i : Fin length, (level i.castSucc).IdealSheafData
  blowupIso : ∀ i : Fin length, level i.succ ≅ (center i).blowup
  blowup_fac : ∀ i : Fin length, (blowupIso i).hom ≫ (center i).blowupMap =
    transition i.castSucc i.succ (le_of_lt i.castSucc_lt_succ)

/-- The structural map of a level of an ordinary tower to its input scheme.
Source: ILO VIII, 2.1.4 (blueprint: def-trf-ordinary-resolution-rule). -/
def OrdinaryBlowupTower.toBase {S : Scheme.{u}} (A : OrdinaryBlowupTower S)
    (i : Fin (A.length + 1)) : A.level i ⟶ S :=
  A.transition ⟨0, Nat.zero_lt_succ A.length⟩ i (Fin.zero_le i) ≫ A.initial.hom

/-- Resolution towers have coherent, nonempty, nowhere dense regular centers and regular
last level. Finite generation on every affine open is coherence here, since the input is
finite type over a field and ordinary blowups preserve the Noetherian property.
Source: ILO VIII, 2.3.1, 2.3.10 (blueprint: def-trf-ordinary-resolution-rule). -/
def OrdinaryBlowupTower.IsRegularResolution {S : Scheme.{u}} (A : OrdinaryBlowupTower S) :
    Prop :=
  (∀ i : Fin A.length, (A.center i).ofFiniteType ∧
    Set.Nonempty ((A.center i).support : Set (A.level i.castSucc)) ∧
    IsNowhereDense ((A.center i).support : Set (A.level i.castSucc)) ∧
    IsRegularScheme (A.center i).subscheme) ∧
  IsRegularScheme (A.level ⟨A.length, Nat.lt_succ_self A.length⟩)

/-- A contracted pullback comparison. `count i` is the number of nonempty stages before
level `i`; its fibers record the identity stages that have been removed. `retainedStage`
is the original ordered list of retained centers. The cartesian squares identify every
uncontracted pullback level, including repetitions, and the two ideal clauses keep exactly
the extended ideals and delete exactly the unit ideals. No pullback scheme is chosen.
Source: ILO VIII, 2.1.7–2.1.9, 2.3.4–2.3.5(i)
(blueprint: def-trf-ordinary-resolution-rule). -/
structure OrdinaryResolutionComparison {S T : Scheme.{u}} (h : T ⟶ S)
    (A : OrdinaryBlowupTower S) (B : OrdinaryBlowupTower T) where
  count : Fin (A.length + 1) →o Fin (B.length + 1)
  count_zero : count ⟨0, Nat.zero_lt_succ A.length⟩ = ⟨0, Nat.zero_lt_succ B.length⟩
  count_last : count ⟨A.length, Nat.lt_succ_self A.length⟩ =
    ⟨B.length, Nat.lt_succ_self B.length⟩
  retainedStage : Fin B.length ↪o Fin A.length
  count_before : ∀ k, count (retainedStage k).castSucc = k.castSucc
  count_after : ∀ k, count (retainedStage k).succ = k.succ
  deleted_level : ∀ i, i ∉ Set.range retainedStage → count i.succ = count i.castSucc
  levelMap : ∀ i, B.level (count i) ⟶ A.level i
  cartesian : ∀ i, IsPullback (levelMap i) (B.toBase (count i)) (A.toBase i) h
  naturality : ∀ i j (hij : i ≤ j),
    B.transition (count i) (count j) (count.monotone hij) ≫ levelMap i =
      levelMap j ≫ A.transition i j hij
  retained_ideal : ∀ k,
    (B.center k).comap (eqToHom (congrArg B.level (count_before k))) =
      (A.center (retainedStage k)).comap (levelMap (retainedStage k).castSucc)
  deleted_iff_unit : ∀ i,
    i ∉ Set.range retainedStage ↔ (A.center i).comap (levelMap i.castSucc) = ⊤

/-- One ordinary resolution rule, simultaneously on all reduced finite-type rational
schemes (including finite disjoint unions), with specified cartesian comparisons for all
smooth maps. Identity and composition hold on the contraction counts and on the actual
level maps, and surjective smooth maps delete no stages. The canonical comparisons are
characterized by their cartesian squares and compatibility with the tower maps and
extended ideals: ordinary blowups have no automorphisms over their base.
Source: ILO VIII, 2.3.4–2.3.5 and Theorem 2.3.10
(blueprint: def-trf-ordinary-resolution-rule). -/
structure SmoothFunctorialOrdinaryResolution where
  tower : ∀ S : RationalResolutionInput.{u}, OrdinaryBlowupTower S.scheme
  resolves : ∀ S, (tower S).IsRegularResolution
  comparison : ∀ (S T : RationalResolutionInput.{u}) (h : T.scheme ⟶ S.scheme)
    (_over : h ≫ S.structureMap = T.structureMap) [Smooth h],
    OrdinaryResolutionComparison h (tower S) (tower T)
  identity_count : ∀ S i, (comparison S S (𝟙 S.scheme) (by simp)).count i = i
  identity_map : ∀ S i,
    eqToHom (congrArg (tower S).level (identity_count S i).symm) ≫
      (comparison S S (𝟙 S.scheme) (by simp)).levelMap i = 𝟙 ((tower S).level i)
  composition_count : ∀ (S T U : RationalResolutionInput.{u})
    (h : T.scheme ⟶ S.scheme) (k : U.scheme ⟶ T.scheme)
    (overH : h ≫ S.structureMap = T.structureMap)
    (overK : k ≫ T.structureMap = U.structureMap) [Smooth h] [Smooth k] i,
    (comparison S U (k ≫ h) (by rw [Category.assoc, overH, overK])).count i =
      (comparison T U k overK).count ((comparison S T h overH).count i)
  composition_map : ∀ (S T U : RationalResolutionInput.{u})
    (h : T.scheme ⟶ S.scheme) (k : U.scheme ⟶ T.scheme)
    (overH : h ≫ S.structureMap = T.structureMap)
    (overK : k ≫ T.structureMap = U.structureMap) [Smooth h] [Smooth k] i,
    eqToHom (congrArg (tower U).level (composition_count S T U h k overH overK i)) ≫
      (comparison T U k overK).levelMap ((comparison S T h overH).count i) ≫
        (comparison S T h overH).levelMap i =
      (comparison S U (k ≫ h) (by rw [Category.assoc, overH, overK])).levelMap i
  surjective_no_deletion : ∀ (S T : RationalResolutionInput.{u})
    (h : T.scheme ⟶ S.scheme) (over : h ≫ S.structureMap = T.structureMap)
    [Smooth h] [Surjective h],
    Function.Surjective (comparison S T h over).retainedStage

end AlgebraicGeometry
