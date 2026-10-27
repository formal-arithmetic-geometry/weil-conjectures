/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q106
-/
module

public import Sheaf.AlgebraicGeometry.ElkikPairGeometry

/-! # Comparisons at common precision of Elkik resolution towers

Source: Temkin, Non-embedded Desingularization, §§3.3.4--3.3.8 and 3.4.1
(blueprint: def-per-elkik-tower-comparison).

Finite fibres of blowups are centered diagrams, and are not asserted to be blowups
of the finite fibres. Completion is represented by all compatible infinitesimal orders.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Elkik

/-- The completion diagram of an ordinary level, along the extended base ideal.
Source: Temkin §§3.3.5, 3.4.1 (blueprint: def-per-elkik-tower-comparison). -/
def levelDiagram {X : Pair.{u}} (A : OrdinaryBlowupTower X.scheme)
    (i : Fin (A.length + 1)) : ℕ ⥤ Scheme.{u} :=
  adicThickeningDiagram (X.ideal.comap (A.toBase i))

/-- The actual structural maps on every finite fibre of a level.
Source: Temkin §§3.3.5, 3.4.1 (blueprint: def-per-elkik-tower-comparison). -/
def levelToBase {X : Pair.{u}} (A : OrdinaryBlowupTower X.scheme)
    (i : Fin (A.length + 1)) : levelDiagram A i ⟶ adicThickeningDiagram X.ideal :=
  adicThickeningMap (A.toBase i) X.ideal (X.ideal.comap (A.toBase i)) le_rfl

/-- The actual transition map restricted to equal precision.
Source: Temkin §3.3.5 (blueprint: def-per-elkik-tower-comparison). -/
def levelTransition {X : Pair.{u}} (A : OrdinaryBlowupTower X.scheme)
    (i j : Fin (A.length + 1)) (hij : i ≤ j) :
    levelDiagram A j ⟶ levelDiagram A i :=
  adicThickeningMap (A.transition i j hij)
    (X.ideal.comap (A.toBase i)) (X.ideal.comap (A.toBase j)) (by
      rw [← Scheme.IdealSheafData.comap_comp]
      have h : A.transition i j hij ≫ A.toBase i = A.toBase j := by
        dsimp [OrdinaryBlowupTower.toBase]
        rw [← Category.assoc, A.transition_comp]
      rw [h])

/-- The center ideal at order t, retaining its scheme structure.
Source: Temkin §§3.3.5--3.3.7 (blueprint: def-per-elkik-tower-comparison). -/
def centerAt {X : Pair.{u}} (A : OrdinaryBlowupTower X.scheme)
    (i : Fin A.length) (t : ℕ) : ((levelDiagram A i.castSucc).obj t).IdealSheafData :=
  (A.center i).comap ((X.ideal.comap (A.toBase i.castSucc)) ^ t).subschemeι

/-- The levels of the staggered restriction, with their actual unequal thicknesses.
No off-center isomorphism is asserted for the unequal-thickness arrows.
Source: Temkin §§3.3.5--3.3.6 (blueprint: def-per-elkik-tower-comparison). -/
def staggeredLevel {X : Pair.{u}} (A : OrdinaryBlowupTower X.scheme)
    (n : ℕ) (i : Fin (A.length + 1)) : Scheme.{u} :=
  (levelDiagram A i).obj (n * (n - i.val))

/-- The ordered center subschemes in a staggered restriction, recorded by their ideals.
Source: Temkin §3.3.5 (blueprint: def-per-elkik-tower-comparison). -/
def staggeredCenter {X : Pair.{u}} (A : OrdinaryBlowupTower X.scheme)
    (n : ℕ) (i : Fin A.length) : (staggeredLevel A n i.castSucc).IdealSheafData :=
  centerAt A i (n * (n - i.val))

/-- The actual centered arrows of the staggered diagram: first include the thinner
fibre, then restrict the ordinary transition at the target precision.
Source: Temkin §3.3.5 (blueprint: def-per-elkik-tower-comparison). -/
def staggeredTransition {X : Pair.{u}} (A : OrdinaryBlowupTower X.scheme)
    (n : ℕ) (i j : Fin (A.length + 1)) (hij : i ≤ j) :
    staggeredLevel A n j ⟶ staggeredLevel A n i :=
  (levelDiagram A j).map
      (homOfLE (Nat.mul_le_mul_left n (Nat.sub_le_sub_left hij n))) ≫
    (levelTransition A i j hij).app (n * (n - i.val))

/-- A pullback-and-delete-empty comparison on a set of common precisions. The level
squares are cartesian; centers and order are preserved; only unit ideals are deleted.
The final equation says that the level maps at different precisions restrict to one
another. It imposes no uniqueness on a finite fibre's automorphisms.
Source: Temkin §§3.3.5--3.3.8, common-precision formulation
(blueprint: def-per-elkik-tower-comparison). -/
structure Comparison {X Y : Pair.{u}} (A : OrdinaryBlowupTower X.scheme)
    (B : OrdinaryBlowupTower Y.scheme) (S : Set ℕ)
    (h : ∀ (t : ℕ) (_ht : t ∈ S), Y.fibre t ⟶ X.fibre t) where
  count : Fin (A.length + 1) →o Fin (B.length + 1)
  count_zero : count 0 = 0
  count_last : count ⟨A.length, Nat.lt_succ_self _⟩ = ⟨B.length, Nat.lt_succ_self _⟩
  retainedStage : Fin B.length ↪o Fin A.length
  count_before : ∀ k, count (retainedStage k).castSucc = k.castSucc
  count_after : ∀ k, count (retainedStage k).succ = k.succ
  deleted_level : ∀ i, i ∉ Set.range retainedStage → count i.succ = count i.castSucc
  levelMap : ∀ (t : ℕ) (_ht : t ∈ S) (i : Fin (A.length + 1)),
    (levelDiagram B (count i)).obj t ⟶ (levelDiagram A i).obj t
  cartesian : ∀ (t : ℕ) (ht : t ∈ S) (i : Fin (A.length + 1)),
    IsPullback (levelMap t ht i) ((levelToBase B (count i)).app t)
      ((levelToBase A i).app t) (h t ht)
  naturality : ∀ (t : ℕ) (ht : t ∈ S) (i j : Fin (A.length + 1)) (hij : i ≤ j),
    (levelTransition B (count i) (count j) (count.monotone hij)).app t ≫ levelMap t ht i =
      levelMap t ht j ≫ (levelTransition A i j hij).app t
  retained_ideal : ∀ (t : ℕ) (ht : t ∈ S) (k : Fin B.length),
    (centerAt B k t).comap (eqToHom
      (congrArg (fun j ↦ (levelDiagram B j).obj t) (count_before k))) =
      (centerAt A (retainedStage k) t).comap (levelMap t ht (retainedStage k).castSucc)
  deleted_iff_unit : ∀ (t : ℕ) (ht : t ∈ S) (i : Fin A.length),
    i ∉ Set.range retainedStage ↔
      (centerAt A i t).comap (levelMap t ht i.castSucc) = ⊤
  precision : ∀ (s t : ℕ) (hs : s ∈ S) (ht : t ∈ S) (hst : s ≤ t)
    (i : Fin (A.length + 1)),
    (levelDiagram B (count i)).map (homOfLE hst) ≫ levelMap t ht i =
      levelMap s hs i ≫ (levelDiagram A i).map (homOfLE hst)

/-- Comparisons below T induced by a specified map at precision m. The base equations
uniquely characterize each restricted h_t because the thickening inclusions are monic.
Source: Temkin Proposition 3.3.5 and the common-precision restriction of §§3.3.5--3.3.7
(blueprint: def-per-elkik-tower-comparison). -/
structure FiniteComparison {X Y : Pair.{u}} (A : OrdinaryBlowupTower X.scheme)
    (B : OrdinaryBlowupTower Y.scheme) (m T : ℕ)
    (h : Y.fibre m ⟶ X.fibre m) where
  baseMap : ∀ (t : ℕ) (_ht : t ∈ Set.Icc 1 T), Y.fibre t ⟶ X.fibre t
  base_fac : ∀ (t : ℕ) (ht : t ∈ Set.Icc 1 T) (htm : t ≤ m),
    baseMap t ht ≫ (adicThickeningDiagram X.ideal).map (homOfLE htm) =
      (adicThickeningDiagram Y.ideal).map (homOfLE htm) ≫ h
  comparison : Comparison A B (Set.Icc 1 T) baseMap

/-- A map of completed pairs, in infinitesimal-system coordinates. Compatible maps
at all orders determine the formal ringed-space map, with inverse-limit structure sheaf.
Ideal preservation is equality, not radical equality or an arbitrary continuity bound.
Source: Temkin §§2.4.1--2.4.5, 3.4.1
(blueprint: def-per-elkik-tower-comparison). -/
structure CompletedMap (X Y : Pair.{u}) where
  map : adicThickeningDiagram Y.ideal ⟶ adicThickeningDiagram X.ideal
  ideal_eq : ∀ t : ℕ, (X.fibreIdeal t).comap (map.app t) = Y.fibreIdeal t

/-- The actual morphism of completed ringed spaces associated to a compatible family.
Source: Temkin §§2.4.1--2.4.5 (blueprint: def-per-elkik-tower-comparison). -/
def CompletedMap.formalMap {X Y : Pair.{u}} (h : CompletedMap X Y) :
    adicFormalCompletion Y.ideal ⟶ adicFormalCompletion X.ideal :=
  colimMap (Functor.whiskerRight h.map
    (Scheme.forgetToLocallyRingedSpace ⋙ LocallyRingedSpace.forgetToSheafedSpace))

/-- Regularity of the completed ring maps on affine charts. The existing predicate
uses the actual homomorphisms on sections of complete formal affines.
Source: Temkin §2.4.12, §3.4.1 (blueprint: def-per-elkik-tower-comparison). -/
def CompletedMap.IsRegular {X Y : Pair.{u}} (h : CompletedMap X Y) : Prop :=
  IsRegularOnAdicFormalAffines h.formalMap

/-- A centered completed-tower comparison is the compatible comparison at every positive
order. The same contraction count and ordered retained stages are used at all orders.
Thus every completed level and every full completed center ideal is compared.
Source: Temkin §3.4.1 (blueprint: def-per-elkik-tower-comparison). -/
def CompletedComparison {X Y : Pair.{u}} (A : OrdinaryBlowupTower X.scheme)
    (B : OrdinaryBlowupTower Y.scheme) (h : CompletedMap X Y) :=
  Comparison A B {t | 1 ≤ t} (fun t _ht ↦ h.map.app t)

/-- A fixed identification of completed pairs. There is no compatibility condition
with either field of definition.
Source: Temkin Proposition 3.3.5, §3.4.1 (blueprint: def-per-elkik-tower-comparison). -/
structure CompletedIso (X Y : Pair.{u}) where
  iso : adicThickeningDiagram Y.ideal ≅ adicThickeningDiagram X.ideal
  ideal_eq : ∀ t : ℕ, (X.fibreIdeal t).comap (iso.hom.app t) = Y.fibreIdeal t

/-- Forget only the inverse of the fixed completed-pair identification.
Source: Temkin §3.4.1 (blueprint: def-per-elkik-tower-comparison). -/
def CompletedIso.toMap {X Y : Pair.{u}} (e : CompletedIso X Y) : CompletedMap X Y :=
  ⟨e.iso.hom, e.ideal_eq⟩

end AlgebraicGeometry.Elkik
