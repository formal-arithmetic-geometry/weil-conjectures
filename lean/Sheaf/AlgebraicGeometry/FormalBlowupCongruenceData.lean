/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q20
-/
module

public import Sheaf.AlgebraicGeometry.NoetherianAdicFormalSystem
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.Algebra.Ring.NonZeroDivisors

/-! # Congruence and bounded centers in adic formal systems

Source: Temkin, Non-embedded Desingularization, proof of Lemma 3.3.3, printed p.23,
and the finite iteration of that chart calculation
(blueprint: def-per-formal-blowup-congruence-data).

Reduction of order m is the scheme at index m-1. At order zero there is no condition,
corresponding to the empty reduction modulo the unit ideal. The existing formal
systems and formal blowups are used throughout.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AdicFormal

/-- Equality modulo the mth power of the specified ideal of definition, including m=0.
Source: Temkin, Lemma 3.3.3 (blueprint: def-per-formal-blowup-congruence-data). -/
def Congruent {F G : ℕ ⥤ Scheme.{u}} (f g : G ⟶ F) (m : ℕ) : Prop :=
  ∀ n : ℕ, n + 1 ≤ m → f.app n = g.app n

/-- An adic morphism identifies the specified ideal of definition with its extension:
all transition squares of infinitesimal thickenings are cartesian.
Source: Temkin §2.4.4 (blueprint: def-per-formal-blowup-congruence-data). -/
def IsAdicMap {F G : ℕ ⥤ Scheme.{u}} (f : G ⟶ F) : Prop :=
  ∀ (n k : ℕ) (h : n ≤ k),
    IsPullback (G.map (homOfLE h)) (f.app n) (f.app k) (F.map (homOfLE h))

/-- A center containing the eth power of the ideal of definition, on every formal affine.
The ordinary chart ideal is retained through its actual extensions to all thickenings.
Source: Temkin, Lemma 3.3.3 (blueprint: def-per-formal-blowup-congruence-data). -/
def HasCenterExponent (F : ℕ ⥤ Scheme.{u})
    (J : ∀ n : ℕ, (F.obj n).IdealSheafData) (e : ℕ) : Prop :=
  ∀ a : AffineChart F, ∃ H : Ideal a.ring,
    a.ideal ^ e ≤ H ∧ ∀ n : ℕ,
      (J n).comap (a.map.app n) =
        (affineIdeal a.ring H).comap (inclusion (affineIdeal a.ring a.ideal) n)

/-- The distinguished ideal is locally principal with a non-zero-divisor generator.
The chart is allowed to depend on the point; no chosen atlas restricts the assertion.
Source: Temkin §§2.4.11, 3.3.3 (blueprint: def-per-formal-blowup-congruence-data). -/
def HasPrincipalRegularCharts (F : ℕ ⥤ Scheme.{u}) : Prop :=
  ∀ (n : ℕ) (x : F.obj n), ∃ (a : AffineChart F) (π : a.ring),
    π ∈ nonZeroDivisors a.ring ∧ a.ideal = Ideal.span {π} ∧
      ∃ y : (completion (affineIdeal a.ring a.ideal)).obj n, a.map.app n y = x

/-- A map of affine formal systems inducing the specified ring homomorphism.
The equations into Spec fix all finite-order maps uniquely.
Source: Temkin, Lemma 3.3.3 (blueprint: def-per-formal-blowup-congruence-data). -/
def InducesRingHom {A B : CommRingCat.{u}} (K : Ideal A) (L : Ideal B)
    (φ : A →+* B)
    (f : completion (affineIdeal B L) ⟶ completion (affineIdeal A K)) : Prop :=
  ∀ n : ℕ, f.app n ≫ inclusion (affineIdeal A K) n =
    inclusion (affineIdeal B L) n ≫ Spec.map (CommRingCat.ofHom φ)

/-- The actual completion of the ordinary blowup along H, along the extended ideal K.
This is the existing completion construction applied to the existing global blowup.
Source: Temkin §§2.4.5, 3.3.3 (blueprint: def-per-formal-blowup-congruence-data). -/
abbrev affineBlowupSystem (A : CommRingCat.{u}) (K H : Ideal A) :=
  completion ((affineIdeal A K).comap (affineIdeal A H).blowupMap)

/-- The completed blowup projection is fixed by its equations into the ordinary base.
Source: Temkin §2.4.5 (blueprint: def-per-formal-blowup-congruence-data). -/
def IsAffineBlowupProjection (A : CommRingCat.{u}) (K H : Ideal A)
    (b : affineBlowupSystem A K H ⟶ completion (affineIdeal A K)) : Prop :=
  ∀ n : ℕ, b.app n ≫ inclusion (affineIdeal A K) n =
    inclusion ((affineIdeal A K).comap (affineIdeal A H).blowupMap) n ≫
      (affineIdeal A H).blowupMap

/-- A finite tower of the existing formal blowups, with each exponent and center retained.
The empty center is the unit ideal and may have exponent zero; length zero is allowed.
Source: Temkin §§2.2.1, 3.3.5 (blueprint: def-per-formal-blowup-congruence-data). -/
structure PrecisionTower (r : ℕ) where
  level : Fin (r + 1) → (ℕ ⥤ Scheme.{u})
  noetherian : ∀ i : Fin (r + 1), IsNoetherian (level i)
  principal : ∀ i : Fin (r + 1), HasPrincipalRegularCharts (level i)
  arrow : ∀ i : Fin r, level i.succ ⟶ level i.castSucc
  center : ∀ (i : Fin r) (n : ℕ), ((level i.castSucc).obj n).IdealSheafData
  exponent : Fin r → ℕ
  bound : ∀ i : Fin r, HasCenterExponent (level i.castSucc) (center i) (exponent i)
  blowup : ∀ i : Fin r, IsBlowup (arrow i) (center i)

/-- A map of two towers identifies every successive center and respects the blowup arrows.
Source: Temkin §3.3.5 (blueprint: def-per-formal-blowup-congruence-data). -/
structure PrecisionTowerMap {r : ℕ} (S T : PrecisionTower.{u} r) where
  map : ∀ i : Fin (r + 1), S.level i ⟶ T.level i
  adic : ∀ i : Fin (r + 1), IsAdicMap (map i)
  arrows : ∀ i : Fin r, map i.succ ≫ T.arrow i = S.arrow i ≫ map i.castSucc
  centers : ∀ (i : Fin r) (n : ℕ),
    (T.center i n).comap ((map i.castSucc).app n) = S.center i n

/-- Levelwise cartesian flat formal pullback of a tower. This is a completed formal
pullback, not an ordinary tensor product of complete rings.
Source: Temkin §§2.4.4--2.4.8 (blueprint: def-per-formal-blowup-congruence-data). -/
def PrecisionTowerMap.IsFlatPullback {r : ℕ} {S T : PrecisionTower.{u} r}
    (h : PrecisionTowerMap S T) : Prop :=
  (∀ (i : Fin (r + 1)) (n : ℕ), Flat ((h.map i).app n)) ∧
    ∀ (i : Fin r) (n : ℕ), IsPullback ((S.arrow i).app n)
      ((h.map i.succ).app n) ((h.map i.castSucc).app n) ((T.arrow i).app n)

end AlgebraicGeometry.AdicFormal
