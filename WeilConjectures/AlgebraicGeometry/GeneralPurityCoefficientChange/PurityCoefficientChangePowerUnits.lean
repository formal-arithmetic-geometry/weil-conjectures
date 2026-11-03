/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GeneralPurityCoefficientChange.PurityCoefficientChangeData
import WeilConjectures.CategoryTheory.ModuleObjects.Linear
import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapGlobalSections
import Mathlib.FieldTheory.Finite.Basic

/-! # Invertibility of the finite-base Tate scalar

Source: coefficient-change proof, the normalization by q^(-d).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory CategoryTheory.MonObj
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.PurityTransport
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.GeneralPurityCoefficientChange

/-- The positive Frobenius scalar is invertible for every native coefficient line.
Source: the coefficient normalization in coefficient change
(blueprint: lem-pur-coefficient-power-units).
Proof: the cardinality of the finite base field is a power of its characteristic p.
Since p differs from ell, this cardinality and all its powers are units in Z_ell,
by the norm criterion for units. Constants, inverse image from the point, and the
integral coefficient map carry these units to global coefficient sections. Their
action is a unit in the center of the module category. Its component on any line
is multiplication by q^d, since each map in this construction is a ring homomorphism. -/
theorem powerScalar_isIso (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
    [Finite k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (c : Coefficient ell) (X : Scheme.{u}) (d : ℕ) :
    IsIso (powerScalar ell k c X d) := by
  let := Fintype.ofFinite k
  obtain ⟨r, hp, hcard⟩ := FiniteField.card k (ringChar k)
  have hc : ell.Coprime (Nat.card k) := by
    rw [Nat.card_eq_fintype_card, hcard]
    exact ((Fact.out : ell.Prime).coprime_iff_not_dvd.mpr
      (fun h ↦ (Fact.out : ringChar k ≠ ell)
        ((Nat.prime_dvd_prime_iff_eq (Fact.out : ell.Prime) hp).mp h).symm)).pow_right _
  have hu : IsUnit (((Nat.card k) ^ d : ℕ) : ℤ_[ell]) := by
    apply PadicInt.isUnit_iff.mpr
    exact (PadicInt.norm_natCast_eq_one_iff).mpr (hc.pow_right d)
  have : PreservesColimitsOfSize.{0, 0} (upperStarFromPoint X) :=
    (pointUpperStarLowerStarAdjunction.comp
      (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X)))
      |>.leftAdjoint_preservesColimits
  have : PreservesBinaryBiproducts (upperStarFromPoint X) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  have : (upperStarFromPoint X).Additive :=
    Functor.additive_of_preservesBinaryBiproducts _
  let φ : ℤ_[ell] →+* Γ (condensedRingObj (c.obj ell) X) :=
    (Γ.map (coefficientMap (c.integralMap ell) X)).comp
      ((Γ.mapFunctor (upperStarFromPoint X)).comp
        (Profinite.continuousMapConstRingHom ℤ_[ell]))
  let ψ := (Mod.toCatCenter (condensedRingObj (c.obj ell) X)).comp φ
  let z : CatCenter (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (c.obj ell) X)) := ψ (((Nat.card k) ^ d : ℕ) : ℤ_[ell])
  let hz : IsIso z := (isUnit_iff_isIso z).mp (hu.map ψ)
  have h : IsIso (z.app (c.line ell X d)) := inferInstance
  have hn (n : ℕ) :
      (n : CatCenter (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (c.obj ell) X))).app (c.line ell X d) =
        n • 𝟙 (c.line ell X d) := by
    induction n with
    | zero =>
      simp only [Nat.cast_zero, CatCenter.app, NatTrans.app_zero, zero_nsmul]
    | succ n ih =>
      rw [Nat.cast_succ, CatCenter.app_add, ih, succ_nsmul]
      rfl
  have he : z.app (c.line ell X d) = powerScalar ell k c X d := by
    dsimp only [z]
    rw [map_natCast, hn]
    rfl
  rwa [he] at h

end AlgebraicGeometry.ProEtale.GeneralPurityCoefficientChange
