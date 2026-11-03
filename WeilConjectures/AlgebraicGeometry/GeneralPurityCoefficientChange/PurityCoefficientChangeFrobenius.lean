/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GeneralPurityCoefficientChange.PurityCoefficientChangeData
import WeilConjectures.CategoryTheory.PurityCoefficientChangeInverseScalar
import Mathlib.CategoryTheory.Adjunction.Additive

/-! # Frobenius scalar equations from invertibility of the positive scalar

Source: the canonical Tate source identifications in coefficient change.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option linter.style.haveILetI false
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.PurityTransport
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.GeneralPurityCoefficientChange
variable (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]

omit [Field k] in
private theorem derivedPower_eq (c : Coefficient ell) (X : Scheme.{u}) (d : ℕ) :
    (shiftFunctor (c.derived ell X) (2 * (d : ℤ))).map
        ((DerivedCategory.singleFunctor _ 0).map (powerScalar ell k c X d)) =
      ((Nat.card k) ^ d) • 𝟙 (c.derivedLine ell X d) := by
  let F := DerivedCategory.singleFunctor
    (ModuleRingedComparison.internalModules (c.obj ell) X) 0
  let S := shiftFunctor (c.derived ell X) (2 * (d : ℤ))
  have hF := F.map_id (c.line ell X d)
  have hS := S.map_id (F.obj (c.line ell X d))
  change S.map (F.map (((Nat.card k) ^ d) • 𝟙 (c.line ell X d))) = _
  rw [F.map_nsmul, hF, S.map_nsmul, hS]
  rfl

omit [Field k] in
private theorem derivedPower_isIso (c : Coefficient ell) (X : Scheme.{u}) (d : ℕ)
    [IsIso (powerScalar ell k c X d)] :
    IsIso (((Nat.card k) ^ d) • 𝟙 (c.derivedLine ell X d)) := by
  have h : IsIso ((shiftFunctor (c.derived ell X) (2 * (d : ℤ))).map
      ((DerivedCategory.singleFunctor _ 0).map (powerScalar ell k c X d))) :=
    inferInstance
  rwa [derivedPower_eq] at h

omit [Field k] in
private theorem derivedTau_eq (c : Coefficient ell) (X : Scheme.{u}) (d : ℕ)
    [IsIso (powerScalar ell k c X d)] :
    derivedTau ell k c X d = Ring.inverse (M₀ := End (c.derivedLine ell X d))
      (((Nat.card k) ^ d) • (1 : End (c.derivedLine ell X d))) := by
  letI := derivedPower_isIso ell k c X d
  unfold derivedTau tau
  rw [ringInverse_eq_categoricalInv, ringInverse_eq_categoricalInv]
  rw [Functor.map_inv, Functor.map_inv]
  dsimp only [Coefficient.derivedLine]
  apply IsIso.inv_eq_inv.mpr
  exact derivedPower_eq ell k c X d

omit [Field k] in
/-- The inverse q^d scalar automatically commutes with the source comparisons.
Source: canonical Tate normalization in det-sp-purity-coefficient-change
(blueprint: lem-pur-coefficient-frobenius-from-units).
Proof: the positive scalar is invertible by assumption. Its ring inverse equals
its categorical inverse. Derived-single and shift preserve both its scalar formula
and its inverse. Additivity of scalar extension and inverse image preserves the
positive scalar. Every arrow commutes with multiples of identities; cancellation
of the positive target scalar proves the inverse commutation equations. This
argument applies to the specified scalar-line and pullback-line arrows themselves. -/
theorem frobenius_of_powers (P : PurityCoefficientChange.Coordinates.{u} ell)
    (hp : Finite k → ∀ (c : Coefficient ell) (X : Scheme.{u}) (d : ℕ),
      IsIso (powerScalar ell k c X d)) : FrobeniusCompatible ell k P := by
  intro hk
  refine ⟨hp hk, ?_, ?_⟩
  · intro c c' a ha X d
    letI := hp hk c X d
    letI := hp hk c' X d
    letI := derivedPower_isIso ell k c X d
    letI := derivedPower_isIso ell k c' X d
    letI : (scalarSixChange a X).Additive :=
      (Mod.derivedExtendMapDerivedCategoryAdjunction
        (coefficientMap (Λ := c.obj ell) (Λ' := c'.obj ell) a.hom.hom X)).left_adjoint_additive
    rw [derivedTau_eq, derivedTau_eq]
    exact map_inverse_nsmul_id_natural (scalarSixChange a X) ((Nat.card k) ^ d)
      (c.derivedLine ell X d) (c'.derivedLine ell X d)
      (scalarLineMap ell a X d ((P.line a ha X).power d))
  · intro c X Y f p d
    letI := hp hk c Y d
    letI := hp hk c X d
    letI : IsIso (((Nat.card k) ^ d) • 𝟙 (c.line ell Y d)) := hp hk c Y d
    letI : IsIso (((Nat.card k) ^ d) • 𝟙 (c.line ell X d)) := hp hk c X d
    exact map_inverse_nsmul_id_natural (CondensedRing.upperStar (c.obj ell) f)
      ((Nat.card k) ^ d) (c.line ell Y d) (c.line ell X d) (p.power d).hom

end AlgebraicGeometry.ProEtale.GeneralPurityCoefficientChange
