/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Homotopy
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
import WeilConjectures.AlgebraicGeometry.SplitTopDifferentialCancellationProperties
import WeilConjectures.AlgebraicGeometry.SplitTopDifferentialCancellationHomotopy

/-! # Cancelling one split top differential of a sheaf complex

## References

* [Stacks Project, Tag 068V](https://stacks.math.columbia.edu/tag/068V)
* [Stacks Project, Tag 00MT](https://stacks.math.columbia.edu/tag/00MT)
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules

private theorem truncLE_term_retract (S : Scheme.{u}) (B : CochainComplex S.Modules ℤ)
    (m : ℕ) (hsplit : IsSplitEpi (B.d (m : ℤ) (m + 1 : ℕ))) (n : ℤ) :
    Nonempty (Retract ((B.truncLE m).X n) (B.X n)) := by
  classical
  by_cases hlt : n < (m : ℤ)
  · exact ⟨(B.truncLEXIso m n hlt).retract⟩
  by_cases heq : n = (m : ℤ)
  · subst n
    let := hsplit
    let δ := B.d (m : ℤ) (m + 1 : ℕ)
    let p : B.X (m : ℤ) ⟶ B.X (m : ℤ) := 𝟙 _ - δ ≫ section_ δ
    have hp : p ≫ δ = 0 := by
      simp [p, Category.assoc]
    let r := B.liftCycles p (m + 1 : ℕ) (by simp) hp
    have hi : B.iCycles (m : ℤ) ≫ r = 𝟙 _ := by
      apply (cancel_mono (B.iCycles (m : ℤ))).1
      dsimp [r]
      rw [Category.assoc, B.liftCycles_i]
      dsimp [p, δ]
      simp [Preadditive.comp_sub, ← Category.assoc]
    exact ⟨(B.truncLEXIsoCycles m).retract.trans
      { i := B.iCycles (m : ℤ), r := r, retract := hi }⟩
  · have hz := (B.truncLE m).isZero_of_isStrictlyLE m n (by omega)
    exact ⟨{ i := 0, r := 0, retract := hz.eq_of_src _ _ }⟩

/-- One split top differential can be removed without changing homotopy type. -/
theorem exists_split_top_differential_cancellation (S : Scheme.{u})
    (B : CochainComplex S.Modules ℤ) (m : ℕ)
    (hBge : B.IsStrictlyGE 0) (hBle : B.IsStrictlyLE (m + 1 : ℕ))
    (hBflat : ∀ n : ℤ, (B.X n).IsFlatOver (𝟙 S))
    (hBqc : ∀ n : ℤ, (B.X n).IsQuasicoherent)
    (hBfp : ∀ n : ℤ, (B.X n).IsFinitePresentation)
    (hsplit : IsSplitEpi (B.d (m : ℤ) (m + 1 : ℕ))) :
    ∃ D : CochainComplex S.Modules ℤ,
      D.IsStrictlyGE 0 ∧ D.IsStrictlyLE m ∧
      (∀ n : ℤ, (D.X n).IsFlatOver (𝟙 S)) ∧
      (∀ n : ℤ, (D.X n).IsQuasicoherent) ∧
      (∀ n : ℤ, (D.X n).IsFinitePresentation) ∧
      Nonempty (HomotopyEquiv D B) := by
  let D := B.truncLE m
  let := hBge
  have hprops : ∀ n : ℤ, (D.X n).IsFlatOver (𝟙 S) ∧
      (D.X n).IsQuasicoherent ∧ (D.X n).IsFinitePresentation := by
    intro n
    obtain ⟨r⟩ := truncLE_term_retract S B m hsplit n
    exact split_top_differential_cancellation_properties S (D.X n) (B.X n) r
      (hBflat n) (hBqc n) (hBfp n)
  exact ⟨D, inferInstance, inferInstance, fun n ↦ (hprops n).1,
    fun n ↦ (hprops n).2.1, fun n ↦ (hprops n).2.2,
    split_top_differential_cancellation_homotopy S B m hBle hsplit⟩

end AlgebraicGeometry.Scheme.Modules
