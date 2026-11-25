/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.RingTheory.StrictlyStandardElement
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Kaehler.Basic
import WeilConjectures.RingTheory.SmoothFreeDifferentialsStrictlyStandardPower
/-!
# A common strictly standard power

If finitely many elements of a finitely presented algebra have smooth localizations with free
differentials, then a common positive power of all of them is strictly standard.

## References

* [Stacks, Tag 07EZ] (e)
-/
@[expose] public section
universe u v
namespace Algebra
/-- If `C` is a finitely presented `R`-algebra and `x : ι → C` is a finite family such that each
`C[1/xᵢ]` is smooth over `R` with free module of differentials, then there is `c ≥ 1` such that
every `xᵢ ^ c` is strictly standard. -/
theorem exists_common_strictlyStandard_power
    (R : Type u) (C : Type v) [CommRing R] [CommRing C] [Algebra R C]
    [FinitePresentation R C] {ι : Type} [Finite ι] (x : ι → C)
    (h : ∀ i, Smooth R (Localization.Away (x i)) ∧
      Module.Free (Localization.Away (x i))
        (KaehlerDifferential R (Localization.Away (x i)))) :
    ∃ c : ℕ, 1 ≤ c ∧ ∀ i, IsStrictlyStandardElement (R := R) (x i ^ c)  := by
  classical
  let _ := Fintype.ofFinite ι
  have hthreshold (i : ι) : ∃ e₀ : ℕ, 1 ≤ e₀ ∧ ∀ e : ℕ, e₀ ≤ e →
      IsStrictlyStandardElement (R := R) (x i ^ e) := by
    let S := Localization.Away (x i)
    let M := KaehlerDifferential R S
    let : Smooth R S := (h i).1
    let : Module.Free S M := (h i).2
    let b := Module.Free.chooseBasis S M
    let q := Finsupp.lcongr (σ := RingHom.id S) (σ_inv := RingHom.id S)
      (Fintype.equivFin (Module.Free.ChooseBasisIndex S M))
      (LinearEquiv.refl S S)
    let e : M ≃ₗ[S]
        (Fin (Fintype.card (Module.Free.ChooseBasisIndex S M)) →₀ S) :=
      b.repr.trans q
    apply smooth_free_differentials_strictly_standard_power R C (x i) 0
      (Fintype.card (Module.Free.ChooseBasisIndex S M))
    exact ⟨(LinearEquiv.prodUnique (R := S) (M := M)
      (M₂ := Fin 0 →₀ S)).trans e⟩
  choose e₀ he₀ hpow using hthreshold
  refine ⟨1 + ∑ i, e₀ i, Nat.le_add_right 1 _, fun i ↦ ?_⟩
  apply hpow i
  exact le_trans (Finset.single_le_sum (fun j _ ↦ Nat.zero_le (e₀ j))
    (Finset.mem_univ i)) (Nat.le_add_left _ _)
end Algebra
