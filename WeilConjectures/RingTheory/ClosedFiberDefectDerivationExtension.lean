/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.FormallySmoothAdic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Noetherian.Defs
import WeilConjectures.RingTheory.ClosedFiberDerivationExtension
import Mathlib.Tactic.LinearCombination

/-! # Extending a parameter-vanishing defect derivation

Let `R → T` be a local map with formally smooth closed fibre and `f : T → D` a ring map lifting
an `R`-algebra map `T → D ⧸ J` along a square-zero ideal `J`. If `f` agrees with the structure map
on generators of the maximal ideal of `R`, the defect `f ∘ (R → T) - (R → D)` extends to a
derivation `T → J`.

## Implementation details

The defect is a derivation `R → J` vanishing on the generators `t`, hence on `m_R`; since `J` is
a vector space over the residue field of `T`, it factors through the differentials of the residue
field of `R`. Formal smoothness of the closed fibre makes the base-field differential map
injective after tensoring with the residue field of `T`, and the functional extends along this
injection (`Derivation.exists_extension_of_closedFiber`).

## References

* [Stacks, Tag 07NQ]
* [Stacks, Tag 07EL]
-/

@[expose] public section

universe u v w

open IsLocalRing

namespace Algebra

/-- If the closed fibre of `R → T` is formally smooth, `J` is a square-zero ideal of `D`, and
`f : T → D` lifts an `R`-algebra map `T → D ⧸ J`, agrees with `R → D` on the generators `t` of the
maximal ideal of `R`, and is such that `m_T` acts trivially on `J`, then there is an additive map
`δ : T → J` satisfying the Leibniz rule for the `T`-action through `f` and restricting on `R` to
the defect `f ∘ (R → T) - (R → D)`. -/
theorem exists_closedFiber_defect_derivation
    (R : Type u) (T : Type v) [CommRing R] [CommRing T]
    [IsLocalRing R] [IsLocalRing T] [IsNoetherianRing T]
    [Algebra R T] [IsLocalHom (algebraMap R T)]
    (t : List R) (ht : Ideal.span {r | r ∈ t} = maximalIdeal R) :
    let L : Ideal T := (maximalIdeal R).map (algebraMap R T)
    letI : Algebra (R ⧸ maximalIdeal R) (T ⧸ L) :=
      Ideal.Quotient.algebraQuotientOfLEComap (Ideal.le_comap_map :
        maximalIdeal R ≤ L.comap (algebraMap R T))
    FormallySmoothAdic (R ⧸ maximalIdeal R) (T ⧸ L)
        ((maximalIdeal T).map (Ideal.Quotient.mk L)) →
    ∀ (D : Type w) [CommRing D] [Algebra R D] (J : Ideal D), J ^ 2 = ⊥ →
      ∀ (g : T →ₐ[R] D ⧸ J) (f : T →+* D),
      (Ideal.Quotient.mk J).comp f = g.toRingHom →
      (∀ r ∈ t, f (algebraMap R T r) = algebraMap R D r) →
      (∀ x ∈ maximalIdeal T, ∀ d : D, Ideal.Quotient.mk J d = g x →
        ∀ j ∈ J, d * j = 0) →
      ∃ δ : T →+ D, δ 1 = 0 ∧ (∀ x, δ x ∈ J) ∧
        (∀ x z, δ (x * z) = f x * δ z + f z * δ x) ∧
        ∀ r : R, δ (algebraMap R T r) =
          f (algebraMap R T r) - algebraMap R D r := by
  intro L hclosed D _ _ J hJ g f hf htAgree hann
  have hfq (x : T) : Ideal.Quotient.mk J (f x) = g x :=
    RingHom.congr_fun hf x
  have hmem (r : R) : f (algebraMap R T r) - algebraMap R D r ∈ J := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub, hfq, g.commutes]
    exact sub_self _
  have hmul (a b : D) (ha : a ∈ J) (hb : b ∈ J) : a * b = 0 := by
    have hab : a * b ∈ J ^ 2 := by
      rw [pow_two]
      exact Ideal.mul_mem_mul ha hb
    simpa [hJ] using hab
  -- Use the lift action, rather than the original R-algebra action, on J.
  let : Algebra T D := f.toAlgebra
  let : SMul R D := ⟨fun r x ↦ f (algebraMap R T r) * x⟩
  let : Module T J := Module.compHom J f
  let : Module R J := Module.compHom J (algebraMap R T)
  let dadd : R →+ J :=
    { toFun := fun r ↦ ⟨f (algebraMap R T r) - algebraMap R D r, hmem r⟩
      map_zero' := by apply Subtype.ext; simp
      map_add' := by intro a b; apply Subtype.ext; simp [sub_add_sub_comm] }
  have hdLeibniz (a b : R) : dadd (a * b) = a • dadd b + b • dadd a := by
    apply Subtype.ext
    change f (algebraMap R T (a * b)) - algebraMap R D (a * b) =
      f (algebraMap R T a) * (f (algebraMap R T b) - algebraMap R D b) +
      f (algebraMap R T b) * (f (algebraMap R T a) - algebraMap R D a)
    have hab := hmul _ _ (hmem a) (hmem b)
    simp only [map_mul]
    linear_combination -hab
  let d : Derivation ℤ R J := Derivation.mk' dadd.toIntLinearMap hdLeibniz
  have hannT (x : T) (hx : x ∈ maximalIdeal T) (j : J) : x • j = 0 := by
    apply Subtype.ext
    exact hann x hx (f x) (hfq x) j j.property
  have hannR (r : R) (hr : r ∈ maximalIdeal R) (j : J) : r • j = 0 := by
    exact hannT (algebraMap R T r) (by
      rw [← maximalIdeal_comap (algebraMap R T)] at hr
      exact hr) j
  have hdt (r : R) (hr : r ∈ t) : d r = 0 := by
    apply Subtype.ext
    exact sub_eq_zero.mpr (htAgree r hr)
  have hkill (r : R) (hr : r ∈ maximalIdeal R) : d r = 0 := by
    rw [← ht] at hr
    induction hr using Submodule.span_induction with
    | mem r hr => exact hdt r hr
    | zero => exact map_zero d
    | add a b ha hb hda hdb => simp only [map_add, hda, hdb, add_zero]
    | smul a b hb hdb =>
      change d (a * b) = 0
      rw [d.leibniz, hdb, smul_zero, zero_add]
      exact hannR b (by rw [← ht]; exact hb) (d a)
  obtain ⟨d', hd'⟩ := Derivation.exists_extension_of_closedFiber R T hclosed J hannT d hkill
  let δ : T →+ D := J.subtype.toAddMonoidHom.comp d'.toLinearMap.toAddMonoidHom
  refine ⟨δ, ?_, ?_, ?_, ?_⟩
  · change (d' 1 : D) = 0
    rw [d'.map_one_eq_zero]
    rfl
  · intro x
    exact (d' x).property
  · intro x z
    exact congrArg Subtype.val (d'.leibniz x z)
  · intro r
    exact congrArg Subtype.val (hd' r)

end Algebra
