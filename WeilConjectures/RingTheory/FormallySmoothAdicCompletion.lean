/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.FormallySmoothAdic
public import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.AdicCompletion.Completeness

/-!
# Adic formal smoothness of the completion

If `S` is formally smooth over `R` for the `n`-adic topology and `n` is finitely generated,
then so is the `n`-adic completion of `S`, for the extended ideal.

## Implementation details

The projections `Ŝ → S ⧸ n ^ m` are surjective with kernel `(n Ŝ) ^ m` (Tag 05GG). A test map
`g : Ŝ → D ⧸ J` killing `(n Ŝ) ^ k` restricts to `S`, where it lifts to `f₀ : S → D`. Since
`J ^ 2 = 0`, `f₀` kills `n ^ (2 * k)` (Tag 07EC), so it factors through `S ⧸ n ^ (2 * k)`, and
composing with the projection gives the lift on `Ŝ`.

## References

* [Stacks, Tag 07ED], (1) implies (2), with the base ring discrete
* [Stacks, Tag 07EC]
* [Stacks, Tag 05GG]
-/

@[expose] public section

universe u v

namespace Algebra

/-- Formal smoothness for the `n`-adic topology passes to the completion when `n` is
finitely generated. The completion has its induced `R`-algebra structure, and its
ideal is the extension of `n` along the canonical map from `S`. -/
theorem FormallySmoothAdic.adicCompletion (R : Type u) (S : Type v)
    [CommRing R] [CommRing S] [Algebra R S] (n : Ideal S) (hn : n.FG)
    (h : FormallySmoothAdic R S n) :
    FormallySmoothAdic R (AdicCompletion n S)
      (n.map (algebraMap S (AdicCompletion n S))) := by
  intro D _ _ J hJ g hg
  obtain ⟨k, hk, hgk⟩ := hg
  let C := AdicCompletion n S
  let ι : S →ₐ[R] C := IsScalarTower.toAlgHom R S C
  let N : Ideal C := n.map (algebraMap S C)
  have hi (x : S) (hx : x ∈ n ^ k) : ι x ∈ N ^ k := by
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hx
  obtain ⟨f₀, hf₀⟩ := h J hJ (g.comp ι) ⟨k, hk, fun x hx ↦ hgk _ (hi x hx)⟩
  have hfJ : n ^ k ≤ J.comap f₀.toRingHom := by
    intro x hx
    have hz : (Ideal.Quotient.mkₐ R J) (f₀ x) = 0 := by
      have hxg := hgk (ι x) (hi x hx)
      have he := congrArg (fun q : S →ₐ[R] D ⧸ J => q x) hf₀
      exact he.symm ▸ hxg
    change f₀ x ∈ J
    exact Ideal.Quotient.eq_zero_iff_mem.mp hz
  have hfkill : ∀ x ∈ n ^ (k + k), f₀ x = 0 := by
    have hp : n ^ (k + k) ≤ (J ^ 2).comap f₀.toRingHom := by
      rw [pow_add, pow_two]
      exact (Ideal.mul_mono hfJ hfJ).trans (Ideal.le_comap_mul _)
    rw [hJ] at hp
    exact fun x hx ↦ hp hx
  let π : C →ₐ[R] S ⧸ n ^ (k + k) :=
    (AdicCompletion.evalₐ n (k + k)).restrictScalars R
  let f : C →ₐ[R] D := (Ideal.Quotient.liftₐ (n ^ (k + k)) f₀ hfkill).comp π
  have hker (m : ℕ) :
      RingHom.ker (AdicCompletion.evalₐ n m).toRingHom = N ^ m := by
    ext x
    rw [RingHom.mem_ker]
    rw [← Ideal.map_pow]
    rw [← Submodule.restrictScalars_mem S, ← Ideal.smul_top_eq_map,
      AdicCompletion.pow_smul_top_eq_ker_eval hn]
    change (AdicCompletion.evalₐ n m) x = 0 ↔ AdicCompletion.eval n S m x = 0
    let e := Ideal.quotientEquivAlgOfEq S
      (show (n ^ m • ⊤ : Ideal S) = n ^ m by simp)
    change e (AdicCompletion.eval n S m x) = 0 ↔ AdicCompletion.eval n S m x = 0
    exact map_eq_zero_iff e e.injective
  refine ⟨f, ?_⟩
  ext x
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (π x)
  have hπa : π (ι a) = Ideal.Quotient.mk (n ^ (k + k)) a :=
    AdicCompletion.evalₐ_of n (k + k) a
  have hd : x - ι a ∈ N ^ (k + k) := by
    rw [← hker, RingHom.mem_ker]
    change π (x - ι a) = 0
    rw [map_sub, hπa, ha, sub_self]
  have hgd : g (x - ι a) = 0 :=
    hgk _ ((Ideal.pow_le_pow_right (Nat.le_add_right k k)) hd)
  have hga : g x = g (ι a) := by
    simpa only [map_sub, sub_eq_zero] using hgd
  have hfa : f x = f₀ a := by
    change Ideal.Quotient.liftₐ (n ^ (k + k)) f₀ hfkill (π x) = f₀ a
    rw [← ha]
    rfl
  change Ideal.Quotient.mkₐ R J (f x) = g x
  rw [hfa, hga]
  exact DFunLike.congr_fun hf₀ a

end Algebra
