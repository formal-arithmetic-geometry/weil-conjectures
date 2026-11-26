/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.FormallySmoothAdic
public import Mathlib.Algebra.Module.ULift
import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Universe transport for adic formal smoothness

Raising the universe of an algebra with `ULift` preserves adic formal smoothness.

## Implementation details

Given a test problem `g : ULift S → D ⧸ J`, choose representatives in `D` of the images of
elements of `S` and let `T` be the image of the polynomial algebra `R[X_s | s ∈ S]` under
evaluation at these representatives; it lives in universe `max u v` and embeds into `D`. The
lifting problem restricts to `T` with the square-zero ideal `J ∩ T`, where the original lifting
property applies. No nontriviality assumptions are needed.

## References

* [Stacks, Tag 07EB]
* [Stacks, Tag 07NI]
* [Stacks, Tag 07NR]
* [Stacks, Tag 07NS]
-/

@[expose] public section

universe u v w

namespace Algebra

/-- Raising the universe of an algebra preserves its adic lifting property: if `S` is
formally smooth over `R` for the `n`-adic topology, then so is `ULift S` for the transported
ideal. -/
theorem formallySmoothAdic_ulift
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (n : Ideal S) (h : FormallySmoothAdic R S n) :
    FormallySmoothAdic R (ULift.{w} S)
      (n.map (ULift.ringEquiv : ULift.{w} S ≃+* S).symm.toRingHom) := by
  classical
  intro D _ _ J hJ g hg
  let e : ULift.{w} S ≃ₐ[R] S := ULift.algEquiv
  let g₀ : S →ₐ[R] D ⧸ J := g.comp e.symm.toAlgHom
  choose r hr using (fun s : S ↦ Ideal.Quotient.mk_surjective (g₀ s))
  let q : MvPolynomial S R →ₐ[R] D := MvPolynomial.aeval r
  let T := MvPolynomial S R ⧸ RingHom.ker q.toRingHom
  let i : T →ₐ[R] D := Ideal.kerLiftAlg q
  have hi : Function.Injective i := Ideal.kerLiftAlg_injective q
  let K : Ideal T := J.comap i.toRingHom
  have hK : K ^ 2 = ⊥ := by
    apply le_antisymm _ bot_le
    have hp := Ideal.le_comap_pow (f := i.toRingHom) (K := J) 2
    rw [hJ, Ideal.comap_bot_of_injective i.toRingHom hi] at hp
    exact hp
  let j : T ⧸ K →ₐ[R] D ⧸ J := Ideal.quotientMapₐ J i le_rfl
  have hj : Function.Injective j := Ideal.quotientMap_injective
  let t : S → T ⧸ K := fun s ↦ Ideal.Quotient.mk K
    (Ideal.Quotient.mk (RingHom.ker q.toRingHom) (MvPolynomial.X s))
  have ht (s : S) : j (t s) = g₀ s := by
    change Ideal.Quotient.mk J (q (MvPolynomial.X s)) = g₀ s
    simpa only [q, MvPolynomial.aeval_X] using hr s
  let g' : S →ₐ[R] T ⧸ K :=
    { toFun := t
      map_one' := hj (by rw [ht, map_one, map_one])
      map_mul' := fun x y ↦ hj (by simp only [map_mul, ht])
      map_zero' := hj (by rw [ht, map_zero, map_zero])
      map_add' := fun x y ↦ hj (by simp only [map_add, ht])
      commutes' := fun a ↦ hj (by rw [ht, g₀.commutes, j.commutes]) }
  have hg' : ∃ k : ℕ, 1 ≤ k ∧ ∀ x ∈ n ^ k, g' x = 0 := by
    obtain ⟨k, hk, hkill⟩ := hg
    refine ⟨k, hk, fun x hx ↦ hj ?_⟩
    rw [map_zero]
    change j (t x) = 0
    rw [ht]
    apply hkill
    change e.symm x ∈ (n.map e.symm.toRingHom) ^ k
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hx
  obtain ⟨f, hf⟩ := h K hK g' hg'
  refine ⟨(i.comp f).comp e.toAlgHom, ?_⟩
  ext x
  have hf' := DFunLike.congr_fun hf (e x)
  have heq := congrArg j hf'
  change Ideal.Quotient.mk J (i (f (e x))) = g x
  change Ideal.Quotient.mk J (i (f (e x))) = j (t (e x)) at heq
  rw [heq, ht]
  exact congrArg g (e.symm_apply_apply x)

end Algebra
