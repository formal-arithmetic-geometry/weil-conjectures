/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.Quotient.Defs
import WeilConjectures.RingTheory.SubsingletonH1CotangentOfCharP
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.Algebra.CharP.Basic

/-!
# Lifting ring maps from fields of positive characteristic

Ring maps from a field of characteristic `p > 0` lift along nilpotent ideals of rings annihilated
by `p`.

## Implementation details

All rings involved are `𝔽_p`-algebras and the maps are `𝔽_p`-algebra maps. The first cotangent
homology of `K/𝔽_p` vanishes and its differentials form a vector space, so `K` is formally smooth
over `𝔽_p` and maps lift along square-zero ideals. A map into `D/J` is lifted successively to
`D/Jⁱ` for `1 ≤ i ≤ N`, the kernel `Jⁱ/Jⁱ⁺¹` being square-zero.

## References

* [Stacks, Tag 0320], part (3)
* [Stacks, Tag 07K4]
* [Stacks, Tag 031Z]
* [Stacks, Tag 031J]
-/

@[expose] public section

universe u v

namespace RingHom

/-- Ring maps from a field of characteristic `p > 0` lift along nilpotent ideals of rings
annihilated by `p`. -/
theorem exists_lift_of_field_charP (K : Type u) (D : Type v) [Field K] [CommRing D]
    (p : ℕ) [CharP K p] (hp : 0 < p) (hD : (p : D) = 0)
    (J : Ideal D) (N : ℕ) (hN : 1 ≤ N) (hJ : J ^ N = ⊥) (g : K →+* D ⧸ J) :
    ∃ f : K →+* D, (Ideal.Quotient.mk J).comp f = g := by
  have hN' : 0 < N := by omega
  rcases subsingleton_or_nontrivial D with hsub | hnon
  · let := hsub
    let f : K →+* D :=
      { toFun := fun _ => 0
        map_one' := Subsingleton.elim _ _
        map_mul' := by intros; apply Subsingleton.elim
        map_zero' := Subsingleton.elim _ _
        map_add' := by intros; apply Subsingleton.elim }
    refine ⟨f, ?_⟩
    ext x
    exact Subsingleton.elim _ _
  · let := hnon
    let := ZMod.algebra K p
    let : CharP D p := by
      apply (CharP.charP_iff_prime_eq_zero (R := D)
        (CharP.char_prime_of_ne_zero K (by omega))).2
      exact hD
    let := ZMod.algebra D p
    let : Module.Free K (KaehlerDifferential (ZMod p) K) :=
      Module.Free.of_divisionRing K _
    let : Module.Projective K (KaehlerDifferential (ZMod p) K) := Module.Projective.of_free
    have h₁ : Subsingleton (Algebra.H1Cotangent (ZMod p) K) :=
      Algebra.subsingleton_h1Cotangent_of_charP p hp K
    let : Algebra.FormallySmooth (ZMod p) K := Algebra.FormallySmooth.mk inferInstance h₁
    obtain ⟨f, hf⟩ := Algebra.FormallySmooth.exists_lift J ⟨N, hJ⟩
      ({ toRingHom := g, commutes' := by
          intro r
          obtain ⟨n, rfl⟩ := ZMod.intCast_surjective r
          simp } : K →ₐ[ZMod p] D ⧸ J)
    refine ⟨f.toRingHom, ?_⟩
    exact congrArg AlgHom.toRingHom hf

end RingHom
