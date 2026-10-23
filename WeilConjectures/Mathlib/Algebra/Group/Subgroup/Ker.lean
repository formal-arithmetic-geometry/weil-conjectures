/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# The splitting lemma for commutative groups

A homomorphism `s : G →* H` of a commutative group `G` with a right inverse `i : H →* G`
(i.e. `s ∘ i = id`) splits `G` as `H × ker s`.

## Main definitions

- `MonoidHom.prodKerEquivOfLeftInverse`: the isomorphism `G ≃* H × ker s`, `g ↦ (s g, g / i (s g))`.
-/

@[expose] public section

namespace MonoidHom

variable {G H : Type*} [CommGroup G] [Group H]

/-- **The splitting lemma.** If `s : G →* H` has a right inverse `i : H →* G`, then
`g ↦ (s g, g * (i (s g))⁻¹)` is an isomorphism `G ≃* H × ker s`, with inverse
`(h, k) ↦ i h * k`. -/
@[to_additive /-- **The splitting lemma.** If `s : G →+ H` has a right inverse
`i : H →+ G`, then `g ↦ (s g, g - i (s g))` is an isomorphism `G ≃+ H × ker s`, with inverse
`(h, k) ↦ i h + k`. -/]
def prodKerEquivOfLeftInverse (s : G →* H) (i : H →* G) (h : Function.LeftInverse s i) :
    G ≃* H × s.ker where
  toFun g := (s g, ⟨g * (i (s g))⁻¹, by simp [mem_ker, h (s g)]⟩)
  invFun p := i p.1 * p.2
  left_inv g := by simp
  right_inv p := by
    have hp : s p.2 = 1 := p.2.2
    ext
    · simp [h p.1, hp]
    · simp [h p.1, hp]
  map_mul' a b := by
    ext
    · simp
    · simp only [map_mul, mul_inv, Subgroup.coe_mul, Prod.snd_mul]
      exact mul_mul_mul_comm _ _ _ _

@[to_additive (attr := simp)]
lemma prodKerEquivOfLeftInverse_apply_fst (s : G →* H) (i : H →* G)
    (h : Function.LeftInverse s i) (g : G) : (prodKerEquivOfLeftInverse s i h g).1 = s g :=
  rfl

@[to_additive (attr := simp)]
lemma coe_prodKerEquivOfLeftInverse_apply_snd (s : G →* H) (i : H →* G)
    (h : Function.LeftInverse s i) (g : G) :
    ((prodKerEquivOfLeftInverse s i h g).2 : G) = g * (i (s g))⁻¹ :=
  rfl

@[to_additive (attr := simp)]
lemma prodKerEquivOfLeftInverse_symm_apply (s : G →* H) (i : H →* G)
    (h : Function.LeftInverse s i) (p : H × s.ker) :
    (prodKerEquivOfLeftInverse s i h).symm p = i p.1 * p.2 :=
  rfl

end MonoidHom
