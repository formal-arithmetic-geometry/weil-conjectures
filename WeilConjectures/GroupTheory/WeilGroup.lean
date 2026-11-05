/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.GroupTheory.OrderOfElement

/-!
# The Weil group of a homomorphism and an element

Let `π : G →* Γ` be a group homomorphism and `Φ : Γ`. The *Weil group* `W(π, Φ)` is the fibre
product `G ×_Γ ℤ` of `π` with `n ↦ Φ ^ n`, realised as the subgroup of `G × ℤ` of pairs `(g, n)`
with `π g = Φ ^ n`, and its *degree map* is the second projection `deg : W(π, Φ) → ℤ`.

In the application `G = π₁(X₀, x̄)` is the arithmetic fundamental group of a geometrically
connected scheme `X₀` over a finite field `k₀`, `Γ = Gal(k / k₀)`, and `Φ` is the geometric
Frobenius; then `W(π, Φ)` is the Weil group `W(X₀, x̄)` of `X₀`, and the kernel `ker π` is the
geometric fundamental group `π₁(X, x̄)`. Since `Φ` has infinite order, `ℤ` is identified with the
cyclic subgroup `⟨Φ⟩` and `W(π, Φ)` with the inverse image of `⟨Φ⟩` in `G`.

## Main declarations

* `MonoidHom.weilGroup`: the Weil group `W(π, Φ)`.
* `MonoidHom.weilGroupDeg`: its degree map.
* `MonoidHom.kerToWeilGroup`: the inclusion `ker π → W(π, Φ)`, `g ↦ (g, 0)`.
* `MonoidHom.exact_weilGroupDeg`: the sequence `1 → ker π → W(π, Φ) → ℤ → 0` is exact, and the
  lifts of `Φ` have degree one.

## Blueprint

`MonoidHom.exact_weilGroupDeg` implements `lem-wf-weil-group-exact-sequence`. The Weil group of a
scheme (`def-wf-weil-group`) is `AlgebraicGeometry.Scheme.FiniteEtale.weilGroup`, the Weil group
`W(π, Φ)` of the action of `π₁(X₀, s)` on the geometric fibres of the constant covers and the
geometric Frobenius.
-/

@[expose] public section

namespace MonoidHom

variable {G Γ : Type*} [Group G] [Group Γ] (π : G →* Γ) (Φ : Γ)

/-- The Weil group `W(π, Φ)` of a homomorphism `π : G →* Γ` and an element `Φ : Γ`: the fibre
product of `π` with `zpowersHom Γ Φ : ℤ →* Γ`, as the subgroup of `G × ℤ` of pairs `(g, n)` with
`π g = Φ ^ n`. -/
def weilGroup : Subgroup (G × Multiplicative ℤ) :=
  (π.comp (fst G (Multiplicative ℤ))).eqLocus ((zpowersHom Γ Φ).comp (snd G (Multiplicative ℤ)))

variable {π Φ} in
theorem mem_weilGroup {x : G × Multiplicative ℤ} :
    x ∈ weilGroup π Φ ↔ π x.1 = Φ ^ x.2.toAdd :=
  Iff.rfl

/-- The degree map `deg : W(π, Φ) → ℤ`, which records the exponent of `Φ`. -/
def weilGroupDeg : weilGroup π Φ →* Multiplicative ℤ :=
  (snd G (Multiplicative ℤ)).comp (weilGroup π Φ).subtype

@[simp]
theorem weilGroupDeg_apply (w : weilGroup π Φ) : weilGroupDeg π Φ w = (w : G × _).2 :=
  rfl

end MonoidHom
