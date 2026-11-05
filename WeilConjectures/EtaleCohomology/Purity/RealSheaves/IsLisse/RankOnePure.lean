/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.Basic
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.Weights
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup
public import WeilConjectures.Mathlib.RepresentationTheory.Basic
import WeilConjectures.AlgebraicGeometry.LinearAlgebraicGroup.Monodromy
import WeilConjectures.AlgebraicGeometry.LinearAlgebraicGroup.RankOne
import WeilConjectures.Mathlib.GroupTheory.SemidirectProduct
import WeilConjectures.Mathlib.Analysis.Normed.Field.Basic
import WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne
import WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity

/-! # Rank-one weights

Source: latest blueprint, part-weights-riemann-hypothesis/sec-rank-one-curves/
sec-logarithms-and-rank-one-purity/sk-cor-wrp-rankone-pure/_section.md, statement and
Complement (blueprint: sk-cor-wrp-rankone-pure).

A rank-one lisse Weil sheaf on a smooth geometrically connected curve is rendered, through the
sheaf/representation correspondence of `sk-d-real-weil`, as a rank-one lisse representation `ρ`
of `W(U₀)` (`AlgebraicGeometry.WeilGroup`, `AlgebraicGeometry.WeilGroup.IsLisse`); its character
is `χ = det ρ`. Punctual purity and the weight are those of `sk-d-real-weights`
(`AlgebraicGeometry.WeilGroup.IsPunctuallyPure`, `AlgebraicGeometry.WeilGroup.frobeniusWeight`).
The finite part `χ_fin` of the Complement is the unique `ε` with `χ = ε · z ^ deg`, `z = χ s`.

## Main statements

- `AlgebraicGeometry.WeilGroup.IsLisse.isPunctuallyPure_and_finitePart_of_finrank_eq_one`
-/

@[expose] public section

universe u

set_option autoImplicit false
set_option relaxedAutoImplicit false

open CategoryTheory

namespace AlgebraicGeometry

namespace WeilGroup

variable {K : Type u} [Field K] [Finite K]
variable {C : Scheme.{u}} {p : C ⟶ Spec (.of K)} [IsCurve p]
variable (W : WeilGroup p) (l : ℕ) [Fact l.Prime]
variable [SmoothOfRelativeDimension 1 p] [GeometricallyConnected p]
variable [Fact (ringChar K ≠ l)] [W.IsEtaleQuotient]
variable {V : Type u} [AddCommGroup V] [Module (PadicAlgCl l) V]
  [FiniteDimensional (PadicAlgCl l) V]
variable (ρ : Representation (PadicAlgCl l) W.carrier V)
variable (ι : PadicAlgCl l →+* ℂ)

variable {W l ρ} in
/-- Rank-one weights. Every rank-one lisse Weil sheaf on a smooth geometrically connected curve
is punctually `ι`-pure of weight `λ_ι(c) = 2 log_q |ι(c)|`, `c = χ(s)`, for any degree-one lift
`s`. Complement: `χ_fin(w) = χ(w) c ^ (-deg w)` is a character with `χ = χ_fin · c ^ deg`,
`χ_fin(s) = 1` and `χ_fin(W(U₀)) = χ(P)`. Here `χ = det ρ`, `P = π₁(U)` is `W.geometric`.
Source: latest blueprint, sk-cor-wrp-rankone-pure/_section.md, statement and Complement
(blueprint: sk-cor-wrp-rankone-pure).

Proof (the node's four steps).
1. By the conventions of `sk-d-real-weil`, `ρ` gives a character `χ : W(U₀) → E^×` continuous on
   `P`; the exact degree sequence makes `(W(U₀), deg, s)` a degree datum of `d-monodromy`. Put
   `c = χ(s) ≠ 0`. By `sk-p-real-rankone` (`IsLisse.finite_geometric_image`), `χ(P)` is finite.
2. Apply `det-p-rankone` (`cor-wf-rank-one-degree-factorization-curve`) with `A = E^×`,
   `γ = s`, `z = c`: `w ↦ c ^ deg w` and `ε(w) = χ(w) c ^ (-deg w)` are characters,
   `χ = ε · c ^ deg`, `ε(s) = 1`, `ε(W) = χ(P)`; for `w = g s ^ n`, `g ∈ P`, `ε(w) = χ(g)`.
3. At a closed point `x` of degree `d`, `q_x = q ^ d` and `deg F_x = d`; the unique local
   eigenvalue of `sk-d-real-weights` is `α_x = χ(F_x) = ε(F_x) c ^ d`. `ε(F_x)` lies in the finite
   group `ε(W)`, so it has finite order and `|ι ε(F_x)| = 1` (`lem-tw-root-of-unity-modulus`).
   With `a = |ι c| > 0`, `|ι α_x| = a ^ d`, and since `q > 1`,
   `2 log |ι α_x| / log q_x = 2 d log a / (d log q) = λ_ι(c)`: punctual purity of that weight.
4. If `s'` also has degree one, `g = s' s⁻¹ ∈ P` and `χ(s') = χ(g) c` with `χ(g)` of finite
   order, so `|ι χ(s')| = |ι c|` (`lem-tw-root-of-unity-modulus`): the weight does not depend
   on the lift. -/
theorem IsLisse.isPunctuallyPure_and_finitePart_of_finrank_eq_one
    (hrank : Module.finrank (PadicAlgCl l) V = 1)
    (hρ : W.IsLisse l ρ)
    (s : W.carrier)
    (hs : W.deg s = Multiplicative.ofAdd 1) :
    W.IsPunctuallyPure l ρ ι (frobeniusWeight ι (Nat.card K) (ρ.detCharacter s)) ∧
      ∃ ε : W.carrier →* (PadicAlgCl l)ˣ,
        ε s = 1 ∧
        Set.range (fun w : W.carrier => ε w) =
          Set.range (fun g : W.geometric => ρ.detCharacter g) ∧
        (∀ w : W.carrier,
          ρ.detCharacter w = ε w * (ρ.detCharacter s) ^ (W.deg w).toAdd) := by
  sorry

end WeilGroup

end AlgebraicGeometry
