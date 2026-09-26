/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs

/-!
# Finite group schemes over a field

A finite group scheme over a field `K` is an object `G` of `Over (Spec (.of K))` equipped with
`CategoryTheory.GrpObj G` whose structure morphism `G.hom` is finite; its *order* is
`G.hom.finrankΓ = dim_K Γ(G, 𝒪_G)`. This file records the basic structural facts about such
group schemes that the abelian-variety block of the blueprint uses: the order of a connected
one is a power of the characteristic, one whose order is prime to the characteristic is étale,
and a finite étale group scheme over an algebraically closed field has exactly `|G|` rational
points, insensitive to enlarging the base field.

## Main statements

- `AlgebraicGeometry.finrankΓ_eq_pow_of_connected`: a connected finite flat group scheme over a
  field of characteristic `p > 0` has order a power of `p`.
- `AlgebraicGeometry.etale_of_not_dvd_finrankΓ`: a finite flat group scheme over an
  algebraically closed field whose order is prime to the characteristic is étale.
- `AlgebraicGeometry.card_points_of_isFinite_of_etale`: a finite étale group scheme over an
  algebraically closed field `K` has exactly `|G|` points over `K`, and base change to any
  algebraically closed extension `K'` is a bijection on points.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry

variable {K : Type u} [Field K]

/-- Blueprint `sk-prop-av-connected-order`: Connected finite group schemes have `p`-power order

Let `G` be a finite flat group scheme over a field `K` of characteristic `p > 0`. If `G` is
connected, then its order `|G| = dim_K Γ(G, 𝒪_G)` is a power of `p`. -/
theorem finrankΓ_eq_pow_of_connected (p : ℕ) [Fact p.Prime] [CharP K p]
    (G : Over (Spec (.of K))) [GrpObj G] [IsFinite G.hom] [Flat G.hom] [ConnectedSpace G.left] :
    ∃ r : ℕ, G.hom.finrankΓ = p ^ r :=
  sorry

/-- Blueprint `sk-prop-av-prime-p-etale`: Group schemes of order prime to `p` are étale

Let `G` be a finite flat group scheme over an algebraically closed field `K` of characteristic
`p`, of order `m`. If `p = 0`, or if `p > 0` and `p ∤ m`, then `G` is étale over `K`. -/
theorem etale_of_not_dvd_finrankΓ [IsAlgClosed K] (p : ℕ) [CharP K p]
    (G : Over (Spec (.of K))) [GrpObj G] [IsFinite G.hom] [Flat G.hom]
    (hp : p = 0 ∨ ¬ (p ∣ G.hom.finrankΓ)) :
    Etale G.hom :=
  sorry

/-- Blueprint `sk-prop-av-finite-etale-points`: Points of finite étale group schemes

Let `G` be a finite étale group scheme of order `m` over an algebraically closed field `K`, and
let `K'` be an algebraically closed extension of `K`. Then `G` has exactly `m` points with
values in `K`, and base change along `K ⊆ K'` is a bijection `G(K) ≃ G(K')`. -/
theorem card_points_of_isFinite_of_etale [IsAlgClosed K] {K' : Type u} [Field K'] [Algebra K K']
    [IsAlgClosed K'] (G : Over (Spec (.of K))) [GrpObj G] [IsFinite G.hom] [Etale G.hom] :
    Nat.card (𝟙_ (Over (Spec (.of K))) ⟶ G) = G.hom.finrankΓ ∧
      Function.Bijective (fun s : 𝟙_ (Over (Spec (.of K))) ⟶ G =>
        (toUnit (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K K')))) ≫ s)) :=
  sorry

end AlgebraicGeometry
