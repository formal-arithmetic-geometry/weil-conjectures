/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs

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

- `AlgebraicGeometry.exists_finrankΓ_eq_pow`: a connected finite group scheme over a field of
  characteristic `p > 0` has order a power of `p`.
- `AlgebraicGeometry.etale_of_not_dvd_finrankΓ`: a finite group scheme whose order is prime to
  the characteristic is étale.
- `AlgebraicGeometry.card_points_eq_finrankΓ`: a finite étale group scheme over an algebraically
  closed field `K` has exactly `|G|` points over `K`.
- `AlgebraicGeometry.bijective_toUnit_comp`: base change of such a `G` to an algebraically
  closed extension `K'` is a bijection on points.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry

variable {K : Type u} [Field K]

/-- Blueprint `sk-prop-av-connected-order`: Connected finite group schemes have `p`-power order

Let `G` be a finite group scheme over a field `K` of characteristic `p > 0`. If `G` is
connected, then its order `|G| = dim_K Γ(G, 𝒪_G)` is a power of `p`. -/
theorem exists_finrankΓ_eq_pow (p : ℕ) [Fact p.Prime] [CharP K p]
    (G : Over (Spec (.of K))) [GrpObj G] [IsFinite G.hom] [ConnectedSpace G.left] :
    ∃ r : ℕ, G.hom.finrankΓ = p ^ r :=
  sorry

/-- Blueprint `sk-prop-av-prime-p-etale`: Group schemes of order prime to `p` are étale

Let `G` be a finite group scheme over a field `K` of characteristic `p`, of order `m`. If
`p ∤ m` — which for `p = 0` just says `m ≠ 0` — then `G` is étale over `K`. -/
theorem etale_of_not_dvd_finrankΓ (p : ℕ) [CharP K p] (G : Over (Spec (.of K))) [GrpObj G]
    [IsFinite G.hom] (hp : ¬ p ∣ G.hom.finrankΓ) :
    Etale G.hom :=
  sorry

/-- Blueprint `sk-prop-av-finite-etale-points`: Points of finite étale group schemes

A finite étale group scheme `G` of order `m` over an algebraically closed field `K` has exactly
`m` points with values in `K`. -/
theorem card_points_eq_finrankΓ [IsAlgClosed K] (G : Over (Spec (.of K))) [GrpObj G]
    [IsFinite G.hom] [Etale G.hom] :
    Nat.card (𝟙_ (Over (Spec (.of K))) ⟶ G) = G.hom.finrankΓ :=
  sorry

/-- Blueprint `sk-prop-av-finite-etale-points`: Points of finite étale group schemes

Let `G` be a finite étale group scheme over an algebraically closed field `K` and let `K'` be an
algebraically closed extension of `K`. Then base change along `K ⊆ K'`, that is precomposition
with the structure morphism of `Spec K'` over `K`, is a bijection `G(K) ≃ G(K')`. -/
theorem bijective_toUnit_comp [IsAlgClosed K] {K' : Type u} [Field K'] [Algebra K K']
    [IsAlgClosed K'] (G : Over (Spec (.of K))) [GrpObj G] [IsFinite G.hom] [Etale G.hom] :
    Function.Bijective (fun s : 𝟙_ (Over (Spec (.of K))) ⟶ G ↦
      toUnit (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K K')))) ≫ s) :=
  sorry

end AlgebraicGeometry
