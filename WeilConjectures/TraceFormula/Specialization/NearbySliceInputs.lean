/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.GenericSliceTrait

/-!

# The inputs of the slice step of Deligne's finiteness theorem

Let `S = Spec k'⟦t⟧` with `k'` separably closed of characteristic `p ≠ ℓ`, `K = k'(x)^alg`,
`T = Spec K⟦t⟧`, and let `φ = NearbyCyclesModel.affineSpaceSliceHom k' n i` be the morphism of
geometric models over the coordinate generic slice `h : 𝔸ⁿ_T ⟶ 𝔸ⁿ⁺¹_S = X`. Following Deligne
(SGA 4½, [Th. finitude], proof of 3.3), `φ` factors through the strict localization `S'` of `𝔸¹_S`
at the generic point of its special fibre (`AlgebraicGeometry.GenericSliceTrait`), with
`X' = X ×_{𝔸¹_S} S'`:
```
(𝔸ⁿ_T over T) ──τ──→ (X' over S') ──σ──→ (X over S)
```
* `τ` (`NearbyCyclesModel.genericSliceTraitChangeHom`) is the change of strictly henselian trait
  `T ⟶ S'`; its pullback exchange is invertible by the invariance of nearby cycles under change
  of trait (`NearbyCyclesModel.Hom.isIso_pullbackExchange_app_of_isPullback_trait`, SGA 4½,
  [Th. finitude], 3.7).
* `σ` (`NearbyCyclesModel.genericSliceTraitHom`) factors through its cartesian model
  (`NearbyCyclesModel.Hom.cartesianModel`), with generic fibre `X' ×_S Spec Ω`. The second factor
  is weakly étale base change along `X' ⟶ X`, an isomorphism
  (`NearbyCyclesModel.Hom.isIso_pullbackExchange_fromCartesian_of_weaklyEtale`). The first factor
  is the change of generic fibres `π : X' ×_{S'} Spec Ω' ⟶ X' ×_S Spec Ω`, whose pullback exchange
  is, up to the extension from an algebraic closure `k̄₀` to `Ω'` (which does not change
  cohomology), the inclusion of the invariants under the pro-`p` group `P = Gal(k̄₀/k₀)`,
  `k₀ = Ω ⊗_{η} η'`
  (Th. finitude, Lemme 3.4), split by averaging
  (`NearbyCyclesModel.isSplitMono_pullbackExchange_app_toCartesian_genericSliceTraitHom`, (M2)).

The strict localization is a generic slice trait
(`AlgebraicGeometry.nonempty_genericSliceTrait`). This file states the averaging splitting (M2),
which is not proved here.

## Unfinished

* (M2): the finite-level Galois trace of #1791 (`trace2/nearby-prop-averaging`) splits the unit of
  each finite Galois `p`-cover. Passing to `π` needs either that `P` acts on `Ψ_{S'}` through a
  finite quotient (true once `Ψ_{X'/S'}(B)` is known to be constructible, i.e. Deligne's finiteness
  over `S'`, which the induction over the traits `Spec k⟦t⟧` does not provide), or the `ℚ̄_ℓ`-valued
  Haar average over `P`; neither is formalised.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

variable {ℓ : ℕ} [Fact ℓ.Prime] {k' : Type u} [Field k'] [IsSepClosed k']
  [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]

/-- **(M2) The pro-`p` averaging splitting on the generic slice trait** (SGA 4½, [Th. finitude],
Lemme 3.4): for a bounded constructible complex
`B` on `X = 𝔸ⁿ⁺¹_S`, the pullback exchange of the first factor `toCartesian` of the morphism of
models `σ : (X ×_{𝔸¹_S} S' over S') ⟶ (X over S)` is a split monomorphism at `B`.

It is `Φ(u)` for `Φ = i^* Rj'_*` (special fibre of `X' = X ×_{𝔸¹_S} S'`, `j'` the inclusion of
`X' ×_S Ω`) and `u : G ⟶ Rπ_* Lπ^* G` the unit of the change of generic fibres
`π : X' ×_{S'} Ω' ⟶ X' ×_S Ω`, `G` the restriction of `B`. Here `π` is the base change of
`Spec Ω' ⟶ Spec k₀`, `k₀ = Ω ⊗_{Frac k'⟦t⟧} Frac R` a field; it factors through the
`P`-torsor `Spec k̄₀ ⟶ Spec k₀`, `P = Gal(k̄₀/k₀)` pro-`p`.
With #1791: if `P` acts on `Ψ_{X'/S'}(B)` through a finite quotient `Gal(L/k₀)` (which holds once
`Ψ_{X'/S'}(B)` is constructible), then `u = uₙ ≫ c` with `uₙ` the unit of the finite Galois
`p`-cover `πₙ` at level `L` and `Φ(c)` invertible; `uₙ` is split by the normalized trace
`normalizedTrace (galoisTrace πₙ)` (`CategoryTheory.comp_normalizedTrace`,
`ProEtale.unit_comp_galoisTrace`), and `CategoryTheory.isSplitMono_map_of_isIso_map` concludes.
Without constructibility, the splitting is the `ℚ̄_ℓ`-valued Haar average over `P`. `sorry`ed. -/
theorem isSplitMono_pullbackExchange_app_toCartesian_genericSliceTraitHom
    (D : GenericSliceTrait k') (n : ℕ) (i : Fin (n + 1))
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology (affineSpaceModel k' (n + 1)).total)
      Ab.{u + 1}) (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
        (affineSpaceModel k' (n + 1)).total))}
    (hB : boundedConstructible _ B) :
    IsSplitMono (((genericSliceTraitHom D n i).toCartesian.pullbackExchange
      (Profinite.padicAlgClRingObj ℓ)).app B) :=
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
