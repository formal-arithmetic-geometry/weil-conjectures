/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.GenericSliceTraitGaloisLayer
public import WeilConjectures.TraceFormula.Specialization.TraitChangeGaloisLayerIntegral
public import WeilConjectures.SixFunctors.NearbyCycles.TraitChangeSplitMono
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.IntegralModelAmbient
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleOrigin
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralReductionConstructible

/-!
# The averaging splitting (M2) on the generic slice trait

This file proves (M2), the averaging splitting of the slice step of Deligne's finiteness theorem
(SGA 4½, [Th. finitude], Lemme 3.4,
`NearbyCyclesModel.isSplitMono_pullbackExchange_app_toCartesian_genericSliceTraitHom`): for the
morphism of models `σ` over a generic slice trait `S' ⟶ S` and a bounded constructible
`ℚ̄_ℓ`-complex `B`, the pullback exchange of `σ.toCartesian` is a split monomorphism at `B`.

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
(`AlgebraicGeometry.nonempty_genericSliceTrait`).

The proof passes to an integral model `K₀` of `B` (derived complete and bounded constructible on
the noetherian `𝔸ⁿ⁺¹_S`, `ProEtale.CondensedRing.exists_derivedCompleteIntegers_iso_integralModel`).
Over a slice trait the change of geometric generic fibres is a pro-`p` Galois layer up to universal
homeomorphisms (`AlgebraicGeometry.SliceTrait.exists_finrank_eq_pow`), so the unit of its
adjunction with `𝒪_E`-coefficients splits
(`NearbyCyclesModel.Hom.isSplitMono_unit_toCartesian_generic_of_sliceTrait_padicIntegers`), hence
the restricted base change morphism with `𝒪_E`-coefficients splits, and the splitting passes to
`E` and `ℚ̄_ℓ`
(`NearbyCyclesModel.Hom.isSplitMono_pullbackExchange_app_of_isSplitMono_padicIntegers`).
The reductions of `K₀` modulo `ℓⁿ⁺¹` are bounded constructible, hence of étale origin.
-/

@[expose] public section

universe u

open CategoryTheory Limits IsLocalRing

open scoped TensorProduct CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.Hom

open Scheme IsLocalRing

variable {R₁ : Type u} [CommRing R₁] [IsDomain R₁] [IsDiscreteValuationRing R₁]
  [IsStrictlyHenselianLocalRing R₁] {Ω₁ : Type u} [Field Ω₁] {a₁ : R₁ →+* Ω₁}
  {κ₁ : Type u} [Field κ₁] {b₁ : R₁ →+* κ₁} (D : SliceTrait a₁ b₁)
  [IsAlgClosed Ω₁] (ha₁ : Function.Injective a₁)
  (halg : letI := a₁.toAlgebra; Algebra.IsAlgebraic R₁ Ω₁)
  {X X' Y Y' : Scheme.{u}} {M : NearbyCyclesModel X X'} {N : NearbyCyclesModel Y Y'}
  {f : X ⟶ Y} {f' : X' ⟶ Y'} (φ : M.Hom N f f')
  {q : M.total ⟶ Spec (.of D.R)} {g : M.generic ⟶ Spec (.of D.Ω)}
  {q₁ : N.total ⟶ Spec (.of R₁)} {g₁ : N.generic ⟶ Spec (.of Ω₁)}

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.Hom

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

variable {ℓ : ℕ} [Fact ℓ.Prime] {k' : Type u} [Field k'] [IsSepClosed k']
  [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
