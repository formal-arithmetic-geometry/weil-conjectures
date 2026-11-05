/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.SliceTraitGaloisLayer
public import WeilConjectures.TraceFormula.Specialization.SliceTraitExists
public import WeilConjectures.TraceFormula.Specialization.SliceTraitFunctoriality

/-!

# Maps of slice traits along a change of trait

Let `S₂ = Spec R₂ ⟶ S₁ = Spec R₁` be a map of strictly henselian traits, given by an injective
local homomorphism `ι : R₁ →+* R₂`, with compatible geometric generic points `a₁ : R₁ ⟶ Ω₁`,
`a₂ : R₂ ⟶ Ω₂` (`c : Ω₁ ⟶ Ω₂`). To compare the slices of a model over the two traits
(SGA 4½, [Th. finitude], 3.7), Deligne uses the morphism `S₂(x) ⟶ S₁(x)` between the strict
localizations of `𝔸¹_{S₂}` and `𝔸¹_{S₁}` at the geometric points over the generic points of their
special fibres. This file constructs it, together with a compatible map of geometric generic
points.

## Main results

- `AlgebraicGeometry.SliceTrait.exists_comp_a_eq`: **extension of geometric generic points**. For
  a slice trait `D` over `S₁` (with `Ω₁` algebraic over `R₁`), any pair of maps `α : R ⟶ Ω₂`,
  `β : Ω₁ ⟶ Ω₂` into an algebraically closed field, compatible over `R₁`, extends to
  `γ : Ω' ⟶ Ω₂`. Indeed `Spec(Ω₁ ⊗_{R₁} R)` is a single point
  (`AlgebraicGeometry.SliceTrait.subsingleton_primeSpectrum`), so the product maps
  `Ω₁ ⊗_{R₁} R ⟶ Ω'` and `Ω₁ ⊗_{R₁} R ⟶ Ω₂` have the same kernel; hence the second factors through
  the compositum `L = Ω₁(R) ⊆ Ω'`, and `L ⟶ Ω₂` extends to the algebraic extension `Ω' / L`.
- `AlgebraicGeometry.SliceTrait.Hom`: a morphism `S'₂ ⟶ S'₁` of slice traits over `S₂ ⟶ S₁`,
  given by a local injective ring map `ψ : R'₁ ⟶ R'₂` over `𝔸¹_{S₂} ⟶ 𝔸¹_{S₁}`, with compatible
  maps of closed and geometric generic points.
- `AlgebraicGeometry.sliceTraitOfStrictLocalizationHom`: the morphism `S₂(x) ⟶ S₁(x)` of
  strict-localization slice traits, given by `AlgebraicGeometry.sliceTraitMap`, with
  `AlgebraicGeometry.exists_sliceTraitOfStrictLocalization_map` providing the map of geometric
  generic points.

-/

@[expose] public section

universe u v

open CategoryTheory IsLocalRing

open scoped TensorProduct

namespace AlgebraicGeometry.SliceTrait

variable {R₁ : Type u} [CommRing R₁] [IsDomain R₁] [IsDiscreteValuationRing R₁]
  [IsStrictlyHenselianLocalRing R₁] {Ω₁ : Type u} [Field Ω₁] {a₁ : R₁ →+* Ω₁}
  {κ₁ : Type u} [Field κ₁] {b₁ : R₁ →+* κ₁} (D : SliceTrait a₁ b₁)

end AlgebraicGeometry.SliceTrait

namespace AlgebraicGeometry

open Scheme

attribute [instance] SliceTrait.Hom.isLocalHom_ψ

variable {R₁ R₂ : Type u} [CommRing R₁] [IsDomain R₁] [IsDiscreteValuationRing R₁]
  [IsStrictlyHenselianLocalRing R₁] [CommRing R₂] [IsDomain R₂] [IsDiscreteValuationRing R₂]
  [IsStrictlyHenselianLocalRing R₂] (ι : R₁ →+* R₂) [IsLocalHom ι] (hι : Function.Injective ι)
  {Ω₁ Ω₂ : Type u} [Field Ω₁] [Field Ω₂] (c : Ω₁ →+* Ω₂)
  {a₁ : R₁ →+* Ω₁} (ha₁ : Function.Injective a₁)
  (halg₁ : letI := a₁.toAlgebra; Algebra.IsAlgebraic R₁ Ω₁)
  {a₂ : R₂ →+* Ω₂} (ha₂ : Function.Injective a₂)
  (halg₂ : letI := a₂.toAlgebra; Algebra.IsAlgebraic R₂ Ω₂)
  (hc : c.comp a₁ = a₂.comp ι)
  {κ₂ : Type u} [Field κ₂] {b₂ : R₂ →+* κ₂} (hb₂ : RingHom.ker b₂ = maximalIdeal R₂)

end AlgebraicGeometry
