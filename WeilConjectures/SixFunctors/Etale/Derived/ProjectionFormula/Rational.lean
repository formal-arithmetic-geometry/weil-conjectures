/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.RationalCoefficient
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Integral

/-!
# The projection formula at the rational stage `E`

Let `E` be a finite extension of `ℚ_ℓ` inside `ℚ̄_ℓ` with ring of integers `𝒪_E`. The rational
stage `D_comp(Y_ét, E)` of the `ℓ`-adic formalism is the rationalization
`DerivedCategoryDerivedCompleteRational` of the integral stage `D_comp(Y_ét, 𝒪_E)`, and the
operations `Rf_!`, `⊗ᴸ` and `Lf^*` on rationalized objects are induced by the integral ones. So
the projection map `PF_{f, K, L}` over `E`, for `K` and `L` obtained by rationalization from
`𝒪_E`-objects, is the image of the integral projection map under the localization functor
`DerivedCategoryDerivedCompleteRational.fromIntegral`. This file proves that it is an
isomorphism (blueprint `thm-sf-pf-field`, rational stage), following the blueprint: the
integral projection map is an isomorphism (`sk-thm-sf-pf-adic`,
`AlgebraicGeometry.Etale.hasProjectionFormula_of_derivedCompleteIntegral`), and a functor carries
isomorphisms to isomorphisms.

## Main statements

- `AlgebraicGeometry.Etale.isIso_fromIntegral_map_projectionMap` (`thm-sf-pf-field`): the
  projection formula over `E` for rationalizations of bounded constructible, derived complete
  `𝒪_E`-objects of finite Tor amplitude.
- `AlgebraicGeometry.Etale.isIso_reductionModIdeal_pow_map_projectionMap` (`thm-sf-pf-field`):
  the reductions modulo `𝔪_Eⁿ` of the integral representative are isomorphisms.
- `AlgebraicGeometry.Etale.hasProjectionFormula_field` (`sk-thm-sf-pf-field`): both together.

## Implementation notes

The stage `ℚ̄_ℓ` of the blueprint concerns objects represented at a finite stage `E'/ℚ_ℓ`; for
those the projection map is the scalar extension of the projection map over `E'`, an isomorphism
by the statement here for `E'`, `E` being an arbitrary finite extension of `ℚ_ℓ` inside `ℚ̄_ℓ`.
The `2`-colimit category over the finite stages is not built in the étale model, and the
compatibility of the projection map with the scalar extension functors `E ⟶ E'` is not stated:
those functors (extension of scalars `𝒪_E ⟶ 𝒪_{E'}` on étale derived categories, and their
commutation with `Rf_!`, `⊗ᴸ` and `Lf^*`) are not constructed yet.
-/

@[expose] public section

universe w u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

set_option hygiene false in
/-- The coefficient category `ModuleCat 𝒪_E` of the integral stage. -/
local notation "𝐌" => ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E))

variable (l : ℕ) [Fact l.Prime] (E : Type w) [Field E] [Algebra ℚ_[l] E]
  [Algebra E (PadicAlgCl l)] [IsScalarTower ℚ_[l] E (PadicAlgCl l)]
  [FiniteDimensional ℚ_[l] E] [Small.{u + 1} E]

variable {X Y : Scheme.{u}}

-- `𝐌` is elaborated with the ring structure `CommRing.toRing` of `Shrink 𝒪_E`, as in
-- `WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Integral`.
attribute [-instance] Shrink.instRing

/-- Blueprint `thm-sf-pf-field`: Rational and algebraically closed stages; the rational stage.

Let `K` and `L` be bounded constructible, derived complete for `𝔪_E` and of finite Tor amplitude
over `𝒪_E`. Over `E`, the projection map `PF_{f, K, L} : Rf_! K ⊗ᴸ L ⟶ Rf_!(K ⊗ᴸ Lf^* L)` of the
rationalizations of `K` and `L` is the image under the rationalization functor
`D_comp(Y_ét, 𝒪_E) ⥤ D_comp(Y_ét, E)` of the integral projection map, both of whose sides are
assumed derived complete (`hs`, `ht`: automatic in the pro-étale setting of the blueprint,
but not on the small étale site, see
`AlgebraicGeometry.Etale.hasProjectionFormula_of_derivedCompleteIntegral`). It is an
isomorphism: the integral projection map is one (`sk-thm-sf-pf-adic`) and the rationalization
functor carries isomorphisms to isomorphisms. -/
theorem isIso_fromIntegral_map_projectionMap (f : X ⟶ Y) [HasCompactification f]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology 𝐌))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology 𝐌))
    (hKc : DerivedCategory.boundedConstructible 𝐌 X K)
    (hK : _root_.DerivedCategory.derivedCompleteIntegral X.smallEtaleTopology l E K)
    (hKt : DerivedCategory.finiteTorAmplitude 𝐌 X K)
    (hLc : DerivedCategory.boundedConstructible 𝐌 Y L)
    (hL : _root_.DerivedCategory.derivedCompleteIntegral Y.smallEtaleTopology l E L)
    (hLt : DerivedCategory.finiteTorAmplitude 𝐌 Y L)
    (hs : _root_.DerivedCategory.derivedCompleteIntegral Y.smallEtaleTopology l E
      (((derivedTensor 𝐌 Y).obj ((R(f)_![𝐌]).obj K)).obj L))
    (ht : _root_.DerivedCategory.derivedCompleteIntegral Y.smallEtaleTopology l E
      ((R(f)_![𝐌]).obj (((derivedTensor 𝐌 X).obj K).obj ((L((f)^*[𝐌])).obj L)))) :
    IsIso ((DerivedCategoryDerivedCompleteRational.fromIntegral Y.smallEtaleTopology l E).map
      (ObjectProperty.homMk
        (P := _root_.DerivedCategory.derivedCompleteIntegral Y.smallEtaleTopology l E)
        (X := ⟨_, hs⟩)
        (Y := ⟨_, ht⟩)
        (((projectionMap 𝐌 f).app K).app L))) := by
  refine @Functor.map_isIso _ _ _ _ _ _ _ _ ?_
  exact @isIso_of_fully_faithful _ _ _ _
    (_root_.DerivedCategory.derivedCompleteIntegral Y.smallEtaleTopology l E).ι _ _ _ _ _
    (hasProjectionFormula_of_derivedCompleteIntegral l E f K L hKc hK hKt hLc hL hLt hs ht)

/-- Blueprint `thm-sf-pf-field`: Rational and algebraically closed stages; the compatibility
with finite reduction.

For `K` and `L` bounded constructible, derived complete for `𝔪_E` and of finite Tor amplitude
over `𝒪_E`, the reduction modulo `𝔪_Eⁿ` of the integral projection map `PF_{f, K, L}`, the
representative of the projection map over `E`, is an isomorphism for every `n`: it is a
finite-level projection map, invertible by the argument of the finite projection formula
(`AlgebraicGeometry.Etale.isIso_reductionModIdeal_pow_map_projectionMap_of_boundedConstructible`,
which needs neither derived completeness nor the Tor amplitude of `L`). -/
theorem isIso_reductionModIdeal_pow_map_projectionMap (f : X ⟶ Y) [HasCompactification f]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology 𝐌))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology 𝐌))
    (hKc : DerivedCategory.boundedConstructible 𝐌 X K)
    (_hK : _root_.DerivedCategory.derivedCompleteIntegral X.smallEtaleTopology l E K)
    (hKt : DerivedCategory.finiteTorAmplitude 𝐌 X K)
    (hLc : DerivedCategory.boundedConstructible 𝐌 Y L)
    (_hL : _root_.DerivedCategory.derivedCompleteIntegral Y.smallEtaleTopology l E L)
    (_hLt : DerivedCategory.finiteTorAmplitude 𝐌 Y L) (n : ℕ) :
    IsIso ((reductionModIdeal _ Y (PadicAlgCl.maximalIdealShrink l E ^ n)).map
      (((projectionMap 𝐌 f).app K).app L)) :=
  isIso_reductionModIdeal_pow_map_projectionMap_of_boundedConstructible l E f K L hKc hKt hLc n

/-- Blueprint `sk-thm-sf-pf-field`: Projection formula: rational and algebraically closed
stages.

Let `f : X ⟶ Y` admit a compactification and let `E/ℚ_ℓ` be a finite extension inside `ℚ̄_ℓ`.
Let `K` and `L` be the rationalizations of bounded constructible objects of `D(X_ét, 𝒪_E)` and
`D(Y_ét, 𝒪_E)`, derived complete for `𝔪_E` and of finite Tor amplitude, such that both sides of
the integral projection map are derived complete. Then the projection map
`PF_{f, K, L} : Rf_! K ⊗ᴸ L ⟶ Rf_!(K ⊗ᴸ Lf^* L)` over `E`, the image of the integral projection
map under the extension functor `D_comp(Y_ét, 𝒪_E) ⥤ D_comp(Y_ét, E)`, is an isomorphism, and the
reductions modulo `𝔪_Eⁿ` of its integral representative are isomorphisms.

The stage `F = ℚ̄_ℓ` of the blueprint concerns objects represented at a finite stage `E'/ℚ_ℓ`:
for those this is the statement at `E = E'`, which is arbitrary here. -/
theorem hasProjectionFormula_field (f : X ⟶ Y) [HasCompactification f]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology 𝐌))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology 𝐌))
    (hKc : DerivedCategory.boundedConstructible 𝐌 X K)
    (hK : _root_.DerivedCategory.derivedCompleteIntegral X.smallEtaleTopology l E K)
    (hKt : DerivedCategory.finiteTorAmplitude 𝐌 X K)
    (hLc : DerivedCategory.boundedConstructible 𝐌 Y L)
    (hL : _root_.DerivedCategory.derivedCompleteIntegral Y.smallEtaleTopology l E L)
    (hLt : DerivedCategory.finiteTorAmplitude 𝐌 Y L)
    (hs : _root_.DerivedCategory.derivedCompleteIntegral Y.smallEtaleTopology l E
      (((derivedTensor 𝐌 Y).obj ((R(f)_![𝐌]).obj K)).obj L))
    (ht : _root_.DerivedCategory.derivedCompleteIntegral Y.smallEtaleTopology l E
      ((R(f)_![𝐌]).obj (((derivedTensor 𝐌 X).obj K).obj ((L((f)^*[𝐌])).obj L)))) :
    IsIso ((DerivedCategoryDerivedCompleteRational.fromIntegral Y.smallEtaleTopology l E).map
      (ObjectProperty.homMk
        (P := _root_.DerivedCategory.derivedCompleteIntegral Y.smallEtaleTopology l E)
        (X := ⟨_, hs⟩)
        (Y := ⟨_, ht⟩)
        (((projectionMap 𝐌 f).app K).app L))) ∧
    ∀ n : ℕ, IsIso ((reductionModIdeal _ Y (PadicAlgCl.maximalIdealShrink l E ^ n)).map
      (((projectionMap 𝐌 f).app K).app L)) :=
  ⟨isIso_fromIntegral_map_projectionMap l E f K L hKc hK hKt hLc hL hLt hs ht,
    isIso_reductionModIdeal_pow_map_projectionMap l E f K L hKc hK hKt hLc hL hLt⟩

end Etale

end AlgebraicGeometry
