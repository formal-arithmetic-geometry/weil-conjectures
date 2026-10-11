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
operations `Rf_!`, `⊗ᴸ` and `Lf^*` on rationalized objects are induced by the integral ones, which
are the derived completions of the plain operations of `D(Y_ét, 𝒪_E)` (see
`WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Integral`). So the projection map
`PF_{f, K, L}` over `E`, for `K` and `L` obtained by rationalization from `𝒪_E`-objects, is the
image of the integral projection map, the derived completion of the plain projection map, under
the localization functor `DerivedCategoryDerivedCompleteRational.fromIntegral`. This file proves
that it is an isomorphism (blueprint `thm-sf-pf-field`, rational stage), following the blueprint:
the integral projection map is an isomorphism (`sk-thm-sf-pf-adic`,
`AlgebraicGeometry.Etale.isIso_completion_map_projectionMap`), and a functor carries
isomorphisms to isomorphisms.

## Main statements

- `AlgebraicGeometry.Etale.isIso_fromIntegral_map_projectionMap` (`thm-sf-pf-field`): the
  projection formula over `E` for rationalizations of `𝒪_E`-objects.
- `AlgebraicGeometry.Etale.isIso_reductionModIdeal_pow_map_projectionMap` (`thm-sf-pf-field`):
  the reductions modulo `𝔪_Eⁿ` of the integral representative are isomorphisms.
- `AlgebraicGeometry.Etale.hasProjectionFormula_field` (`sk-thm-sf-pf-field`): both together.

## Implementation notes

The blueprint states these for rationalizations of bounded constructible, derived complete
`𝒪_E`-objects of finite Tor amplitude; the statements here hold for all `𝒪_E`-objects.

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

/-- Blueprint `thm-sf-pf-field`: Rational and algebraically closed stages; the rational stage.

Over `E`, the projection map `PF_{f, K, L} : Rf_! K ⊗ᴸ L ⟶ Rf_!(K ⊗ᴸ Lf^* L)` of the
rationalizations of `K, L` over `𝒪_E` is the image under the rationalization functor
`D_comp(Y_ét, 𝒪_E) ⥤ D_comp(Y_ét, E)` of the integral projection map, the derived completion of
the plain projection map. It is an isomorphism: the integral projection map is one
(`sk-thm-sf-pf-adic`, `AlgebraicGeometry.Etale.isIso_completion_map_projectionMap`) and the
rationalization functor carries isomorphisms to isomorphisms. The blueprint takes `K` and `L`
bounded constructible, derived complete and of finite Tor amplitude; this is not needed. -/
theorem isIso_fromIntegral_map_projectionMap (f : X ⟶ Y) [HasCompactification f]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology 𝐌))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology 𝐌)) :
    IsIso ((DerivedCategoryDerivedCompleteRational.fromIntegral Y.smallEtaleTopology l E).map
      ((DerivedCategoryDerivedCompleteIntegral.completion Y.smallEtaleTopology l E).map
        (((projectionMap 𝐌 f).app K).app L))) :=
  @Functor.map_isIso _ _ _ _ _ _ _ _ (isIso_completion_map_projectionMap l E f K L)

/-- Blueprint `thm-sf-pf-field`: Rational and algebraically closed stages; the compatibility
with finite reduction.

The reduction modulo `𝔪_Eⁿ` of the plain projection map `PF_{f, K, L}` over `𝒪_E`, whose derived
completion is the integral representative of the projection map over `E`, is an isomorphism for
every `n`: it is the finite-level projection map `PF_{f, K_n, L_n}`
(`AlgebraicGeometry.Etale.isIso_reductionModIdeal_maximalIdealShrink_pow_map_projectionMap`).
The blueprint takes `K` and `L` bounded constructible, derived complete and of finite Tor
amplitude; this is not needed. -/
theorem isIso_reductionModIdeal_pow_map_projectionMap (f : X ⟶ Y) [HasCompactification f]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology 𝐌))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology 𝐌)) (n : ℕ) :
    IsIso ((reductionModIdeal _ Y (PadicAlgCl.maximalIdealShrink l E ^ n)).map
      (((projectionMap 𝐌 f).app K).app L)) :=
  isIso_reductionModIdeal_maximalIdealShrink_pow_map_projectionMap l E f K L n

/-- Blueprint `sk-thm-sf-pf-field`: Projection formula: rational and algebraically closed
stages.

Let `f : X ⟶ Y` admit a compactification and let `E/ℚ_ℓ` be a finite extension inside `ℚ̄_ℓ`.
Let `K` and `L` be the rationalizations of objects of `D(X_ét, 𝒪_E)` and `D(Y_ét, 𝒪_E)` (in the
blueprint: bounded constructible, derived complete for `𝔪_E` and of finite Tor amplitude, which
is not needed). Then the projection map `PF_{f, K, L} : Rf_! K ⊗ᴸ L ⟶ Rf_!(K ⊗ᴸ Lf^* L)` over
`E`, the image of the integral projection map (the derived completion of the plain one) under the
extension functor `D_comp(Y_ét, 𝒪_E) ⥤ D_comp(Y_ét, E)`, is an isomorphism, and the reductions
modulo `𝔪_Eⁿ` of its integral representative are isomorphisms.

The stage `F = ℚ̄_ℓ` of the blueprint concerns objects represented at a finite stage `E'/ℚ_ℓ`:
for those this is the statement at `E = E'`, which is arbitrary here. -/
theorem hasProjectionFormula_field (f : X ⟶ Y) [HasCompactification f]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology 𝐌))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology 𝐌)) :
    IsIso ((DerivedCategoryDerivedCompleteRational.fromIntegral Y.smallEtaleTopology l E).map
      ((DerivedCategoryDerivedCompleteIntegral.completion Y.smallEtaleTopology l E).map
        (((projectionMap 𝐌 f).app K).app L))) ∧
    ∀ n : ℕ, IsIso ((reductionModIdeal _ Y (PadicAlgCl.maximalIdealShrink l E ^ n)).map
      (((projectionMap 𝐌 f).app K).app L)) :=
  ⟨isIso_fromIntegral_map_projectionMap l E f K L,
    isIso_reductionModIdeal_pow_map_projectionMap l E f K L⟩

end Etale

end AlgebraicGeometry
