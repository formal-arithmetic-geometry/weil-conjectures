/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!
# Scheme-theoretically dense opens

The project uses Mathlib's `IsSchemeTheoreticallyDominant` (kernel ideal sheaf `⊥`) as the
definition of a scheme-theoretically dense open immersion. We show that for quasi-compact
morphisms this is equivalent to injectivity of all maps on sections, i.e. of
`𝒪_X → j_* 𝒪_U`, which is the blueprint's definition.

## Main results

- `AlgebraicGeometry.isSchemeTheoreticallyDominant_iff_app_injective`
  (blueprint: `def-nagata-scheme-theoretically-dense-open`).

This lemma belongs in
`WeilConjectures/Mathlib/AlgebraicGeometry/Morphisms/SchemeTheoreticallyDominant.lean`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

section AppInjective

/-- **Scheme-theoretic density via sections**: a quasi-compact morphism `f : X ⟶ Y` is
scheme-theoretically dominant if and only if every map on sections `f.app U` is injective,
i.e. the sheaf map `𝒪_Y ⟶ f_* 𝒪_X` is injective.

For a quasi-compact open immersion `j : U ⟶ X` this is the blueprint's definition of a
scheme-theoretically dense open (`𝒪_X → j_* 𝒪_U` injective). The project uses Mathlib's
`IsSchemeTheoreticallyDominant` (kernel ideal sheaf `⊥`) as the definition, and this
lemma identifies it with the blueprint's formulation.
(blueprint: `def-nagata-scheme-theoretically-dense-open`) -/
theorem isSchemeTheoreticallyDominant_iff_app_injective {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] :
    IsSchemeTheoreticallyDominant f ↔ ∀ U : Y.Opens, Function.Injective (f.app U) := by
  refine ⟨fun _ U ↦ f.app_injective U, fun h ↦ ⟨Scheme.IdealSheafData.ext ?_⟩⟩
  funext U
  rw [f.ker_apply U, Scheme.IdealSheafData.ideal_bot, Pi.bot_apply]
  exact (RingHom.injective_iff_ker_eq_bot _).mp (h U)

end AppInjective

end AlgebraicGeometry
