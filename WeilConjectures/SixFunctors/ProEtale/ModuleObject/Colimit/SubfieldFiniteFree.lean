/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.MapModFiniteFree
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapFiniteFree
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility

/-!
# `F_X` is finite free over `E_X`

For finite subextensions `E ≤ F` of `ℚ̄_ℓ / ℚ_ℓ` and a scheme `X`, the coefficient ring `F_X`,
regarded as an `E_X`-module through the inclusion `E_X ⟶ F_X`, is finite free
(blueprint `sk-prop-sfb-cartesian-coefficients` (2)), of rank `[F : E]`: an `E`-basis of `F` has
continuous coordinates, so that `C(S, F) ≅ C(S, E)ᵈ` as `C(S, E)`-modules, naturally in the
profinite set `S` (`Profinite.comapRegularIsoFiniteFree`), and this isomorphism of condensed
modules is transported to `X` along the additive monoidal functor `p_X^*`
(`CategoryTheory.Functor.comapRegularIsoFiniteFree`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime] {E F : FiniteIntermediateField ℓ} (h : E ≤ F)

/-- Blueprint `sk-prop-sfb-cartesian-coefficients` (2): for finite subextensions `E ≤ F`, the
coefficient ring `F_X`, regarded as an `E_X`-module, is finite free, of a rank independent of
the scheme `X`. -/
theorem exists_comap_regular_iso_finiteFree :
    ∃ d : ℕ, ∀ X : Scheme.{u},
      Nonempty ((Mod.comap (padicSubfieldRingObjMap X ℓ h)).obj
          (Mod.regular (padicSubfieldRingObj X ℓ F)) ≅
        Mod.finiteFree (padicSubfieldRingObj X ℓ E) d) := by
  let : Algebra E F := (IntermediateField.inclusion h).toRingHom.toAlgebra
  have : IsScalarTower ℚ_[ℓ] E F := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : FiniteDimensional E F := Module.Finite.of_restrictScalars_finite ℚ_[ℓ] E F
  refine ⟨Module.finrank E F, fun X ↦ ?_⟩
  have adj : upperStarFromPoint X ⊣ _ := pointUpperStarLowerStarAdjunction.comp
    (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))
  have := Functor.preservesZeroMorphisms_of_isLeftAdjoint (upperStarFromPoint X)
  have : PreservesColimitsOfSize.{0, 0} (upperStarFromPoint X) :=
    adj.leftAdjoint_preservesColimits
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (upperStarFromPoint X)
  have := Functor.additive_of_preservesBinaryBiproducts (upperStarFromPoint X)
  exact ⟨(upperStarFromPoint X).comapRegularIsoFiniteFree _
    (Profinite.comapRegularIsoFiniteFree (continuous_subtype_val.subtype_mk _)
      (Module.finBasis E F) fun i ↦
        (((Module.finBasis E F).coord i).restrictScalars ℚ_[ℓ]).continuous_of_finiteDimensional)⟩

end AlgebraicGeometry.ProEtale.CondensedRing
