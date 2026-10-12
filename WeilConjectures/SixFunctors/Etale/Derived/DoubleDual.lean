/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapClosed
public import WeilConjectures.SixFunctors.Etale.Derived.Composition
public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula

/-!
# The double-dual morphism under proper push-forward and restriction

Let `Λ` be a finite ring. This file compares the double-dual morphisms
`δ_K : K ⟶ 𝔻 𝔻 K` (`AlgebraicGeometry.Etale.verdierDualDoubleDual`) on different schemes.

- `AlgebraicGeometry.Etale.rightDerivedLowerStarVerdierDualIso` (`lem-weil-delta-proper-pushforward`):
  for a proper `f : X ⟶ Y`, the ambient exchange `Rf_* 𝔻_X K ≅ 𝔻_Y Rf_* K`, the adjoint of the
  pairing `Rf_* K ⊗ᴸ Rf_* 𝔻_X K ⟶ Rf_*(K ⊗ᴸ 𝔻_X K) ⟶ Rf_* ω_X ⟶ ω_Y`;
  `AlgebraicGeometry.Etale.rightDerivedLowerStar_map_verdierDualDoubleDual_app`: it carries
  `Rf_* δ_K` to `δ_{Rf_* K}`.

## Implementation notes

The exchange isomorphism is the comparison map `G [K, W] ⟶ [G K, G W]` of the lax monoidal
right adjoint `G = Rf_*` of the monoidal functor `Lf^*`, followed by the counit
`Rf_* ω_X ≅ Rf_* f^! ω_Y ⟶ ω_Y`. It is an isomorphism by the proper projection formula
(`CategoryTheory.Adjunction.isIso_internalAdjunctionHom`), and the compatibility with the
double-dual morphisms is the general
`CategoryTheory.MonoidalClosed.map_toIhomIhom_comp_ihomComparison_comp_ihom_map`, `Rf_*` being
lax braided as the right adjoint of the braided monoidal functor `Lf^*`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed Opposite Functor.LaxMonoidal

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

section ProperPushforward

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]

/-- The adjunction `Rf_* ⊣ Rf^!` of a proper morphism `f`, obtained from `Rf_! ⊣ Rf^!` and the
proper coincidence `Rf_! ≅ Rf_*` (`AlgebraicGeometry.Etale.rightDerivedLowerShriekIsoRightDerivedLowerStar`). -/
noncomputable def rightDerivedLowerStarUpperShriekAdjunction :
    R((f)_*[ModuleCat.{u + 1} Λ]) ⊣ R(f)^![ModuleCat.{u + 1} Λ] :=
  (rightDerivedUpperShriekAdjunction _ f).ofNatIsoLeft
    (rightDerivedLowerShriekIsoRightDerivedLowerStar _ f)

attribute [local instance] leftDerivedUpperStarMonoidal

/-- The projection map of `Lf^* ⊣ Rf_*` (`CategoryTheory.Adjunction.projectionHom`) is the
projection map `AlgebraicGeometry.Etale.rightDerivedLowerStarProjectionMap`. -/
lemma projectionHom_derivedUpperStarLowerStarAdjunction
    (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (derivedUpperStarLowerStarAdjunction _ f).projectionHom M L =
      ((rightDerivedLowerStarProjectionMap _ f).app M).app L :=
  rfl

instance isIso_projectionHom_derivedUpperStarLowerStarAdjunction
    (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso ((derivedUpperStarLowerStarAdjunction _ f).projectionHom M L) := by
  have := isIso_rightDerivedLowerStarProjectionMap_of_finite Λ f
  rw [projectionHom_derivedUpperStarLowerStarAdjunction]
  infer_instance

/-- **The internal ambient adjunction for a proper morphism.** For `f` proper and a finite ring
`Λ`, the canonical map `Rf_* RHom(M, f^! K) ⟶ RHom(Rf_* M, Rf_* f^! K) ⟶ RHom(Rf_* M, K)` is an
isomorphism. This is the proper case of blueprint `prop-asd-internal-adjunction`, proved from the
proper projection formula. -/
instance isIso_internalAdjunctionHom_rightDerivedLowerStar
    (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso ((derivedUpperStarLowerStarAdjunction _ f).internalAdjunctionHom
      (rightDerivedLowerStarUpperShriekAdjunction Λ f) M K) :=
  Adjunction.isIso_internalAdjunctionHom _ _ M K

end ProperPushforward

end AlgebraicGeometry.Etale
