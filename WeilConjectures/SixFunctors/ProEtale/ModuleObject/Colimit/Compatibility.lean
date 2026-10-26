/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients

/-!

# Compatibility of the six functors with the extension of `ℓ`-adic coefficients

Let `ℓ` be a prime, `E ≤ F` finite subextensions of `ℚ_ℓ` inside `ℚ̄_ℓ`
(`PadicAlgCl.FiniteIntermediateField ℓ`) and `Ω = ℚ̄_ℓ`. The inclusions of condensed rings
`E̲ ⟶ F̲` (`Profinite.padicSubfieldRingObjMap`) and `E̲ ⟶ ℚ̲̄_ℓ`
(`Profinite.padicSubfieldRingObjToPadicAlgCl`) of
`WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension` pull back, on a
scheme `X`, to coefficient changes `ι : E_X ⟶ F_X` and `ι : E_X ⟶ ℚ̄_ℓ,X`
(`ProEtale.coefficientMap`), inducing the derived extensions of scalars
```
T^X_{E,F} = F_X ⊗ᴸ_{E_X} - ,   T^X_{E,Ω} = ℚ̄_ℓ,X ⊗ᴸ_{E_X} - .
```
The comparisons (Pull), (Push) and (Shriek) between these and the derived functors `Lf^*`,
`Rf_*`, `Rf_!` on module objects are the ones of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients`, for these two
coefficient changes. This file defines the coefficient rings `E_X`, `ℚ̄_ℓ,X` and their
inclusions, and proves `ℚ̄_ℓ,X = colim_E E_X` (`ProEtale.isColimitPadicAlgClRingObjCocone`), the
pullback along the left adjoint `p_X^*` of `ℚ̲̄_ℓ = colim_E E̲`
(`Profinite.isColimitPadicAlgClRingObjCocone`).

The coefficient-specific input on the comparisons is in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.SubfieldFlat` and the files it
points to:

* both coefficient changes are flat, so that (Pull) and (Push) are defined on the unbounded
  derived categories, and (Pull) is an isomorphism there;
* for a finite extension `F/E`, (Push) is an isomorphism on all unbounded objects, hence so is
  (Shriek);
* for `E ⊆ Ω`, (Push) is an isomorphism at bounded below objects for every quasi-compact
  quasi-separated `f`, by the continuity of `Rf_*` on bounded below complexes
  (`ProEtale.CondensedRing.isIso_derivedPushHom_app_padicSubfieldRingObjToPadicAlgCl_of_isGE`,
  in `WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushPadicSubfieldFinite`), hence so is
  (Shriek) (`ProEtale.CondensedRing.isIso_derivedLowerShriekHom_app_padicAlgCl_of_isGE`). It is
  not an isomorphism on all unbounded objects, even for proper `f`: `Rf_*` need not commute
  with direct sums (blueprint `sk-rem-sf-fullcd-scope`), while `ℚ̄_ℓ ≅ ⨁_ℕ E` as `E`-modules.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl

/-! ### The coefficient rings `E_X`, `ℚ̄_ℓ,X` and their inclusions -/

section RingObj

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]

/-- The coefficient ring object `E_X = p_X^* E̲` on `X_proét`, for a finite subextension
`E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`. -/
noncomputable abbrev padicSubfieldRingObj (E : FiniteIntermediateField ℓ) :
    Sheaf (ProEt.topology X) Ab.{u + 1} :=
  condensedRingObj (Profinite.continuousMapRingObj E) X

/-- The coefficient ring object `ℚ̄_ℓ,X = p_X^* ℚ̲̄_ℓ` on `X_proét`. -/
noncomputable abbrev padicAlgClRingObj : Sheaf (ProEt.topology X) Ab.{u + 1} :=
  condensedRingObj (Profinite.padicAlgClRingObj ℓ) X

/-- The inclusion `E_X ⟶ F_X` for finite subextensions `E ≤ F`, the coefficient change induced by
the inclusion `E̲ ⟶ F̲` of condensed rings. -/
noncomputable abbrev padicSubfieldRingObjMap {E F : FiniteIntermediateField ℓ} (h : E ≤ F) :
    padicSubfieldRingObj X ℓ E ⟶ padicSubfieldRingObj X ℓ F :=
  coefficientMap (Profinite.padicSubfieldRingObjMap ℓ h) X

/-- The inclusion `E_X ⟶ ℚ̄_ℓ,X` for a finite subextension `E`, the coefficient change induced by
the inclusion `E̲ ⟶ ℚ̲̄_ℓ` of condensed rings. -/
noncomputable abbrev padicSubfieldRingObjToPadicAlgCl (E : FiniteIntermediateField ℓ) :
    padicSubfieldRingObj X ℓ E ⟶ padicAlgClRingObj X ℓ :=
  coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) X

/-- The inclusion `E_X ⟶ F_X` followed by the inclusion `F_X ⟶ ℚ̄_ℓ,X` is the inclusion
`E_X ⟶ ℚ̄_ℓ,X`. -/
@[reassoc]
lemma padicSubfieldRingObjMap_comp_toPadicAlgCl {E F : FiniteIntermediateField ℓ} (h : E ≤ F) :
    padicSubfieldRingObjMap X ℓ h ≫ padicSubfieldRingObjToPadicAlgCl X ℓ F =
      padicSubfieldRingObjToPadicAlgCl X ℓ E := by
  rw [← coefficientMap_comp, Profinite.padicSubfieldRingObjMap_comp_toPadicAlgCl]

/-- The inverse image `p_X^*` from condensed abelian groups is a left adjoint, being the
composite `π_X^* ∘ p^*` of two left adjoints. -/
instance isLeftAdjoint_upperStarFromPoint : (upperStarFromPoint X).IsLeftAdjoint :=
  (pointUpperStarLowerStarAdjunction.comp
    (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))).isLeftAdjoint

/-- The inverse image `p_X^*` is additive, being a left adjoint. -/
instance additive_upperStarFromPoint : (upperStarFromPoint X).Additive :=
  have adj : upperStarFromPoint X ⊣ _ := pointUpperStarLowerStarAdjunction.comp
    (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))
  have : (upperStarFromPoint X).IsLeftAdjoint := adj.isLeftAdjoint
  have := Functor.preservesZeroMorphisms_of_isLeftAdjoint (upperStarFromPoint X)
  have : PreservesColimitsOfSize.{0, 0} (upperStarFromPoint X) :=
    adj.leftAdjoint_preservesColimits
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (upperStarFromPoint X)
  Functor.additive_of_preservesBinaryBiproducts (upperStarFromPoint X)

/-- The cocone over the diagram `E ↦ E_X` with vertex `ℚ̄_ℓ,X`, given by the inclusions
`E_X ⟶ ℚ̄_ℓ,X`: the image under `p_X^*` of `Profinite.padicAlgClRingObjCocone`. -/
noncomputable abbrev padicAlgClRingObjCocone :
    Cocone (Profinite.padicSubfieldRingObjFunctor ℓ ⋙ upperStarFromPoint X) :=
  (upperStarFromPoint X).mapCocone (Profinite.padicAlgClRingObjCocone ℓ)

/-- **`ℚ̄_ℓ,X = colim_E E_X`**: the inclusions `E_X ⟶ ℚ̄_ℓ,X` exhibit `ℚ̄_ℓ,X` as the filtered
colimit of the `E_X` in abelian pro-étale sheaves on `X`. This is the image of
`ℚ̲̄_ℓ = colim_E E̲` (`Profinite.isColimitPadicAlgClRingObjCocone`) under the left adjoint
`p_X^*`. -/
noncomputable def isColimitPadicAlgClRingObjCocone : IsColimit (padicAlgClRingObjCocone X ℓ) :=
  isColimitOfPreserves (upperStarFromPoint X) (Profinite.isColimitPadicAlgClRingObjCocone ℓ)

end RingObj

end AlgebraicGeometry.ProEtale
