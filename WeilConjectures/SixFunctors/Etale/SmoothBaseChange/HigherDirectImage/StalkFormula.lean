/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.CohomologyLimit
public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf

/-!
# Stalks of higher direct images at geometric points

Let `f : X ⟶ S` be quasi-compact and quasi-separated, `F` an étale sheaf of `Λ`-modules on `X`
and `s : Spec Ω ⟶ S` a geometric point. Then the geometric stalk of `R^q f_* F` at `s` is the
étale cohomology `H^q(S_(s) ×_S X, F|)` of the base change of `X` to the strict localization
`S_(s)` of `S` at `s` ([Stacks, Tag 03Q9], blueprint
`prop-weil-pbc-strict-henselization-stalk-formula`).

The proof follows the blueprint: `R^q f_* F` is the sheafification of the presheaf
`V ↦ H^q(V ×_S X, F|)`, so its stalk is the colimit of `H^q(V ×_S X, F|)` over the pointed étale
neighbourhoods `V` of `s`. The affine neighbourhoods are cofinal, `S_(s) ×_S X` is the limit of
the `V ×_S X` (`AlgebraicGeometry.Scheme.isLimitStrictLocalizationConePullback`) and the
continuity of étale cohomology
(`AlgebraicGeometry.Etale.exists_cohomologyRestrictOver_eq_of_isLimit`)
identifies the colimit of the cohomology groups with the cohomology of the limit.

## Main statements

- `AlgebraicGeometry.Etale.nonempty_geometricStalk_higherDirectImage_addEquiv`: the stalk
  formula `(R^q f_* F)_s ≅ H^q(S_(s) ×_S X, F|)`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Abelian

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- **Strict-henselization stalk formula** (blueprint
`prop-weil-pbc-strict-henselization-stalk-formula`): for a quasi-compact quasi-separated
`f : X ⟶ S`, a sheaf `F` of `Λ`-modules on `X_ét` and a geometric point `s : Spec Ω ⟶ S`, the
geometric stalk of `R^q f_* F` at `s` is the étale cohomology `H^q(S_(s) ×_S X, F|)` of the base
change of `X` to the strict localization `S_(s)`. -/
@[stacks 03Q9]
theorem nonempty_geometricStalk_higherDirectImage_addEquiv {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s : Spec (.of Ω) ⟶ S) (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ) :
    Nonempty ((Scheme.geometricStalkFunctor s (ModuleCat.{u + 1} Λ)).obj
        (Etale.higherDirectImage Λ f q F) ≃+
      Ext (SemiSimplicialObject.constSheaf
          (pullback (Scheme.strictLocalizationToBase s) f).smallEtaleTopology Λ)
        ((Etale.upperStar (ModuleCat.{u + 1} Λ)
          (pullback.snd (Scheme.strictLocalizationToBase s) f)).obj F) q) :=
  sorry

end AlgebraicGeometry.Etale
