/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Deligne

/-!
# Generic constructibility of `Rj_*` after base change

Deligne's generic constructibility theorem
(`AlgebraicGeometry.Etale.exists_hasConstructibleDirectImageBaseChangeOn`) gives, over a nonempty
open `U` of the base, both the bounded constructibility of the direct image after every
noetherian base change into `U` and the base change isomorphism. This file isolates the first
part.

## Main statements

- `AlgebraicGeometry.Etale.exists_boundedConstructible_rightDerivedLowerStar_baseChange`:
  `Rj_{T,*}(g_X^* F)` is bounded constructible for every noetherian `T` over a nonempty open of
  the base.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- Let `S` be integral and of finite type over a field `k`, let `Λ` be a finite ring whose
exponent is invertible on `S`, and let `j : X ⟶ Y` be an open immersion of finite-type
`S`-schemes. For a constructible sheaf `F` of `Λ`-modules on `X`, there is a nonempty open
`U ⊆ S` such that for every noetherian `T` and every `t : T ⟶ S` with image in `U`, with base
change `j_T : X_T ⟶ Y_T` and projection `g_X : X_T ⟶ X`, the complex `Rj_{T,*}(g_X^* F)` is
bounded constructible. -/
theorem exists_boundedConstructible_rightDerivedLowerStar_baseChange {k : Type u} [Field k]
    {S X Y : Scheme.{u}} [IsIntegral S] (aS : S ⟶ Spec (.of k)) [LocallyOfFiniteType aS]
    [QuasiCompact aS] [HasInvertibleExponent Λ S] (fY : Y ⟶ S) [LocallyOfFiniteType fY]
    [QuasiCompact fY] (j : X ⟶ Y) [IsOpenImmersion j]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsConstructibleSheaf F] :
    ∃ U : S.Opens, (U : Set S).Nonempty ∧
      ∀ (T : Scheme.{u}) [IsNoetherian T] (t : T ⟶ S), Set.range t ⊆ U →
        ∀ (YT XT : Scheme.{u}) (g : YT ⟶ Y) (fT : YT ⟶ T) (g' : XT ⟶ X) (jT : XT ⟶ YT),
          IsPullback g fT fY t → IsPullback g' jT j g →
            DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) YT
              ((R((jT)_*[ModuleCat.{u + 1} Λ])).obj ((L((g')^*[ModuleCat.{u + 1} Λ])).obj
                ((_root_.DerivedCategory.singleFunctor _ 0).obj F))) := by
  obtain ⟨U, hU, h⟩ := exists_hasConstructibleDirectImageBaseChangeOn Λ aS fY j F
  exact ⟨U, hU, fun T _ t ht YT XT g fT g' jT hY hX ↦ (h T t ht YT XT g fT g' jT hY hX).1⟩

end Etale

end AlgebraicGeometry
