/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.LocalizedChern

/-!
# The top Chern class of a vector bundle

The *top Chern class* (Euler class) `c_r(V) ∈ H^{2r}(T, Λ(r))` of a vector bundle `π : V ⟶ T` of
rank `r` is the localized top Chern class of the zero section with supports forgotten,
`c_r(V) = 0^* th(V)` (`AlgebraicGeometry.VectorBundle.topChernClass`). For a rank-one bundle this
is the first Chern class.

Property (L4) of `thm-pur-localized-top-chern` says that the localized top Chern class of *any*
section `s` becomes `c_r(V)` after forgetting supports
(`AlgebraicGeometry.VectorBundle.forgetSupports_localizedTopChern`); for a line bundle and a
section cutting out a divisor `D` this is the comparison `cl(D) = c₁(𝒪(D))` of
`lem-pur-divisor-class` (b) (`AlgebraicGeometry.VectorBundle.forgetSupports_localizedTopChern_one`).
Both rest on the homotopy invariance of the cohomology of the total space of a vector bundle (the
sections `s` and `0` are homotopic through `t s`, `t ∈ 𝔸¹`), which is not available in this
repository; they are stated here and not proved.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme Etale

namespace VectorBundle

variable {V T : Scheme.{u}} {r : ℕ} {π : V ⟶ T} (E : VectorBundle r π)
  (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasKummerClass Λ]
  [HasKummerClass.IsNormalized Λ] [HasInvertibleExponent Λ V]
  {k : Type u} [Field k] (aT : T ⟶ Spec (.of k)) [IsSeparated aT] [LocallyOfFiniteType aT]

/-- The localized top Chern class of a section `s`, with supports forgotten: a class in
`H^{2r}(T, Λ(r)) = Hom(Λ_T, Λ_T(r)[2r])`. -/
noncomputable def localizedTopChernForget (s : T ⟶ V) :
    haveI : HasInvertibleExponent Λ T := .of_hom E.zero
    constantComplex Λ T ⟶ (tateObject Λ T r)⟦2 * (r : ℤ)⟧ :=
  haveI : HasInvertibleExponent Λ T := .of_hom E.zero
  E.localizedTopChern s Λ aT ≫
    (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) (pullback.snd E.zero s)).counit.app _

/-- Blueprint `thm-pur-localized-top-chern`: the *top Chern class* (Euler class)
`c_r(V) ∈ H^{2r}(T, Λ(r))` of a vector bundle of rank `r`: the localized top Chern class of the
zero section with supports forgotten. For `r = 1` it is the first Chern class `c₁`. -/
noncomputable def topChernClass :
    haveI : HasInvertibleExponent Λ T := .of_hom E.zero
    constantComplex Λ T ⟶ (tateObject Λ T r)⟦2 * (r : ℤ)⟧ :=
  E.localizedTopChernForget Λ aT E.zero

/-- Blueprint `thm-pur-localized-top-chern`: Localized top Chern class

*(L4).* After forgetting supports, the localized top Chern class of any section `s` is the top
Chern class: `c_r(V, s) ↦ c_r(V)` in `H^{2r}(T, Λ(r))`.

Not proved here: the sections `s` and `0` are homotopic through `t s`, `t ∈ 𝔸¹`, and the
argument needs the homotopy invariance `Λ_T ≅ Rπ_* Λ_V` (through the unit) of the cohomology of
the total space, which this repository does not provide. -/
theorem forgetSupports_localizedTopChern (s : T ⟶ V) (hs : s ≫ π = 𝟙 T) :
    E.localizedTopChernForget Λ aT s = E.topChernClass Λ aT := by
  sorry

/-- Blueprint `lem-pur-divisor-class`: Divisor classes

*(b), the comparison with `c₁(𝒪(D))`.* For a line bundle `L` (a vector bundle of rank one) and a
section `s` with zero scheme `D = Z(s)`, the Kummer class `cl(D) = c₁(L, s)` of the divisor,
supports forgotten, is the first Chern class `c₁(L)`; the comparison does not depend on the
section. This is the case `r = 1` of (L4) of `thm-pur-localized-top-chern`
(`AlgebraicGeometry.VectorBundle.forgetSupports_localizedTopChern`). -/
theorem forgetSupports_localizedTopChern_one {π₁ : V ⟶ T} (L : VectorBundle 1 π₁) (s : T ⟶ V)
    (hs : s ≫ π₁ = 𝟙 T) :
    L.localizedTopChernForget Λ aT s = L.topChernClass Λ aT :=
  L.forgetSupports_localizedTopChern Λ aT s hs

end VectorBundle

end AlgebraicGeometry
