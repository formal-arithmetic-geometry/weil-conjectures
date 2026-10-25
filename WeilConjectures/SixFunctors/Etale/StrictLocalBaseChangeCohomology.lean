/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization
public import WeilConjectures.SixFunctors.Etale.ZModCoefficients

/-!
# Cohomology over the base change to a strict localization

Let `s` be a geometric point of a quasi-separated scheme `S`, `f : W ⟶ S` a morphism and
`W' = W ×_S S_(s)` the base change of the strict localization, assumed to be the spectrum of a
strictly henselian local ring (e.g. `W = S`, or `W` a closed subscheme of `S`). For a
quasi-compact quasi-separated `g : T ⟶ W` with base change `T' = T ×_W W'`, the cohomology of
the constant sheaf `ℤ/ℓ` on `T'` is the module of global sections over `W'` of the pullback of
`R^q g_* ℤ/ℓ`:

`H^q(T', ℤ/ℓ) ≅ Γ(W', u^* R^q g_* ℤ/ℓ)`.

Indeed, `u^* R^q g_* ≅ R^q g'_* e^*` by smooth base change in the limit form
(`AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_isPullback_strictLocalization`), the
global sections over the strictly local `W'` are exact, so the Leray spectral sequence of
`g' : T' ⟶ W'` degenerates, and the cohomology of a sheaf of `ℤ/ℓ`-modules is that of the
underlying abelian sheaf (`AlgebraicGeometry.Etale.forgetRightDerivedSectionsIso`).

## Main statements

- `AlgebraicGeometry.Etale.nonempty_addEquiv_sheafH_constantZMod_of_isPullback_strictLocalization`
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

open scoped AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

open Scheme

/-- **Cohomology over the base change to a strict localization.** Let `s` be a geometric point of
a quasi-separated scheme `S`, `f : W ⟶ S` a morphism, `W' = W ×_S S_(s)` (with projection
`uW : W' ⟶ W`) the spectrum of a strictly henselian local ring, `g : T ⟶ W` quasi-compact and
quasi-separated and `T' = T ×_W W'`. For a prime `ℓ` invertible on `W`,

`H^q(T', ℤ/ℓ) ≅ Γ(W', uW^* R^q g_* ℤ/ℓ)`. -/
theorem nonempty_addEquiv_sheafH_constantZMod_of_isPullback_strictLocalization
    {S : Scheme.{u}} [QuasiSeparatedSpace S] {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s : Spec (.of Ω) ⟶ S) {W W' : Scheme.{u}} (f : W ⟶ S) (uW : W' ⟶ W)
    (r : W' ⟶ strictLocalization s) (hW' : IsPullback uW r f (strictLocalizationToBase s))
    [IsAffine W'] [IsStrictlyHenselianLocalRing Γ(W', ⊤)]
    {T T' : Scheme.{u}} (g : T ⟶ W) [QuasiCompact g] [QuasiSeparated g]
    (e : T' ⟶ T) (h : T' ⟶ W') (sq : IsPullback e h g uW)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : Γ(W, ⊤))) (q : ℕ) :
    Nonempty (Sheaf.H (T'.constantZMod ℓ) q ≃+
      ((sectionsFunctor (ModuleCat.{u + 1} (ZModCoeff.{u} ℓ)) W').obj
        ((uW)^*[ModuleCat.{u + 1} (ZModCoeff.{u} ℓ)].obj
          (Etale.higherDirectImage (ZModCoeff.{u} ℓ) g q (constantZModModule T ℓ))))) := by
  sorry

end AlgebraicGeometry.Etale
