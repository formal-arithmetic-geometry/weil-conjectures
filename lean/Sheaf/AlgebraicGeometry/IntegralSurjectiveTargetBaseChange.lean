/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import Sheaf.AlgebraicGeometry.CumulativeUniversalBaseChangeProperty
import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.IntegralBaseChange

/-!
# Integral surjective base change on the target

Source: Stacks Project, Tag 0F04, Lemma `lemma-base-change-q-integral-top`;
blueprint, sec-smooth-base-change/sk-lem-universal-datum
(blueprint: sbc-lem-bc-integral-surjective).

The coefficient sheaves are modules over the size lift of `ZMod n`, equivalently
abelian sheaves annihilated by `n`, following the recorded coefficient convention.
The degreewise map is the existing bounded-below presentation of the recorded exchange.
-/

@[expose] public section

universe u

open CategoryTheory
open scoped AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

/-- Integral surjective target change detects the degree-`q` base-change isomorphism.
Source: Stacks Project, Tag 0F04, Lemma `lemma-base-change-q-integral-top`;
blueprint, sec-smooth-base-change/sk-lem-universal-datum
(blueprint: sbc-lem-bc-integral-surjective).

Proof: specialize the universal degree-`q - 1` hypothesis to the Cartesian base
change `f'`. Apply the existing arbitrary-coefficient integral-surjective target-change
theorem to `sq` and the pasted Cartesian square `sqπ.paste_vert sq`, with coefficient
ring `ULift (ZMod n)`. Surjectivity of the underlying map is the field of `Surjective π`.
The source theorem uses the same canonical bounded-below degreewise exchange map. -/
theorem isIso_baseChangeHomologyMap_of_integralSurjective_target
    {X S X' S' Y T Y' T' : Scheme.{u}} (f : X ⟶ S)
    (n : ℕ) (_hn : 0 < n) (_hinv : IsUnit (n : Γ(S, ⊤)))
    (q : ℕ) (_hq : 1 ≤ q)
    (_hprev : UniversalBaseChangeProperty (ULift.{u + 1} (ZMod n)) f ((q : ℤ) - 1))
    (a : S' ⟶ S) (b : X' ⟶ X) (f' : X' ⟶ S')
    (_sq₀ : IsPullback b f' f a)
    (g : T ⟶ S') (e : Y ⟶ T) (h : Y ⟶ X')
    [QuasiCompact g] [QuasiSeparated g] (sq : IsPullback e h g f')
    (π : T' ⟶ T) (π' : Y' ⟶ Y) (e' : Y' ⟶ T')
    [IsIntegralHom π] [Surjective π] (sqπ : IsPullback e' π' π e)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n))))
    (_hF : IsIso (baseChangeHomologyMap (ULift.{u + 1} (ZMod n))
      (sqπ.paste_vert sq) (q : ℤ)
      ((π)^*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n))].obj F))) :
    IsIso (baseChangeHomologyMap (ULift.{u + 1} (ZMod n)) sq (q : ℤ) F) := by
  exact isIso_baseChangeHomologyMap_of_isIntegralHom_of_surjective
    (ULift.{u + 1} (ZMod n)) (q : ℤ) (by omega) (_hprev a b f' _sq₀)
    sq π π.surjective (sqπ.paste_vert sq) F _hF

end AlgebraicGeometry.Etale
