/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import Sheaf.AlgebraicGeometry.CumulativeUniversalBaseChangeProperty
public import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Sheaf.Paper.InverseImageStalkGerm
import Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.SixFunctors.Integral.BaseChange
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import Sheaf.Paper.ExchangeIdentityPasting
import Sheaf.AlgebraicGeometry.BaseChangeMapAbelianAndSets
import Sheaf.AlgebraicGeometry.IntegralEtaleDirectImageExact
import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Injectivity.CriticalMap
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

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

Proof plan:
1. The universal hypothesis gives the fixed-degree property for `f'`. Integrality of
   `π'` follows from integrality of `π`, using affine and universally closed permanence
   (`pqf-lem-integral-univclosed`, `lem-weil-pbc-affine-morphism-permanence`, and
   `lem-weil-pbc-universally-closed-base-change`).
2. Set `G = π_* π⁻¹ F`. On geometric stalks the adjunction unit `F → G` has a left inverse:
   represent a section on an etale neighbourhood, pull that neighbourhood to `T'`, and
   take its germ at a chosen lift of the geometric point. Surjectivity supplies such
   lifts, so stalk detection gives a monomorphism (`lem-weil-pbc-inverse-image-stalk-germ`,
   `lem-weil-pbc-geometric-stalks-detect-mono`).
3. Both inverse and direct image are additive, so `G` is still annihilated by `n`.
   Apply `sbc-lem-bc-injectivity`: the map at `F` is mono and its cokernel embeds into
   that at `G`.
4. The canonical integral underived exchange is invertible
   (`lem-sbc-integral-underived-exchange`). Integral direct image and inverse image are
   exact (`sbc-lem-integral-etale-direct-image-exact`,
   `prop-weil-pbc-inverse-image-modules-exact`). Apply that exchange termwise and use
   `lem-weil-pbc-exact-functor-derived-functor` to obtain the canonical derived exchange.
5. Derived pushforward composition identifies `Rg_* G` with `R(π ≫ g)_* π⁻¹ F` and
   similarly on the upper row (`lem-weil-pbc-ringed-topoi-derived-pushforward-composition`).
6. The vertical pasting identity (`lem-weil-pbc-exchange-identity-pasting`) identifies
   the map at `G`, followed by the invertible integral exchange, with the assumed
   map upstairs. Take degree-`q` cohomology, commuting exact inverse image with it
   (`lem-weil-pbc-exact-functor-complex-cohomology`). Thus the map at `G` is invertible.
7. Its cokernel vanishes, so the embedded cokernel at `F` vanishes. The map at `F`
   is both mono and epi and therefore an isomorphism. -/
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
  sorry

end AlgebraicGeometry.Etale
