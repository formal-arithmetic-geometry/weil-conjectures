/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Derived.DirectImageFiniteness

/-!
# Finite-level amplification for a cartesian square

Let `A` be a commutative ring with an ideal `I`, and put `P_n = A ⧸ Iⁿ`. For a cartesian
square of schemes

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

the condition `AMP(□; c)` (`AlgebraicGeometry.ProEtale.FiniteLevelAmplification`, blueprint
`def-weil-pbc-finite-level-amplification`) asks, for every `n ≥ 1`, for the direct-image
finiteness conditions `FIN(f, P_n; c)` and `FIN(f', P_n; c)` and for the restriction of the
pullbacks `Lg^*`, `Lg'^*` to bounded constructible complexes preserving cohomological intervals.
The pullback clause always holds (`lem-weil-pbc-pullback-preserves-bounded-constructible`), see
`FiniteLevelAmplification.of_directImageFiniteness`.

Its consequences (`FiniteLevelAmplification.consequences`, blueprint
`prop-weil-pbc-amplification-consequences`) are the amplitude containments for the four
finite-level functors.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (A : Type (u + 1)) [CommRing A] (I : Ideal A)

/-- Blueprint `def-weil-pbc-finite-level-amplification`: the condition `AMP(□; c)` for a
cartesian square `□` (`sq : IsPullback g' f' f g`) and the coefficient quotients
`P_n = A ⧸ Iⁿ`: for every `n ≥ 1`,
1. the direct images satisfy `FIN(f, P_n; c)` and `FIN(f', P_n; c)`
   (`def-weil-pbc-constructible-direct-image-finiteness`);
2. the pullbacks `Lg^*`, `Lg'^*` send bounded constructible complexes of `P_n`-modules with
   cohomology in `[a, b]` to bounded constructible complexes with cohomology in `[a, b]`. -/
structure FiniteLevelAmplification {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y}
    {f' : X' ⟶ Y'} {g' : X' ⟶ X} (_sq : IsPullback g' f' f g) (c : ℕ) : Prop where
  directImageFiniteness (n : ℕ) (hn : 1 ≤ n) : DirectImageFiniteness (A ⧸ I ^ n) f c
  directImageFiniteness' (n : ℕ) (hn : 1 ≤ n) : DirectImageFiniteness (A ⧸ I ^ n) f' c
  pullback (n : ℕ) (hn : 1 ≤ n) {a b : ℤ}
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} (A ⧸ I ^ n)))}
    (hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} (A ⧸ I ^ n)) Y K)
    (hab : _root_.DerivedCategory.homologyConcentratedIn a b K) :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} (A ⧸ I ^ n)) Y'
        ((L(ProEtale.upperStar (ModuleCat.{u + 1} (A ⧸ I ^ n)) g)).obj K) ∧
      _root_.DerivedCategory.homologyConcentratedIn a b
        ((L(ProEtale.upperStar (ModuleCat.{u + 1} (A ⧸ I ^ n)) g)).obj K)
  pullback' (n : ℕ) (hn : 1 ≤ n) {a b : ℤ}
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (A ⧸ I ^ n)))}
    (hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} (A ⧸ I ^ n)) X K)
    (hab : _root_.DerivedCategory.homologyConcentratedIn a b K) :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} (A ⧸ I ^ n)) X'
        ((L(ProEtale.upperStar (ModuleCat.{u + 1} (A ⧸ I ^ n)) g')).obj K) ∧
      _root_.DerivedCategory.homologyConcentratedIn a b
        ((L(ProEtale.upperStar (ModuleCat.{u + 1} (A ⧸ I ^ n)) g')).obj K)

variable {A I}

namespace FiniteLevelAmplification

variable {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
  {sq : IsPullback g' f' f g} {c : ℕ}

/-- The pullback clause of `AMP(□; c)` is automatic
(`lem-weil-pbc-pullback-preserves-bounded-constructible`): `AMP(□; c)` holds as soon as the
two direct-image finiteness conditions hold at every level. -/
lemma of_directImageFiniteness (sq : IsPullback g' f' f g)
    (hf : ∀ n, 1 ≤ n → DirectImageFiniteness (A ⧸ I ^ n) f c)
    (hf' : ∀ n, 1 ≤ n → DirectImageFiniteness (A ⧸ I ^ n) f' c) :
    FiniteLevelAmplification A I sq c where
  directImageFiniteness := hf
  directImageFiniteness' := hf'
  pullback _ _ _ _ _ hK hab :=
    ⟨boundedConstructible_leftDerivedUpperStar g hK,
      homologyConcentratedIn_leftDerivedUpperStar g hab⟩
  pullback' _ _ _ _ _ hK hab :=
    ⟨boundedConstructible_leftDerivedUpperStar g' hK,
      homologyConcentratedIn_leftDerivedUpperStar g' hab⟩

/-- Blueprint `prop-weil-pbc-amplification-consequences`: under `AMP(□; c)` (and finite
quotients `P_n = A ⧸ Iⁿ`), for every `n ≥ 1` and every interval `[a, b]`:
`Rf_*` and `Rf'_*` send bounded constructible complexes of `P_n`-modules with cohomology in
`[a, b]` to bounded constructible complexes with cohomology in `[a, b + c]`
(`prop-weil-pbc-restriction-direct-image`), and `Lg^*`, `Lg'^*` preserve bounded
constructibility and the interval `[a, b]`. -/
theorem consequences (h : FiniteLevelAmplification A I sq c) (n : ℕ) (hn : 1 ≤ n)
    [Finite (A ⧸ I ^ n)] {a b : ℤ} :
    (∀ K : _root_.DerivedCategory
        (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (A ⧸ I ^ n))),
      DerivedCategory.boundedConstructible (ModuleCat.{u + 1} (A ⧸ I ^ n)) X K →
      _root_.DerivedCategory.homologyConcentratedIn a b K →
      DerivedCategory.boundedConstructible (ModuleCat.{u + 1} (A ⧸ I ^ n)) Y
          ((R(ProEtale.lowerStar (ModuleCat.{u + 1} (A ⧸ I ^ n)) f)).obj K) ∧
        _root_.DerivedCategory.homologyConcentratedIn a (b + c)
          ((R(ProEtale.lowerStar (ModuleCat.{u + 1} (A ⧸ I ^ n)) f)).obj K)) ∧
    (∀ K : _root_.DerivedCategory
        (Sheaf (Scheme.ProEt.topology X') (ModuleCat.{u + 1} (A ⧸ I ^ n))),
      DerivedCategory.boundedConstructible (ModuleCat.{u + 1} (A ⧸ I ^ n)) X' K →
      _root_.DerivedCategory.homologyConcentratedIn a b K →
      DerivedCategory.boundedConstructible (ModuleCat.{u + 1} (A ⧸ I ^ n)) Y'
          ((R(ProEtale.lowerStar (ModuleCat.{u + 1} (A ⧸ I ^ n)) f')).obj K) ∧
        _root_.DerivedCategory.homologyConcentratedIn a (b + c)
          ((R(ProEtale.lowerStar (ModuleCat.{u + 1} (A ⧸ I ^ n)) f')).obj K)) ∧
    (∀ K : _root_.DerivedCategory
        (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} (A ⧸ I ^ n))),
      DerivedCategory.boundedConstructible (ModuleCat.{u + 1} (A ⧸ I ^ n)) Y K →
      _root_.DerivedCategory.homologyConcentratedIn a b K →
      DerivedCategory.boundedConstructible (ModuleCat.{u + 1} (A ⧸ I ^ n)) Y'
          ((L(ProEtale.upperStar (ModuleCat.{u + 1} (A ⧸ I ^ n)) g)).obj K) ∧
        _root_.DerivedCategory.homologyConcentratedIn a b
          ((L(ProEtale.upperStar (ModuleCat.{u + 1} (A ⧸ I ^ n)) g)).obj K)) ∧
    (∀ K : _root_.DerivedCategory
        (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (A ⧸ I ^ n))),
      DerivedCategory.boundedConstructible (ModuleCat.{u + 1} (A ⧸ I ^ n)) X K →
      _root_.DerivedCategory.homologyConcentratedIn a b K →
      DerivedCategory.boundedConstructible (ModuleCat.{u + 1} (A ⧸ I ^ n)) X'
          ((L(ProEtale.upperStar (ModuleCat.{u + 1} (A ⧸ I ^ n)) g')).obj K) ∧
        _root_.DerivedCategory.homologyConcentratedIn a b
          ((L(ProEtale.upperStar (ModuleCat.{u + 1} (A ⧸ I ^ n)) g')).obj K)) :=
  ⟨fun _ hK hab ↦ (h.directImageFiniteness n hn).boundedConstructible_rightDerivedLowerStar hK hab,
    fun _ hK hab ↦
      (h.directImageFiniteness' n hn).boundedConstructible_rightDerivedLowerStar hK hab,
    fun _ hK hab ↦ h.pullback n hn hK hab, fun _ hK hab ↦ h.pullback' n hn hK hab⟩

end FiniteLevelAmplification

end AlgebraicGeometry.ProEtale
