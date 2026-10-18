/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix

/-!
# The typing table of the six operations

The typing table of the six-functor section (blueprint `sk-rem-sf-typing`) lists, for each
operation, where it is defined and the theorem showing that it descends to the small categories
`Dᵇc`, `Dctf` and `D_c^[a, b]`. This file collects these theorems, for a finite coefficient ring
whose exponent is invertible on an algebraically closed base field, in one statement
(`AlgebraicGeometry.Etale.sixOperations_typing`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

open _root_.AlgebraicGeometry.Etale.DerivedCategory

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {k : Type u} [Field k]
  [HasInvertibleExponent Λ (Spec (.of k))]
  {X Y : Scheme.{u}} (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k))
  [LocallyOfFiniteType aX] [QuasiCompact aX] [LocallyOfFiniteType aY] [QuasiCompact aY]
  (f : X ⟶ Y) (hf : f ≫ aY = aX)

include hf

/-- Blueprint `sk-rem-sf-typing`: Typing table: ambient definition, small-category theorem.

Let `Λ` be a finite ring whose exponent is invertible on an algebraically closed field `k`, and
`f : X ⟶ Y` a separated morphism of schemes of finite type over `k`, with `X` separated over
`k`. Each row of the table is a theorem:

* `Lf^*` maps `Dᵇc(Y) ⥤ Dᵇc(X)` and `Dctf(Y) ⥤ Dctf(X)`, preserving Tor amplitude `[a, b]`;
* `- ⊗ᴸ -` maps `Dᵇc × Dctf ⥤ Dᵇc` and `Dctf × Dctf ⥤ Dctf`, with `[a, b] + [c, d] ↦
  [a + c, b + d]`;
* `RHom(-, -)` maps `Dctf × Dctf ⥤ Dctf` for two arbitrary objects, with
  `[a, b], [c, d] ↦ [c - b - 2m, d - a + 2m]` if `dim X ≤ m`, and `[c - b, d - a]` for a
  site-perfect (dualizable) first argument;
* `Rf_*` maps `Dᵇc(X) ⥤ Dᵇc(Y)` and `Dctf(X) ⥤ Dctf(Y)`, and on the pro-étale site
  `[a, b] ↦ [a, b + 2 dim X]`;
* `Rf_!` maps `Dᵇc(X) ⥤ Dᵇc(Y)` and `Dctf(X) ⥤ Dctf(Y)`;
* `Rf^!` maps `Dctf(Y) ⥤ Dctf(X)` for every such `f`, shifting `D_c^[a, b]` (with Tor amplitude
  `[a, b]`) to `[a - 2d, b - 2d]` for `g` smooth of pure relative dimension `d`, to
  `[a, b + 2d + 1]` for a closed immersion `i` into a target of dimension `≤ d`, and to
  `[a - 2D, b + 2 dim Y + 1]` in general;
* `𝔻_X` maps `Dctf(X) ⥤ Dctf(X)` with `K ≅ 𝔻_X 𝔻_X K`, an anti-equivalence, and
  `[a, b] ↦ [-b - 2d, -a]` if `dim X ≤ d`.

The row `Rf^×` asserts nothing: it is an ambient functor used nowhere. The statement collects
`AlgebraicGeometry.Etale.boundedConstructible_preservation`,
`AlgebraicGeometry.Etale.constructibleFiniteTor_preservation`,
`AlgebraicGeometry.Etale.torAmplitudeIn_preservation`,
`AlgebraicGeometry.Etale.boundedConstructible_tensor` and the two shift estimates of
`sk-prop-sf-rf-shriek-preservation`. -/
theorem sixOperations_typing [QuasiCompact f] [HasCompactification f]
    [IsSeparated aX] [HasCompactification aX] [IsAlgClosed k] :
    ((∀ K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      boundedConstructible (ModuleCat.{u + 1} Λ) Y K →
        boundedConstructible (ModuleCat.{u + 1} Λ) X
          ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)) ∧
    (∀ K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      boundedConstructible (ModuleCat.{u + 1} Λ) X K →
        boundedConstructible (ModuleCat.{u + 1} Λ) Y
          ((R((f)_*[ModuleCat.{u + 1} Λ])).obj K)) ∧
    (∀ K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      boundedConstructible (ModuleCat.{u + 1} Λ) X K →
        boundedConstructible (ModuleCat.{u + 1} Λ) Y
          ((R(f)_![ModuleCat.{u + 1} Λ]).obj K))) ∧
    ((∀ K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y K →
        constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
          ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)) ∧
    (∀ K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K →
        constructibleFiniteTor (ModuleCat.{u + 1} Λ) X M →
          constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
            (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj K).obj M)) ∧
    (∀ K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K →
        constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y
          ((R((f)_*[ModuleCat.{u + 1} Λ])).obj K)) ∧
    (∀ K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K →
        constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y
          ((R(f)_![ModuleCat.{u + 1} Λ]).obj K)) ∧
    (∀ K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K →
        constructibleFiniteTor (ModuleCat.{u + 1} Λ) X M →
          constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
            (((RHom(X)[ModuleCat.{u + 1} Λ]).obj (op K)).obj M)) ∧
    (∀ K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y K →
        constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
          ((R(f)^![ModuleCat.{u + 1} Λ]).obj K)) ∧
    (∀ K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K →
        constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
          ((verdierDual (ModuleCat.{u + 1} Λ) aX).obj (op K)))) ∧
    ((∀ (a b : ℤ) (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      torAmplitudeIn (ModuleCat.{u + 1} Λ) Y a b K →
        torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)) ∧
    (∀ (a b c d : ℤ)
      (K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K →
        torAmplitudeIn (ModuleCat.{u + 1} Λ) X c d M →
          torAmplitudeIn (ModuleCat.{u + 1} Λ) X (a + c) (b + d)
            (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj K).obj M)) ∧
    (∀ d : ℕ, topologicalKrullDim X ≤ (d : WithBot ℕ∞) → ∀ (a b : ℤ)
      (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))),
      ProEtale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K →
        ProEtale.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K →
          ProEtale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y
              ((R(ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f)).obj K) ∧
            ProEtale.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) Y a (b + 2 * (d : ℤ))
              ((R(ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f)).obj K)) ∧
    (∀ m : ℕ, topologicalKrullDim X ≤ (m : WithBot ℕ∞) → ∀ (a b c d : ℤ)
      (K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      boundedConstructible (ModuleCat.{u + 1} Λ) X K →
        torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K →
          boundedConstructible (ModuleCat.{u + 1} Λ) X M →
            torAmplitudeIn (ModuleCat.{u + 1} Λ) X c d M →
              torAmplitudeIn (ModuleCat.{u + 1} Λ) X (c - b - 2 * (m : ℤ)) (d - a + 2 * (m : ℤ))
                (((RHom(X)[ModuleCat.{u + 1} Λ]).obj (op K)).obj M)) ∧
    (∀ (a b c d : ℤ)
      (K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      boundedConstructible (ModuleCat.{u + 1} Λ) X K →
        torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K → IsDualizable K →
          boundedConstructible (ModuleCat.{u + 1} Λ) X M →
            torAmplitudeIn (ModuleCat.{u + 1} Λ) X c d M →
              torAmplitudeIn (ModuleCat.{u + 1} Λ) X (c - b) (d - a)
                (((RHom(X)[ModuleCat.{u + 1} Λ]).obj (op K)).obj M)) ∧
    (∃ D : ℕ, ∀ d : ℕ, topologicalKrullDim Y ≤ (d : WithBot ℕ∞) → ∀ (a b : ℤ)
      (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      constructibleTorAmplitudeIn (ModuleCat.{u + 1} Λ) Y a b K →
        constructibleTorAmplitudeIn (ModuleCat.{u + 1} Λ) X (a - 2 * D) (b + 2 * d + 1)
          ((R(f)^![ModuleCat.{u + 1} Λ]).obj K)) ∧
    (∀ d : ℕ, topologicalKrullDim X ≤ (d : WithBot ℕ∞) → ∀ (a b : ℤ)
      (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      boundedConstructible (ModuleCat.{u + 1} Λ) X K →
        torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K →
          torAmplitudeIn (ModuleCat.{u + 1} Λ) X (-b - 2 * (d : ℤ)) (-a)
            ((verdierDual (ModuleCat.{u + 1} Λ) aX).obj (op K))) ∧
    (∀ K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K →
        constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
            ((verdierDual (ModuleCat.{u + 1} Λ) aX).obj (op K)) ∧
          Nonempty (K ≅ (verdierDual (ModuleCat.{u + 1} Λ) aX).obj
            (op ((verdierDual (ModuleCat.{u + 1} Λ) aX).obj (op K)))))) ∧
    (∀ K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      boundedConstructible (ModuleCat.{u + 1} Λ) X K →
        constructibleFiniteTor (ModuleCat.{u + 1} Λ) X M →
          boundedConstructible (ModuleCat.{u + 1} Λ) X
            (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj K).obj M)) ∧
    (∀ {X' : Scheme.{u}} (g : X' ⟶ Y) [HasCompactification g] (d : ℕ)
      [SmoothOfRelativeDimension d g] (a b : ℤ)
      (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      constructibleTorAmplitudeIn (ModuleCat.{u + 1} Λ) Y a b K →
        constructibleTorAmplitudeIn (ModuleCat.{u + 1} Λ) X' (a - 2 * d) (b - 2 * d)
          ((R(g)^![ModuleCat.{u + 1} Λ]).obj K)) ∧
    (∀ {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [HasCompactification i] (d : ℕ),
      topologicalKrullDim X ≤ (d : WithBot ℕ∞) → ∀ (a b : ℤ)
      (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      constructibleTorAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K →
        constructibleTorAmplitudeIn (ModuleCat.{u + 1} Λ) Z a (b + 2 * d + 1)
          ((R(i)^![ModuleCat.{u + 1} Λ]).obj K)) := by
  have : HasInvertibleExponent Λ X := .of_hom aX
  have : HasInvertibleExponent Λ Y := .of_hom aY
  refine ⟨boundedConstructible_preservation Λ aX aY f hf,
    constructibleFiniteTor_preservation Λ aX aY f hf,
    torAmplitudeIn_preservation Λ aX aY f hf,
    fun K M hK hM ↦ boundedConstructible_tensor Λ X hK hM.1 hM.2,
    fun g _ d _ a b K hK ↦
      constructibleTorAmplitudeIn_rightDerivedUpperShriek_of_smoothOfRelativeDimension Λ g d a b hK,
    fun i _ _ d hd a b K hK ↦
      constructibleTorAmplitudeIn_rightDerivedUpperShriek_of_isClosedImmersion Λ aX i d hd a b hK⟩

end Etale

end AlgebraicGeometry
