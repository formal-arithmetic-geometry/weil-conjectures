/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.DirectImageTorAmplitude
public import WeilConjectures.SixFunctors.Etale.Derived.DualityPullback
public import WeilConjectures.SixFunctors.Etale.Derived.HomTriangulated
public import WeilConjectures.SixFunctors.Etale.Derived.Perfect.SitePerfect
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix

/-!
# The six operations on `Dctf` at a finite coefficient stage

Let `k` be an algebraically closed field, `Λ` a finite ring whose exponent is invertible on `k`
(the finite stage `A = A_{E,n}`), and let `f : X ⟶ Y` be a separated morphism of separated
finite-type `k`-schemes. This file assembles the finite-stage stability theorem
`thm-sf-ctf-stability`, clauses (i)–(vi): the six operations preserve the constructible
complexes of finite Tor amplitude, with explicit Tor intervals, the exceptional inverse image is
`Rf^! ≅ 𝔻_X Lf^* 𝔻_Y` on `Dctf`, and the Verdier dual is an exact anti-equivalence of `Dctf`.

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_verdierDual_leftDerivedUpperStar`
  (`thm-sf-ctf-stability` (v)): `Rf^! K ≅ 𝔻_X Lf^* 𝔻_Y K` for `K ∈ Dctf(Y, Λ)`.
- `AlgebraicGeometry.Etale.torAmplitudeIn_rightDerivedUpperShriek_of_verdierDual`
  (`thm-sf-ctf-stability` (v)): the Tor interval `[a - 2 dim X, b + 2 dim Y]` of `Rf^! K`.
- `AlgebraicGeometry.Etale.constructibleFiniteTor_stability` (`thm-sf-ctf-stability`):
  clauses (i)–(vi) together.

## Implementation notes

The blueprint works over the algebraic closure of a finite field; only the algebraic closedness
of `k` is used (for biduality, `sk-prop-sf-biduality-general`). Site-perfect complexes
(`def-weil-site-perfect-complex`) are dualizable
(`AlgebraicGeometry.Etale.DerivedCategory.IsSitePerfect.isDualizable`), which is what the
sharper internal-Hom interval of clause (ii) uses. The anti-equivalence of clause (vi), as a
functor, is `AlgebraicGeometry.Etale.verdierDualEquivalence`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite Pretriangulated

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

open _root_.AlgebraicGeometry.Etale.DerivedCategory

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {k : Type u} [Field k] [IsAlgClosed k]
  [HasInvertibleExponent Λ (Spec (.of k))]
  {X Y : Scheme.{u}} (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k))
  [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX] [HasCompactification aX]
  [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY] [HasCompactification aY]

/-- Blueprint `thm-sf-ctf-stability`, clause (v): the exceptional inverse image on the
constructible finite-Tor category is `Rf^! = 𝔻_X f^* 𝔻_Y`.

For a morphism `f : X ⟶ Y` of separated finite-type `k`-schemes over `k` and `K ∈ Dctf(Y, Λ)`,

`Rf^! K ≅ 𝔻_X (Lf^* (𝔻_Y K))`.

By biduality (`sk-prop-sf-biduality-general`) `K ≅ 𝔻_Y 𝔻_Y K`, and duality against pullback
(`cor-sf-duality-pullback`) gives `𝔻_X Lf^* 𝔻_Y K ≅ Rf^! 𝔻_Y 𝔻_Y K`. -/
theorem nonempty_iso_rightDerivedUpperShriek_verdierDual_leftDerivedUpperStar
    (f : X ⟶ Y) (hf : f ≫ aY = aX)
    [HasCompactification f]
    {K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y K) :
    Nonempty ((R(f)^![ModuleCat.{u + 1} Λ]).obj K ≅
      (verdierDual (ModuleCat.{u + 1} Λ) aX).obj
        (op ((L((f)^*[ModuleCat.{u + 1} Λ])).obj
          ((verdierDual (ModuleCat.{u + 1} Λ) aY).obj (op K))))) := by
  subst hf
  obtain ⟨e⟩ := nonempty_iso_verdierDual_leftDerivedUpperStar Λ f aY
  obtain ⟨b⟩ := nonempty_iso_verdierDual_verdierDual Λ aY hK
  exact ⟨(R(f)^![ModuleCat.{u + 1} Λ]).mapIso b ≪≫
    (e.app (op ((verdierDual (ModuleCat.{u + 1} Λ) aY).obj (op K)))).symm⟩

/-- Blueprint `thm-sf-ctf-stability`, clause (v), the Tor interval: if `dim X ≤ d_X`,
`dim Y ≤ d_Y` and `K ∈ Dctf(Y, Λ)` has Tor amplitude in `[a, b]`, then `Rf^! K` has Tor
amplitude in `[a - 2 d_X, b + 2 d_Y]`.

Indeed `Rf^! K ≅ 𝔻_X Lf^* 𝔻_Y K`
(`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_verdierDual_leftDerivedUpperStar`);
the duality bound
(`lem-weil-verdier-preservation-strata`) on `Y` gives `𝔻_Y K` the interval `[-b - 2 d_Y, -a]`,
pullback preserves it, and the duality bound on `X` gives `[a - 2 d_X, b + 2 d_Y]`. -/
theorem torAmplitudeIn_rightDerivedUpperShriek_of_verdierDual (f : X ⟶ Y) (hf : f ≫ aY = aX)
    [HasCompactification f] (dX dY : ℕ) (hdX : topologicalKrullDim X ≤ (dX : WithBot ℕ∞))
    (hdY : topologicalKrullDim Y ≤ (dY : WithBot ℕ∞)) (a b : ℤ)
    {K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y K)
    (hKt : torAmplitudeIn (ModuleCat.{u + 1} Λ) Y a b K) :
    torAmplitudeIn (ModuleCat.{u + 1} Λ) X (a - 2 * (dX : ℤ)) (b + 2 * (dY : ℤ))
      ((R(f)^![ModuleCat.{u + 1} Λ]).obj K) := by
  obtain ⟨e⟩ :=
    nonempty_iso_rightDerivedUpperShriek_verdierDual_leftDerivedUpperStar Λ aX aY f hf hK
  have hD := constructibleFiniteTor_verdierDual Λ aY hK
  have hDt := torAmplitudeIn_verdierDual Λ aY dY hdY a b hK.1 hKt
  have hP := constructibleFiniteTor_leftDerivedUpperStar _ f hD
  have hPt := torAmplitudeIn_leftDerivedUpperStar _ f _ _ hDt
  have h := torAmplitudeIn_verdierDual Λ aX dX hdX _ _ hP.1 hPt
  refine (torAmplitudeIn (ModuleCat.{u + 1} Λ) X _ _).prop_of_iso e.symm ?_
  convert h using 2 <;> ring

/-- Blueprint `thm-sf-ctf-stability`: Preservation on the proved finite-Tor domains.

Let `k` be algebraically closed, `Λ` a finite ring whose exponent is invertible on `k` (the
finite stage `A = A_{E,n}`), and `f : X ⟶ Y` a morphism over `k` of separated finite-type
`k`-schemes (it is then separated of finite type). Then:

1. (i) `Lf^*` carries `Dctf(Y, Λ)` into `Dctf(X, Λ)`, preserving Tor intervals;
2. (ii) `⊗ᴸ` carries `Dctf × Dctf` into `Dctf`, with Tor intervals `[a, b]`, `[c, d]` going to
   `[a + c, b + d]`; so does the internal hom `RHom`; for `dim X ≤ m` and `K`, `L` of Tor
   amplitude in `[a, b]` and `[c, d]`, `RHom(K, L)` has Tor amplitude in
   `[c - b - 2m, d - a + 2m]`, and if `K` is site-perfect, `RHom(K, L) ≅ K^∨ ⊗ᴸ L` with
   `K^∨ = RHom(K, Λ_X)` and the Tor interval is `[c - b, d - a]`;
3. (iii) `Rf_*` carries `Dctf(X, Λ)` into `Dctf(Y, Λ)`, the Tor interval `[a, b]` going to
   `[a, b + 2d]` if `dim X ≤ d`;
4. (iv) `Rf_!` carries `Dctf(X, Λ)` into `Dctf(Y, Λ)`;
5. (v) `Rf^!` carries `Dctf(Y, Λ)` into `Dctf(X, Λ)` and `Rf^! ≅ 𝔻_X Lf^* 𝔻_Y` there; the Tor
   interval `[a, b]` goes to `[a - 2 dim X, b + 2 dim Y]`;
6. (vi) `𝔻_X = RHom(-, Ra_X^! Λ)` carries `Dctf(X, Λ)` into itself, is exact (it carries a
   distinguished triangle `K → L → M → K[1]` to a distinguished triangle
   `𝔻M → 𝔻L → 𝔻K → 𝔻M[1]`), and the double-dual map `K ⟶ 𝔻_X 𝔻_X K` is an isomorphism on
   `Dctf(X, Λ)`; so `𝔻_X` is an anti-equivalence of `Dctf(X, Λ)`
   (`AlgebraicGeometry.Etale.verdierDualEquivalence`).

The blueprint's example that the dimension-free interval of (ii) needs site-perfectness
(`RHom(i_* Λ, Λ) = i_* Λ(-1)[-2]` for the origin `i` of `𝔸¹`) is not formalised here.
Clause (vii), on coefficient reduction, is in
`WeilConjectures.SixFunctors.Etale.Derived.Stability.Reduction`. -/
theorem constructibleFiniteTor_stability (f : X ⟶ Y) (hf : f ≫ aY = aX) [HasCompactification f] :
    -- (i)
    (∀ K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y K →
        constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
          ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)) ∧
    (∀ (a b : ℤ) (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      torAmplitudeIn (ModuleCat.{u + 1} Λ) Y a b K →
        torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)) ∧
    -- (ii)
    (∀ K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K →
        constructibleFiniteTor (ModuleCat.{u + 1} Λ) X M →
          constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
            (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj K).obj M)) ∧
    (∀ (a b c d : ℤ)
      (K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K →
        torAmplitudeIn (ModuleCat.{u + 1} Λ) X c d M →
          torAmplitudeIn (ModuleCat.{u + 1} Λ) X (a + c) (b + d)
            (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj K).obj M)) ∧
    (∀ K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K →
        constructibleFiniteTor (ModuleCat.{u + 1} Λ) X M →
          constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
            (((RHom(X)[ModuleCat.{u + 1} Λ]).obj (op K)).obj M)) ∧
    (∀ m : ℕ, topologicalKrullDim X ≤ (m : WithBot ℕ∞) → ∀ (a b c d : ℤ)
      (K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K →
        torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K →
          constructibleFiniteTor (ModuleCat.{u + 1} Λ) X M →
            torAmplitudeIn (ModuleCat.{u + 1} Λ) X c d M →
              torAmplitudeIn (ModuleCat.{u + 1} Λ) X (c - b - 2 * (m : ℤ)) (d - a + 2 * (m : ℤ))
                (((RHom(X)[ModuleCat.{u + 1} Λ]).obj (op K)).obj M)) ∧
    (∀ (a b c d : ℤ)
      (K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K → IsSitePerfect K →
        torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K →
          constructibleFiniteTor (ModuleCat.{u + 1} Λ) X M →
            torAmplitudeIn (ModuleCat.{u + 1} Λ) X c d M →
              Nonempty ((((RHom(X)[ModuleCat.{u + 1} Λ]).obj (op K)).obj M) ≅
                ((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj
                  ((coefficientDual (ModuleCat.{u + 1} Λ) X).obj (op K))).obj M) ∧
              torAmplitudeIn (ModuleCat.{u + 1} Λ) X (c - b) (d - a)
                (((RHom(X)[ModuleCat.{u + 1} Λ]).obj (op K)).obj M)) ∧
    -- (iii)
    (∀ K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K →
        constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y
          ((R((f)_*[ModuleCat.{u + 1} Λ])).obj K)) ∧
    (∀ d : ℕ, topologicalKrullDim X ≤ (d : WithBot ℕ∞) → ∀ (a b : ℤ)
      (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K →
        torAmplitudeIn (ModuleCat.{u + 1} Λ) Y a (b + 2 * (d : ℤ))
          ((R((f)_*[ModuleCat.{u + 1} Λ])).obj K)) ∧
    -- (iv)
    (∀ K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K →
        constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y
          ((R(f)_![ModuleCat.{u + 1} Λ]).obj K)) ∧
    -- (v)
    (∀ K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y K →
        constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
            ((R(f)^![ModuleCat.{u + 1} Λ]).obj K) ∧
          Nonempty ((R(f)^![ModuleCat.{u + 1} Λ]).obj K ≅
            (verdierDual (ModuleCat.{u + 1} Λ) aX).obj
              (op ((L((f)^*[ModuleCat.{u + 1} Λ])).obj
                ((verdierDual (ModuleCat.{u + 1} Λ) aY).obj (op K)))))) ∧
    (∀ dX dY : ℕ, topologicalKrullDim X ≤ (dX : WithBot ℕ∞) →
      topologicalKrullDim Y ≤ (dY : WithBot ℕ∞) → ∀ (a b : ℤ)
      (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y K →
        torAmplitudeIn (ModuleCat.{u + 1} Λ) Y a b K →
          torAmplitudeIn (ModuleCat.{u + 1} Λ) X (a - 2 * (dX : ℤ)) (b + 2 * (dY : ℤ))
            ((R(f)^![ModuleCat.{u + 1} Λ]).obj K)) ∧
    -- (vi)
    (∀ K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K →
        constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
            ((verdierDual (ModuleCat.{u + 1} Λ) aX).obj (op K)) ∧
          IsIso ((verdierDualDoubleDual (ModuleCat.{u + 1} Λ) aX).app K)) ∧
    (∀ T ∈ distTriang (_root_.DerivedCategory (Sheaf X.smallEtaleTopology
        (ModuleCat.{u + 1} Λ))),
      ∃ w, Triangle.mk ((verdierDual (ModuleCat.{u + 1} Λ) aX).map T.mor₂.op)
        ((verdierDual (ModuleCat.{u + 1} Λ) aX).map T.mor₁.op) w ∈ distTriang _) := by
  have : HasInvertibleExponent Λ X := .of_hom aX
  have : HasInvertibleExponent Λ Y := .of_hom aY
  have : IsSeparated f := by
    have : IsSeparated (f ≫ aY) := hf ▸ inferInstance
    exact IsSeparated.of_comp f aY
  have : LocallyOfFiniteType f := by
    have : LocallyOfFiniteType (f ≫ aY) := hf ▸ inferInstance
    exact locallyOfFiniteType_of_comp f aY
  have : QuasiCompact f := by
    have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian aY
    have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace aY
    have : IsNoetherian Y := {}
    have : QuasiCompact (f ≫ aY) := hf ▸ inferInstance
    exact QuasiCompact.of_comp f aY
  refine ⟨fun K hK ↦ constructibleFiniteTor_leftDerivedUpperStar _ f hK,
    fun a b K hK ↦ torAmplitudeIn_leftDerivedUpperStar _ f a b hK,
    fun K M hK hM ↦ constructibleFiniteTor_tensor Λ X hK hM,
    fun a b c d K M hK hM ↦ torAmplitudeIn_tensor _ X a b c d hK hM,
    fun K M hK hM ↦ constructibleFiniteTor_derivedHom Λ aX hK hM,
    fun m hm a b c d K M hK hKt hM hMt ↦
      torAmplitudeIn_derivedHom Λ aX m hm a b c d hK.1 hKt hM.1 hMt,
    fun a b c d K M hK hKp hKt hM hMt ↦ ⟨?_,
      torAmplitudeIn_derivedHom_of_isDualizable Λ aX a b c d hK.1 hKt hKp.isDualizable hM.1 hMt⟩,
    fun K hK ↦ constructibleFiniteTor_rightDerivedLowerStar Λ aX aY f hf hK,
    fun d hd a b K hK ↦ torAmplitudeIn_rightDerivedLowerStar_of_finite Λ aX aY f hf d hd a b hK,
    fun K hK ↦ constructibleFiniteTor_rightDerivedLowerShriek Λ aY f hK,
    fun K hK ↦ ⟨constructibleFiniteTor_rightDerivedUpperShriek Λ aY f hK,
      nonempty_iso_rightDerivedUpperShriek_verdierDual_leftDerivedUpperStar Λ aX aY f hf hK⟩,
    fun dX dY hdX hdY a b K hK hKt ↦
      torAmplitudeIn_rightDerivedUpperShriek_of_verdierDual Λ aX aY f hf dX dY hdX hdY a b hK hKt,
    fun K hK ↦ ⟨constructibleFiniteTor_verdierDual Λ aX hK,
      isIso_verdierDualDoubleDual_app Λ aX hK⟩,
    fun T hT ↦ exists_distTriang_derivedHom_left _ T hT⟩
  obtain ⟨e⟩ := nonempty_iso_coefficientDual_tensor hKp.isDualizable M
  exact ⟨e.symm⟩

end Etale

end AlgebraicGeometry
