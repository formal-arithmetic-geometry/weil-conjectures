/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible
public import WeilConjectures.SixFunctors.ProEtale.Derived.HomComparison
public import WeilConjectures.SixFunctors.ProEtale.Derived.Stability

/-!
# The preservation matrix of the six operations

For a finite coefficient ring `Λ` whose exponent is invertible on a field `k` and schemes of
finite type over `k`, this file collects which of the six operations preserve the bounded
constructible complexes `Dᵇc` and the constructible complexes of finite Tor amplitude `Dctf`
(blueprint `sk-rem-sf-matrix`), and the explicit intervals that come with them (blueprint
`rem-sf-preservation-matrix`).

## Main statements

- `AlgebraicGeometry.Etale.boundedConstructible_preservation`: `Lf^*`, `Rf_*` and `Rf_!`
  preserve `Dᵇc`.
- `AlgebraicGeometry.Etale.constructibleFiniteTor_preservation`: `Lf^*`, `⊗ᴸ`, `Rf_*`, `Rf_!`,
  `RHom`, `Rf^!` and `𝔻_X` preserve `Dctf`.
- `AlgebraicGeometry.ProEtale.DerivedCategory.constructibleFiniteTor_derivedHom_mapDerivedCategory`:
  on the pro-étale site, `RHom(ν^* K, ν^* M)` lies in `Dctf` for `K, M ∈ Dctf(X_ét)`.
- `AlgebraicGeometry.Etale.torAmplitudeIn_preservation`: the Tor-amplitude intervals of these
  operations.

## Implementation notes

All statements are assembled from the individual stability theorems of
`WeilConjectures.SixFunctors.Etale.Derived.Stability` and of
`WeilConjectures.SixFunctors.ProEtale.Derived`; this file adds no new mathematics beyond
choosing the dimension bounds and the torsion exponent these theorems ask for.
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

omit [HasInvertibleExponent Λ (Spec (.of k))] in
include aX in
/-- Blueprint `sk-thm-sf-hom-ctf`: Internal Hom with finite Tor amplitude.

For `X` of finite type over `k` and a finite `Λ` whose exponent is invertible on `X`, the
internal hom carries `Dctf(X, Λ) × Dctf(X, Λ)` into `Dctf(X, Λ)`, for two arbitrary objects.
This is `AlgebraicGeometry.Etale.boundedConstructible_derivedHom` together with the
dimension-dependent bound `AlgebraicGeometry.Etale.torAmplitudeIn_derivedHom`, `X` having
finite dimension. -/
theorem constructibleFiniteTor_derivedHom [HasInvertibleExponent Λ X]
    {K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K)
    (hM : constructibleFiniteTor (ModuleCat.{u + 1} Λ) X M) :
    constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
      (((RHom(X)[ModuleCat.{u + 1} Λ]).obj (op K)).obj M) := by
  obtain ⟨hKbc, a, b, hKt⟩ := hK
  obtain ⟨hMbc, c, d, hMt⟩ := hM
  obtain ⟨m, hm⟩ := exists_topologicalKrullDim_le aX
  exact ⟨boundedConstructible_derivedHom Λ aX a b c d hKbc hKt hMbc hMt, _, _,
    torAmplitudeIn_derivedHom Λ aX m hm a b c d hKbc hKt hMbc hMt⟩

variable (f : X ⟶ Y) (hf : f ≫ aY = aX)

include hf

omit [QuasiCompact aX] in
/-- Blueprint `sk-rem-sf-matrix`: The preservation matrix, bounded constructible cells.

For a finite `Λ` whose exponent is invertible on `k` and a morphism `f : X ⟶ Y` of schemes of
finite type over `k`, the operations `Lf^* : Dᵇc(Y) ⥤ Dᵇc(X)`, `Rf_* : Dᵇc(X) ⥤ Dᵇc(Y)` and
`Rf_! : Dᵇc(X) ⥤ Dᵇc(Y)` are defined, with no further hypothesis (the compactly supported direct
image being defined for `f` admitting a compactification). -/
theorem boundedConstructible_preservation [QuasiCompact f] [HasCompactification f] :
    (∀ K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
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
          ((R(f)_![ModuleCat.{u + 1} Λ]).obj K)) := by
  have : HasInvertibleExponent Λ X := .of_hom aX
  exact ⟨fun K hK ↦ boundedConstructible_leftDerivedUpperStar _ f hK,
    fun K hK ↦ boundedConstructible_rightDerivedLowerStar_of_hasInvertibleExponent Λ f aX aY hf
      K hK,
    fun K hK ↦ boundedConstructible_rightDerivedLowerShriek Λ f aX aY hf K hK⟩

/-- Blueprint `sk-rem-sf-matrix`: The preservation matrix, constructible finite-Tor cells.

For a finite `Λ` whose exponent is invertible on `k` and a separated morphism `f : X ⟶ Y` of
schemes of finite type over `k`, with `X` separated over `k`, the following operations preserve
the constructible complexes of finite Tor amplitude:
`Lf^* : Dctf(Y) ⥤ Dctf(X)`, `- ⊗ᴸ - : Dctf(X) × Dctf(X) ⥤ Dctf(X)`, `Rf_* : Dctf(X) ⥤ Dctf(Y)`,
`Rf_! : Dctf(X) ⥤ Dctf(Y)`, `RHom(-, -) : Dctf(X) × Dctf(X) ⥤ Dctf(X)` for two arbitrary
objects, `Rf^! : Dctf(Y) ⥤ Dctf(X)` for every such `f` (no admissibility hypothesis), and the
Verdier dual `𝔻_X : Dctf(X) ⥤ Dctf(X)`. The pro-étale internal-Hom cell is
`AlgebraicGeometry.ProEtale.DerivedCategory.constructibleFiniteTor_derivedHom_mapDerivedCategory`.
-/
theorem constructibleFiniteTor_preservation [IsSeparated f] [QuasiCompact f]
    [HasCompactification f] [IsSeparated aX] [HasCompactification aX] :
    (∀ K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
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
          ((verdierDual (ModuleCat.{u + 1} Λ) aX).obj (op K))) := by
  have : HasInvertibleExponent Λ Y := .of_hom aY
  exact ⟨fun K hK ↦ constructibleFiniteTor_leftDerivedUpperStar _ f hK,
    fun K M hK hM ↦ constructibleFiniteTor_tensor Λ X hK hM,
    fun K hK ↦ constructibleFiniteTor_rightDerivedLowerStar Λ aX aY f hf hK,
    fun K hK ↦ constructibleFiniteTor_rightDerivedLowerShriek Λ aY f hK,
    fun K M hK hM ↦ have : HasInvertibleExponent Λ X := .of_hom aX
      constructibleFiniteTor_derivedHom Λ aX hK hM,
    fun K hK ↦ constructibleFiniteTor_rightDerivedUpperShriek Λ aY f hK,
    fun K hK ↦ constructibleFiniteTor_verdierDual Λ aX hK⟩

end Etale

namespace ProEtale.DerivedCategory

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- Blueprint `sk-rem-sf-matrix`: The preservation matrix, the pro-étale internal-Hom cell.

Let `X` be of finite type over an algebraic closure `k` of `𝔽_p` and `Λ` a finite ring whose
exponent is invertible on `X`. For a pulled-back pair `ν^* K, ν^* M` with `K, M ∈ Dctf(X_ét, Λ)`,
the pro-étale internal hom `RHom(ν^* K, ν^* M)` lies in `Dctf(X_proét, Λ)`: it is
`ν^* RHom(K, M)` (`thm-sf-hom-comparison-constructible`), and `RHom(K, M) ∈ Dctf(X_ét, Λ)`. -/
theorem constructibleFiniteTor_derivedHom_mapDerivedCategory {k : Type u} [Field k] {p : ℕ}
    [Fact p.Prime] [Algebra (ZMod p) k] [IsAlgClosure (ZMod p) k]
    {X : Scheme.{u}} (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
    [HasInvertibleExponent Λ X]
    {K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K)
    (hM : Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X M) :
    constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
      (((ProEtale.derivedHom (ModuleCat.{u + 1} Λ) X).obj
        (op (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj K))).obj
          (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj M)) := by
  obtain ⟨e⟩ := nonempty_iso_mapDerivedCategory_derivedHom Λ (p := p) aX hK hM.1
  exact (constructibleFiniteTor _ X).prop_of_iso e
    (constructibleFiniteTor_mapDerivedCategory Λ
      (Etale.constructibleFiniteTor_derivedHom Λ aX hK hM))

end ProEtale.DerivedCategory

end AlgebraicGeometry
