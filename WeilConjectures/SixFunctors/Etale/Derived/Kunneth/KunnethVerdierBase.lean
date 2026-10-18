/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.KunnethVerdierTransport

/-!

# The Künneth–Verdier map on the dualizable locus

Let `X`, `Y` be separated of finite type over a field `k`, with structure morphisms `a`, `b` and
projections `p : X ×_k Y ⟶ X`, `q : X ×_k Y ⟶ Y`, and let `N, ω ∈ D(Y_ét, Λ)` with `ω` and
`RHom(N, ω)` in `Dctf`. The Künneth–Verdier map (`AlgebraicGeometry.Etale.kunnethVerdierMap`)
`κ_M : Lp^* M ⊗ᴸ Lq^* RHom(N, ω) ⟶ RHom(Lq^* N, Lp^* M ⊗ᴸ Lq^* ω)` is an isomorphism

* for `M = ω_X`: by the constant coefficient exceptional Künneth formula
  (`AlgebraicGeometry.Etale.coreProp`), `Lp^* ω_X ≅ Rq^! Λ` and the tensor maps of `Rq^!` at the
  unit are isomorphisms, so `κ_{ω_X}` is the transport along `Rq^!` of the evaluation
  `RHom(N, ω) ≅ RHom(N, ω)`;
* for `M ≅ D ⊗ᴸ ω_X` with `D` dualizable, since tensoring with the dualizable `Lp^* D` commutes
  with internal homs.

This is the base of the dévissage in the proof of `thm-trf-kunneth-verdier`.

## Main statements

- `AlgebraicGeometry.Etale.isIso_kunnethVerdierMap_dualizingComplex`
- `AlgebraicGeometry.Etale.isIso_kunnethVerdierMap_of_iso_derivedTensor`
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

open _root_.AlgebraicGeometry.Etale.DerivedCategory

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

-- Search the braiding through the symmetric structure, as in the definition of the derived
-- tensor product: otherwise the monoidal structures found by instance search differ from the
-- ones of the canonical maps, and unifying them is very expensive.
attribute [local instance high] SymmetricCategory.toBraidedCategory

-- The coefficient category `ModuleCat Λ`.
set_option hygiene false in
local notation "𝓜" => ModuleCat.{u + 1} Λ

variable {k : Type u} [Field k] [HasInvertibleExponent Λ (Spec (.of k))]
  {Y : Scheme.{u}} (b : Y ⟶ Spec (.of k)) [IsSeparated b] [LocallyOfFiniteType b]
  [QuasiCompact b] (N ω : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology 𝓜))
  {X : Scheme.{u}} (a : X ⟶ Spec (.of k)) [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]

/-- **The Künneth–Verdier map at the dualizing complex** (`thm-trf-kunneth-verdier`): `κ_{ω_X}` is
an isomorphism. By the constant coefficient case of the exceptional Künneth formula
(`AlgebraicGeometry.Etale.coreProp`), `Lp^* ω_X ≅ Rq^! Λ` and the maps
`θ_{q, K} : ω_q ⊗ᴸ Lq^* K ⟶ Rq^! K` are isomorphisms for `K = RHom(N, ω)` and `K = ω`, so that
`κ_{Rq^! Λ}` is the transport along `Rq^!` of the Künneth map of the evaluation pairing at the
unit, `RHom(N, ω) ≅ RHom(N, Λ ⊗ᴸ ω)`. -/
theorem isIso_kunnethVerdierMap_dualizingComplex (hE : RightDerivedLowerShriekCompCoherence Λ)
    (hD : constructibleFiniteTor 𝓜 Y ((RHom(Y)[𝓜].obj (op N)).obj ω))
    (hω : constructibleFiniteTor 𝓜 Y ω) :
    IsIso (kunnethVerdierMap 𝓜 N ω (pullback.snd a b)
      ((L((pullback.fst a b)^*[𝓜])).obj (dualizingComplex 𝓜 a))) := by
  obtain ⟨hA, hθ⟩ := coreProp Λ b hE a
  have h₁ := isIso_rightDerivedUpperShriekTensorMap_unit_of_isIso (pullback.snd a b) _ (hθ _ hD)
  have h₂ := isIso_rightDerivedUpperShriekTensorMap_unit_of_isIso (pullback.snd a b) _ (hθ _ hω)
  have h := isIso_kunnethVerdierMap_rightDerivedUpperShriek_unit N ω (pullback.snd a b)
    (projectionMapAssociativity Λ _) h₁ h₂
  let eω : (R(pullback.snd a b)^![𝓜]).obj (𝟙_ _) ≅
      (L((pullback.fst a b)^*[𝓜])).obj (dualizingComplex 𝓜 a) :=
    ((R(pullback.snd a b)^![𝓜]).mapIso (leftDerivedUpperStarUnitIso _ b)).symm ≪≫
      (asIso ((rightDerivedUpperShriekBaseChangeMap Λ (IsPullback.of_hasPullback a b)).app
        (𝟙_ _))).symm
  exact (isIso_kunnethVerdierMap_iff_of_iso N ω _ eω).1 h

/-- **The Künneth–Verdier map on the dualizable locus** (`thm-trf-kunneth-verdier`): if
`M ≅ D ⊗ᴸ ω_X` for some `D` with a right dual, then `κ_M` is an isomorphism: tensoring with the
dualizable `Lp^* D` preserves the invertibility of `κ`
(`AlgebraicGeometry.Etale.isIso_kunnethVerdierMap_derivedTensor_of_exactPairing`), and `κ_{ω_X}`
is an isomorphism (`AlgebraicGeometry.Etale.isIso_kunnethVerdierMap_dualizingComplex`). -/
theorem isIso_kunnethVerdierMap_of_iso_derivedTensor
    (hE : RightDerivedLowerShriekCompCoherence Λ)
    (hD : constructibleFiniteTor 𝓜 Y ((RHom(Y)[𝓜].obj (op N)).obj ω))
    (hω : constructibleFiniteTor 𝓜 Y ω)
    (D F : _root_.DerivedCategory (Sheaf X.smallEtaleTopology 𝓜))
    [ExactPairing D F] {M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology 𝓜)}
    (e : M ≅ ((derivedTensor 𝓜 X).obj D).obj (dualizingComplex 𝓜 a)) :
    IsIso (kunnethVerdierMap 𝓜 N ω (pullback.snd a b) ((L((pullback.fst a b)^*[𝓜])).obj M)) := by
  have h := isIso_kunnethVerdierMap_derivedTensor_of_exactPairing N ω (pullback.snd a b)
    (pullback.fst a b) D F _ (isIso_kunnethVerdierMap_dualizingComplex Λ b N ω a hE hD hω)
  exact (isIso_kunnethVerdierMap_iff_of_iso N ω _ ((L((pullback.fst a b)^*[𝓜])).mapIso e ≪≫
    leftDerivedUpperStarTensorIso _ (pullback.fst a b) _ _)).2 h

end Etale

end AlgebraicGeometry
