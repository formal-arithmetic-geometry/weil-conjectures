/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.KunnethVerdierTransport

/-!

# The Künneth–Verdier map: the open–closed dévissage on the first factor

Let `Y` be separated of finite type over a field `k`, with structure morphism `b`, and fix
`N, ω ∈ D(Y_ét, Λ)` such that `ω` and `RHom(N, ω)` lie in `Dctf`. For `X` separated of finite type
over `k`, with projections `p : X ×_k Y ⟶ X` and `q : X ×_k Y ⟶ Y`, and `M ∈ Dctf(X, Λ)`,
consider the Künneth–Verdier map (`AlgebraicGeometry.Etale.kunnethVerdierMap`)

`κ_M : Lp^* M ⊗ᴸ Lq^* RHom(N, ω) ⟶ RHom(Lq^* N, Lp^* M ⊗ᴸ Lq^* ω)`.

For a closed immersion `i : Z ⟶ X` with open complement `j : U ⟶ X`, with base changes
`i' : Z ×_k Y ⟶ X ×_k Y` and `j' : U ×_k Y ⟶ X ×_k Y`, the map `Ri'^! κ_M` is `κ_{Ri^! M}` for
`Z` and `Lj'^* κ_M` is `κ_{Lj^* M}` for `U`
(`AlgebraicGeometry.Etale.isIso_map_kunnethVerdierMap_iff`): the tensor maps of `Ri'^!` and
`Rj'^!` are isomorphisms by supported localization and the ordinary Künneth formula, and the base
change maps by supported localization. As a map is an isomorphism once it is so after `Ri'^!`
and `Lj'^*`, `κ_M` is an isomorphism if `κ_{Ri^! M}` and `κ_{Lj^* M}` are
(`thm-trf-kunneth-verdier`, the dévissage of the blueprint proof).

## Main statements

- `AlgebraicGeometry.Etale.isIso_kunnethVerdierMap_of_isClosedImmersion_of_isOpenImmersion`
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

/-- **The dévissage step** (`thm-trf-kunneth-verdier`). Let `i : Z ⟶ X` be a closed immersion
with open complement `j : U ⟶ X`. If the Künneth–Verdier maps of `Ri^! M` on `Z ×_k Y` and of
`Lj^* M` on `U ×_k Y` are isomorphisms, then so is the Künneth–Verdier map of `M`. -/
theorem isIso_kunnethVerdierMap_of_isClosedImmersion_of_isOpenImmersion
    (hD : constructibleFiniteTor 𝓜 Y ((RHom(Y)[𝓜].obj (op N)).obj ω))
    (hω : constructibleFiniteTor 𝓜 Y ω) {X Z U : Scheme.{u}}
    (a : X ⟶ Spec (.of k)) [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    {M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology 𝓜)}
    (hM : constructibleFiniteTor 𝓜 X M)
    (hZ : IsIso (kunnethVerdierMap 𝓜 N ω (pullback.snd (i ≫ a) b)
      ((L((pullback.fst (i ≫ a) b)^*[𝓜])).obj ((R(i)^![𝓜]).obj M))))
    (hU : IsIso (kunnethVerdierMap 𝓜 N ω (pullback.snd (j ≫ a) b)
      ((L((pullback.fst (j ≫ a) b)^*[𝓜])).obj ((L((j)^*[𝓜])).obj M)))) :
    IsIso (kunnethVerdierMap 𝓜 N ω (pullback.snd a b) ((L((pullback.fst a b)^*[𝓜])).obj M)) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace a
  have : HasInvertibleExponent Λ X := .of_hom a
  have : HasCompactification j := (Compactification.ofIsOpenImmersion j).hasCompactification
  have : HasCompactification (pullbackMapLeft a b j) :=
    (Compactification.ofIsOpenImmersion _).hasCompactification
  have : QuasiCompact (pullbackMapLeft a b j) :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) (isPullback_pullbackMapLeft a b j)
      inferInstance
  have hij' := range_pullbackMapLeft_eq_compl a b i j hij
  have hdisj : Disjoint (Set.range (pullbackMapLeft a b i).base)
      (Set.range (pullbackMapLeft a b j).base) := by
    rw [hij']; exact disjoint_compl_left
  have sqi := isPullback_pullbackMapLeft a b i
  have sqj := isPullback_pullbackMapLeft a b j
  have wi : pullbackMapLeft a b i ≫ pullback.snd a b = pullback.snd (i ≫ a) b := by simp
  have wj : pullbackMapLeft a b j ≫ pullback.snd a b = pullback.snd (j ≫ a) b := by simp
  have hτi (B : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology 𝓜))
      (hB : constructibleFiniteTor 𝓜 Y B) :
      IsIso (rightDerivedUpperShriekTensorMap (pullbackMapLeft a b i)
        ((L((pullback.fst a b)^*[𝓜])).obj M) ((L((pullback.snd a b)^*[𝓜])).obj B)) :=
    isIso_rightDerivedUpperShriekTensorMap_of_isClosedImmersion Λ (pullbackMapLeft a b i)
      (pullbackMapLeft a b j) hij' _ _
      (exists_nonempty_iso_derivedTensor_rightDerivedLowerStar Λ b a j hM (Iso.refl _) hB)
  have hτj (B : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology 𝓜)) :
      IsIso (rightDerivedUpperShriekTensorMap (pullbackMapLeft a b j)
        ((L((pullback.fst a b)^*[𝓜])).obj M) ((L((pullback.snd a b)^*[𝓜])).obj B)) :=
    isIso_rightDerivedUpperShriekTensorMap_of_isOpenImmersion Λ (pullbackMapLeft a b j)
      (pullbackMapLeft a b i) hij' _ _
  refine isIso_of_isIso_rightDerivedUpperShriek_map_of_isIso_map Λ (pullbackMapLeft a b i)
    (pullbackMapLeft a b j) hij' _ ?_ ?_
  · rw [isIso_map_kunnethVerdierMap_iff N ω (pullbackMapLeft a b i)
      (projectionMapAssociativity Λ _) _ _ (hτi _ hD) (hτi _ hω),
      isIso_kunnethVerdierMap_congr N ω wi]
    have : IsIso ((rightDerivedUpperShriekBaseChangeMap Λ sqi).app M) :=
      isIso_rightDerivedUpperShriekBaseChangeMap_app_of_isClosedImmersion Λ sqi j hij
        (pullbackMapLeft a b j) hdisj _
        ⟨_, nonempty_iso_leftDerivedUpperStar_fst_rightDerivedLowerStar Λ b a j
          (constructibleFiniteTor_leftDerivedUpperStar _ j hM)⟩
    exact (isIso_kunnethVerdierMap_iff_of_iso N ω _
      (asIso ((rightDerivedUpperShriekBaseChangeMap Λ sqi).app M))).1 hZ
  · refine (NatIso.isIso_map_iff (rightDerivedUpperShriekIsoLeftDerivedUpperStar Λ
      (pullbackMapLeft a b j)) _).1 ?_
    rw [isIso_map_kunnethVerdierMap_iff N ω (pullbackMapLeft a b j)
      (projectionMapAssociativity Λ _) _ _ (hτj _) (hτj _),
      isIso_kunnethVerdierMap_congr N ω wj]
    exact (isIso_kunnethVerdierMap_iff_of_iso N ω _
      ((rightDerivedUpperShriekIsoLeftDerivedUpperStar Λ (pullbackMapLeft a b j)).app _ ≪≫
        ((leftDerivedUpperStarComp _ (pullbackMapLeft a b j) (pullback.fst a b)
          (pullback.fst (j ≫ a) b ≫ j) sqj.w).app M).symm ≪≫
        (leftDerivedUpperStarComp _ (pullback.fst (j ≫ a) b) j).app M)).2 hU

end Etale

end AlgebraicGeometry
