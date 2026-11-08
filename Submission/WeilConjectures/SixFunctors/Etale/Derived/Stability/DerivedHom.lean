/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Submission.WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.VerdierBiduality

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Stability of `Dctf` under the internal hom

For a finite coefficient ring `Λ` whose exponent is invertible on schemes of finite type over an
algebraically closed field `k`, the internal hom `RHom(K, M)` of two objects of `Dctf` lies in
`Dctf`, with the Tor interval of blueprint `sk-thm-sf-hom-ctf`. As in the blueprint, this goes
through Verdier biduality: `RHom(K, M) ≅ 𝔻(𝔻M ⊗ᴸ K)`
(`AlgebraicGeometry.Etale.isIso_verdierDualDoubleDual_app`).

This file is part of `WeilConjectures.SixFunctors.Etale.Derived.Stability`, whose module
documentation records the implementation notes. The blueprint states these results over
`k = 𝔽̄_q`; the algebraic closedness of `k` is used by Verdier biduality.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

open _root_.AlgebraicGeometry.Etale.DerivedCategory

section Torsion

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {k : Type u} [Field k] [IsAlgClosed k]

section DualizingHom

variable [HasInvertibleExponent Λ (Spec (.of k))] {X : Scheme.{u}} (a : X ⟶ Spec (.of k))
  [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a] [HasCompactification a]

include a in
/-- Blueprint `cor-weil-finite-constructible-hom`: Internal Hom for arbitrary finite-stage
constructible complexes.

For `X` separated of finite type over a field `k` with `dim X ≤ d`, a finite coefficient ring `Λ`
whose exponent is invertible on `k`, and `K, L ∈ Dctf(X, Λ)` with Tor intervals `[p, q]` and
`[r, s]`, the internal hom `RHom(K, L)` is bounded constructible with Tor amplitude in
`[r - q - 2d, s - p + 2d]`. As in the blueprint, `RHom(K, L) ≅ 𝔻_X(𝔻_X L ⊗ᴸ K)` by biduality
(`AlgebraicGeometry.Etale.nonempty_iso_verdierDual_verdierDual`), and `𝔻_X` carries the Tor
interval `[r, s]` into `[-s - 2d, -r]` (`AlgebraicGeometry.Etale.torAmplitudeIn_verdierDual`). -/
theorem constructibleFiniteTor_derivedHom_of_isSeparated (d : ℕ)
    (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) {p q r s : ℤ}
    {K L : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : boundedConstructible (ModuleCat.{u + 1} Λ) X K)
    (hKt : torAmplitudeIn (ModuleCat.{u + 1} Λ) X p q K)
    (hL : boundedConstructible (ModuleCat.{u + 1} Λ) X L)
    (hLt : torAmplitudeIn (ModuleCat.{u + 1} Λ) X r s L) :
    boundedConstructible (ModuleCat.{u + 1} Λ) X
        ((RHom(X)[ModuleCat.{u + 1} Λ].obj (op K)).obj L) ∧
      torAmplitudeIn (ModuleCat.{u + 1} Λ) X (r - q - 2 * (d : ℤ))
        (s - p + 2 * (d : ℤ)) ((RHom(X)[ModuleCat.{u + 1} Λ].obj (op K)).obj L) := by
  have hL' : constructibleFiniteTor (ModuleCat.{u + 1} Λ) X L := ⟨hL, r, s, hLt⟩
  obtain ⟨e⟩ := nonempty_iso_verdierDual_verdierDual Λ a hL'
  obtain ⟨e'⟩ := nonempty_iso_derivedHom_verdierDual _ a K L e
  -- `𝔻_X L` has Tor amplitude in `[-s - 2d, -r]`, so `𝔻_X L ⊗ᴸ K` in `[p - s - 2d, q - r]`
  have hD := constructibleFiniteTor_verdierDual Λ a hL'
  have hDt := torAmplitudeIn_verdierDual Λ a d hd r s hL hLt
  have hT := constructibleFiniteTor_tensor Λ X hD ⟨hK, p, q, hKt⟩
  have hTt := torAmplitudeIn_tensor _ X _ _ _ _ hDt hKt
  have hDT := torAmplitudeIn_verdierDual Λ a d hd _ _ hT.1 hTt
  refine ⟨(boundedConstructible _ X).prop_of_iso e'.symm
    (constructibleFiniteTor_verdierDual Λ a hT).1, (torAmplitudeIn _ X _ _).prop_of_iso e'.symm ?_⟩
  exact hDT.mono (by omega) (by omega)

end DualizingHom

section DerivedHom

variable {X : Scheme.{u}} (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
  [HasInvertibleExponent Λ X] (m : ℕ) (hm : topologicalKrullDim X ≤ (m : WithBot ℕ∞))
  (a b c d : ℤ)
  {K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}

include aX in
/-- Blueprint `sk-thm-sf-hom-ctf`: Internal Hom with finite Tor amplitude.

For `X` of finite type over `k`, a finite `Λ` whose exponent is invertible on `X` and bounded
constructible `K` and `M` on `X_ét` of finite Tor amplitude, the internal hom `RHom(K, M)` is
bounded constructible. -/
theorem boundedConstructible_derivedHom
    (hK : boundedConstructible (ModuleCat.{u + 1} Λ) X K)
    (hKt : torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K)
    (hM : boundedConstructible (ModuleCat.{u + 1} Λ) X M)
    (hMt : torAmplitudeIn (ModuleCat.{u + 1} Λ) X c d M) :
    boundedConstructible (ModuleCat.{u + 1} Λ) X
      (((RHom(X)[ModuleCat.{u + 1} Λ]).obj (op K)).obj M) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace aX
  have : IsNoetherian X := { __ := LocallyOfFiniteType.isLocallyNoetherian aX }
  by_cases hX : IsEmpty X
  · exact boundedConstructible_of_openCover Λ (n := 0) Fin.elim0
      (fun x ↦ (hX.false x).elim) _ (fun i ↦ i.elim0)
  rw [not_isEmpty_iff] at hX
  have := HasInvertibleExponent.of_hom_of_nonempty (Λ := Λ) aX
  -- a finite cover by affine opens
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun V : X.affineOpens ↦ (V : Set X))
    (fun V ↦ V.1.isOpen) (fun x _ ↦ by
      obtain ⟨V, hV, hxV, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens)
        (show x ∈ (⊤ : X.Opens) from trivial)
      exact Set.mem_iUnion.2 ⟨⟨V, hV⟩, hxV⟩)
  let U : Fin t.card → X.Opens := fun i ↦ (t.equivFin.symm i).1.1
  refine boundedConstructible_of_openCover Λ U (fun x ↦ ?_) _ (fun i ↦ ?_)
  · obtain ⟨V, hV, hx⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
    exact ⟨t.equivFin ⟨V, hV⟩, by simpa [U] using hx⟩
  have : IsAffine (U i) := (t.equivFin.symm i).1.2
  let aU := (U i).ι ≫ aX
  obtain ⟨e⟩ := nonempty_iso_mapDerivedCategory_upperStar_derivedHom _ (U i).ι K M
  exact (boundedConstructible _ _).prop_of_iso e.symm
    (constructibleFiniteTor_derivedHom_of_verdierDual _ aU
      (constructibleFiniteTor_verdierDual Λ aU) (nonempty_iso_verdierDual_verdierDual Λ aU)
      (constructibleFiniteTor_tensor Λ _)
      (constructibleFiniteTor_mapDerivedCategory_upperStar Λ _ ⟨hK, a, b, hKt⟩)
      (constructibleFiniteTor_mapDerivedCategory_upperStar Λ _ ⟨hM, c, d, hMt⟩)).1

include aX hm in
/-- Blueprint `sk-thm-sf-hom-ctf`: Internal Hom with finite Tor amplitude.

If `K` and `M` have Tor amplitude in `[a, b]` and `[c, d]` and `dim X ≤ m`, then `RHom(K, M)`
has Tor amplitude in `[c - b - 2m, d - a + 2m]`. The blueprint derives this from
`RHom(K, M) ≅ 𝔻_X (K ⊗ᴸ 𝔻_X M)`, the dualizing complex having cohomology in `[-2m, 0]`. The
statement is local on `X`, and on the separated affine opens it is
`AlgebraicGeometry.Etale.constructibleFiniteTor_derivedHom_of_isSeparated`
(`cor-weil-finite-constructible-hom`). -/
theorem torAmplitudeIn_derivedHom
    (hK : boundedConstructible (ModuleCat.{u + 1} Λ) X K)
    (hKt : torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K)
    (hM : boundedConstructible (ModuleCat.{u + 1} Λ) X M)
    (hMt : torAmplitudeIn (ModuleCat.{u + 1} Λ) X c d M) :
    torAmplitudeIn (ModuleCat.{u + 1} Λ) X (c - b - 2 * (m : ℤ)) (d - a + 2 * (m : ℤ))
      (((RHom(X)[ModuleCat.{u + 1} Λ]).obj (op K)).obj M) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace aX
  have : IsNoetherian X := { __ := LocallyOfFiniteType.isLocallyNoetherian aX }
  by_cases hX : IsEmpty X
  · exact torAmplitudeIn_of_openCover _ (n := 0) Fin.elim0
      (fun x ↦ (hX.false x).elim) _ (fun i ↦ i.elim0)
  rw [not_isEmpty_iff] at hX
  have := HasInvertibleExponent.of_hom_of_nonempty (Λ := Λ) aX
  -- a finite cover by affine opens
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun V : X.affineOpens ↦ (V : Set X))
    (fun V ↦ V.1.isOpen) (fun x _ ↦ by
      obtain ⟨V, hV, hxV, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens)
        (show x ∈ (⊤ : X.Opens) from trivial)
      exact Set.mem_iUnion.2 ⟨⟨V, hV⟩, hxV⟩)
  let U : Fin t.card → X.Opens := fun i ↦ (t.equivFin.symm i).1.1
  refine torAmplitudeIn_of_openCover _ U (fun x ↦ ?_) _ (fun i ↦ ?_)
  · obtain ⟨V, hV, hx⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
    exact ⟨t.equivFin ⟨V, hV⟩, by simpa [U] using hx⟩
  have : IsAffine (U i) := (t.equivFin.symm i).1.2
  let aU := (U i).ι ≫ aX
  have hmU : topologicalKrullDim (U i) ≤ (m : WithBot ℕ∞) :=
    ((U i).ι.isOpenEmbedding.isInducing.topologicalKrullDim_le).trans hm
  obtain ⟨e⟩ := nonempty_iso_mapDerivedCategory_upperStar_derivedHom _ (U i).ι K M
  have hKt' : torAmplitudeIn (ModuleCat.{u + 1} Λ) (U i) a b
      (D(((U i).ι)^*[ModuleCat.{u + 1} Λ]).obj K) :=
    (torAmplitudeIn (ModuleCat.{u + 1} Λ) (U i) a b).prop_of_iso
      ((leftDerivedUpperStarIsoMapDerivedCategory _ (U i).ι).app K)
      (torAmplitudeIn_leftDerivedUpperStar _ (U i).ι a b hKt)
  have hMt' : torAmplitudeIn (ModuleCat.{u + 1} Λ) (U i) c d
      (D(((U i).ι)^*[ModuleCat.{u + 1} Λ]).obj M) :=
    (torAmplitudeIn (ModuleCat.{u + 1} Λ) (U i) c d).prop_of_iso
      ((leftDerivedUpperStarIsoMapDerivedCategory _ (U i).ι).app M)
      (torAmplitudeIn_leftDerivedUpperStar _ (U i).ι c d hMt)
  exact (torAmplitudeIn _ _ _ _).prop_of_iso e.symm
    (constructibleFiniteTor_derivedHom_of_isSeparated (Λ := Λ) (a := aU) m hmU
      (hK.mapDerivedCategory_upperStar (U i).ι) hKt'
      (hM.mapDerivedCategory_upperStar (U i).ι) hMt').2

-- `aX` and the coefficient hypotheses are part of the blueprint setting, unused by the proof
end DerivedHom

end Torsion

end Etale

end AlgebraicGeometry
