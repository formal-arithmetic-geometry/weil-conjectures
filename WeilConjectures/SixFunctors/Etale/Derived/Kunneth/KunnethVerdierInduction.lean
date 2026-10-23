/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.LisseLocus
public import WeilConjectures.SixFunctors.Etale.Derived.GenericFibre.InternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.GenericPerfect
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Formal
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.KunnethVerdierBase
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.KunnethVerdierDevissage
public import WeilConjectures.SixFunctors.Etale.Derived.Supports

/-!

# The Künneth–Verdier map: the induction on the dimension

Let `k` be an algebraically closed field, `X`, `Y` separated of finite type over `k` with
projections `p : X ×_k Y ⟶ X`, `q : X ×_k Y ⟶ Y`, and `N, ω ∈ D(Y_ét, Λ)` with `ω` and
`RHom(N, ω)` in `Dctf`. For every `M ∈ Dctf(X, Λ)` the Künneth–Verdier map
(`AlgebraicGeometry.Etale.kunnethVerdierMap`)

`κ_M : Lp^* M ⊗ᴸ Lq^* RHom(N, ω) ⟶ RHom(Lq^* N, Lp^* M ⊗ᴸ Lq^* ω)`

is an isomorphism (`thm-trf-kunneth-verdier`). The proof is by induction on `dim X`. The Verdier
dual `𝔻_X M` is dualizable on a dense open `j : U ⟶ X`
(`AlgebraicGeometry.Etale.exists_dense_open_exactPairing`), with left dual `D`; by biduality
`Lj^* M ≅ 𝔻_U 𝔻_U Lj^* M ≅ RHom(Lj^* 𝔻_X M, ω_U) ≅ D ⊗ᴸ ω_U`, so `κ_{Lj^* M}` is an isomorphism
(`AlgebraicGeometry.Etale.isIso_kunnethVerdierMap_of_iso_derivedTensor`). The closed complement
`i : Z ⟶ X` has smaller dimension, so `κ_{Ri^! M}` is an isomorphism by induction, and the
dévissage step
(`AlgebraicGeometry.Etale.isIso_kunnethVerdierMap_of_isClosedImmersion_of_isOpenImmersion`)
concludes.

## Main statements

- `AlgebraicGeometry.Etale.isIso_kunnethVerdierMap`
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

/-- An element of `WithBot ℕ∞` smaller than one which is smaller than `d + 1` is smaller
than `d`. -/
private lemma lt_natCast_of_lt_of_lt_add_one {x y : WithBot ℕ∞} {d : ℕ} (h₁ : x < y)
    (h₂ : y < ((d + 1 : ℕ) : WithBot ℕ∞)) : x < (d : WithBot ℕ∞) := by
  induction y using WithBot.recBotCoe with
  | bot => simp at h₁
  | coe e =>
    induction x using WithBot.recBotCoe with
    | bot => exact WithBot.bot_lt_coe _
    | coe f =>
      have h₁' : f < e := WithBot.coe_lt_coe.1 h₁
      have h₂' : e < ((d + 1 : ℕ) : ℕ∞) := WithBot.coe_lt_coe.1 h₂
      have hf : f < (d : ℕ∞) := by
        have hf' : f ≠ ⊤ := ne_top_of_lt h₁'
        have h3 : f + 1 ≤ e := (ENat.add_one_le_iff hf').2 h₁'
        have h4 : f + 1 < (d : ℕ∞) + 1 := by push_cast at h₂'; exact lt_of_le_of_lt h3 h₂'
        exact (ENat.add_lt_add_iff_right ENat.one_ne_top).1 h4
      exact WithBot.coe_lt_coe.2 hf

variable {k : Type u} [Field k] [IsAlgClosed k] [HasInvertibleExponent Λ (Spec (.of k))]
  {Y : Scheme.{u}} (b : Y ⟶ Spec (.of k)) [IsSeparated b] [LocallyOfFiniteType b]
  [QuasiCompact b] (N ω : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology 𝓜))

omit [Finite Λ] [IsAlgClosed k] [HasInvertibleExponent Λ (Spec (.of k))] [IsSeparated b]
  [LocallyOfFiniteType b] [QuasiCompact b] in
/-- The Künneth–Verdier map of an empty scheme `X` is an isomorphism, `D((X ×_k Y)_ét)` being
zero. -/
lemma isIso_kunnethVerdierMap_of_isEmpty {X : Scheme.{u}} [IsEmpty X] (a : X ⟶ Spec (.of k))
    (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology 𝓜)) :
    IsIso (kunnethVerdierMap 𝓜 N ω (pullback.snd a b) ((L((pullback.fst a b)^*[𝓜])).obj M)) := by
  have : IsEmpty ↥(pullback a b) := ⟨fun x ↦ IsEmpty.false ((pullback.fst a b).base x)⟩
  exact IsZero.isIso
    (_root_.DerivedCategory.isZero_of_forall_isZero (Scheme.Etale.isZero_sheaf_of_isEmpty ·) _)
    (_root_.DerivedCategory.isZero_of_forall_isZero (Scheme.Etale.isZero_sheaf_of_isEmpty ·) _) _

/-- On the dense open `j : V ⟶ X` where `𝔻_X M` has a left dual `D`, `Lj^* M ≅ D ⊗ᴸ ω_V`: by
biduality and duality against pullback,
`Lj^* M ≅ 𝔻_V 𝔻_V Lj^* M ≅ RHom(Lj^* 𝔻_X M, ω_V) ≅ D ⊗ᴸ ω_V`. -/
lemma nonempty_iso_leftDerivedUpperStar_derivedTensor_dualizingComplex {X : Scheme.{u}}
    (a : X ⟶ Spec (.of k)) [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    (V : X.Opens) [QuasiCompact V.ι]
    {M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology 𝓜)}
    (hM : constructibleFiniteTor 𝓜 X M)
    (D : _root_.DerivedCategory (Sheaf V.toScheme.smallEtaleTopology 𝓜))
    [ExactPairing D ((L((V.ι)^*[𝓜])).obj ((verdierDual 𝓜 a).obj (op M)))] :
    Nonempty ((L((V.ι)^*[𝓜])).obj M ≅
      ((derivedTensor 𝓜 V).obj D).obj (dualizingComplex 𝓜 (V.ι ≫ a))) := by
  have : HasCompactification V.ι := (Compactification.ofIsOpenImmersion V.ι).hasCompactification
  obtain ⟨bi⟩ := nonempty_iso_verdierDual_verdierDual Λ (V.ι ≫ a)
    (constructibleFiniteTor_leftDerivedUpperStar _ V.ι hM)
  obtain ⟨c⟩ := nonempty_iso_verdierDual_leftDerivedUpperStar Λ a V.ι M
  let c' := c ≪≫ (rightDerivedUpperShriekIsoLeftDerivedUpperStar Λ V.ι).app _
  exact ⟨bi ≪≫ ((RHom(V)[𝓜]).mapIso c'.symm.op).app (dualizingComplex 𝓜 (V.ι ≫ a)) ≪≫
    derivedHomIsoDerivedTensorOfExactPairing 𝓜 D _ _⟩

/-- **The induction on the dimension** (`thm-trf-kunneth-verdier`): for `X` separated of finite
type over `k` of dimension `< d` and `M ∈ Dctf(X, Λ)`, the Künneth–Verdier map `κ_M` is an
isomorphism. On a dense open `j : V ⟶ X` where `𝔻_X M` is dualizable, `Lj^* M ≅ D ⊗ᴸ ω_V` with
`D` dualizable; its closed complement has smaller dimension. -/
theorem isIso_kunnethVerdierMap_of_topologicalKrullDim_lt
    (hE : RightDerivedLowerShriekCompCoherence Λ)
    (hD : constructibleFiniteTor 𝓜 Y ((RHom(Y)[𝓜].obj (op N)).obj ω))
    (hω : constructibleFiniteTor 𝓜 Y ω) (d : ℕ) :
    ∀ {X : Scheme.{u}} (a : X ⟶ Spec (.of k)) [IsSeparated a] [LocallyOfFiniteType a]
      [QuasiCompact a], topologicalKrullDim X < d →
      ∀ {M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology 𝓜)},
        constructibleFiniteTor 𝓜 X M →
        IsIso (kunnethVerdierMap 𝓜 N ω (pullback.snd a b)
          ((L((pullback.fst a b)^*[𝓜])).obj M)) := by
  induction d with
  | zero =>
    intro X a _ _ _ hX M _
    rcases isEmpty_or_nonempty X with hXe | hXe
    · exact isIso_kunnethVerdierMap_of_isEmpty Λ b N ω a M
    · exact absurd hX (not_lt.2 (by simpa using topologicalKrullDim_nonneg (X := X)))
  | succ d ih =>
    intro X a _ _ _ hX M hM
    rcases isEmpty_or_nonempty X with hXe | hXe
    · exact isIso_kunnethVerdierMap_of_isEmpty Λ b N ω a M
    have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace a
    have : IsNoetherian X := { __ := LocallyOfFiniteType.isLocallyNoetherian a }
    have : HasInvertibleExponent Λ X := .of_hom a
    obtain ⟨V, hVd, hV⟩ :=
      exists_dense_open_exactPairing Λ (constructibleFiniteTor_verdierDual Λ a hM)
    obtain ⟨D, -, ⟨ep⟩⟩ := hV V le_rfl
    have : TopologicalSpace.NoetherianSpace V := V.ι.isOpenEmbedding.isInducing.noetherianSpace
    have : QuasiCompact V.ι := ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
    have hij : Set.range V.closedComplement.base = (Set.range V.ι.base)ᶜ := by simp
    refine isIso_kunnethVerdierMap_of_isClosedImmersion_of_isOpenImmersion Λ b N ω hD hω a
      V.closedComplement V.ι hij hM ?_ ?_
    · have key : ∀ {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i],
          Set.range i.base = (V : Set X)ᶜ →
            topologicalKrullDim Z ≤ topologicalKrullDim ((V : Set X)ᶜ : Set X) :=
        fun i _ hi ↦ (i.isClosedEmbedding.isInducing.codRestrict
          (fun z ↦ by rw [← hi]; exact ⟨z, rfl⟩)).topologicalKrullDim_le
      have h₁ := key V.closedComplement (by simp)
      have h₂ := topologicalKrullDim_compl_lt_of_dense (X := X) (ne_top_of_lt hX) hVd V.isOpen
      exact ih (V.closedComplement ≫ a)
        (lt_natCast_of_lt_of_lt_add_one (lt_of_le_of_lt h₁ h₂) hX)
        (constructibleFiniteTor_rightDerivedUpperShriek_of_comp Λ a _ M hM)
    · obtain ⟨e⟩ := nonempty_iso_leftDerivedUpperStar_derivedTensor_dualizingComplex Λ a V hM D
      exact isIso_kunnethVerdierMap_of_iso_derivedTensor Λ b N ω (V.ι ≫ a) hE hD hω D
        ((L((V.ι)^*[𝓜])).obj ((verdierDual 𝓜 a).obj (op M))) e

/-- **The Künneth–Verdier map is an isomorphism** (`thm-trf-kunneth-verdier`): for `X`
separated of finite type over `k` and `M ∈ Dctf(X, Λ)`, the Künneth–Verdier map
`κ_M : Lp^* M ⊗ᴸ Lq^* RHom(N, ω) ⟶ RHom(Lq^* N, Lp^* M ⊗ᴸ Lq^* ω)` is an isomorphism, by
induction on the dimension of `X`
(`AlgebraicGeometry.Etale.isIso_kunnethVerdierMap_of_topologicalKrullDim_lt`). -/
theorem isIso_kunnethVerdierMap (hE : RightDerivedLowerShriekCompCoherence Λ)
    (hD : constructibleFiniteTor 𝓜 Y ((RHom(Y)[𝓜].obj (op N)).obj ω))
    (hω : constructibleFiniteTor 𝓜 Y ω) {X : Scheme.{u}} (a : X ⟶ Spec (.of k))
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    {M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology 𝓜)}
    (hM : constructibleFiniteTor 𝓜 X M) :
    IsIso (kunnethVerdierMap 𝓜 N ω (pullback.snd a b) ((L((pullback.fst a b)^*[𝓜])).obj M)) := by
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_le a
  exact isIso_kunnethVerdierMap_of_topologicalKrullDim_lt Λ b N ω hE hD hω (d + 1) a
    (lt_of_le_of_lt hd (by exact_mod_cast Nat.lt_succ_self d)) hM

end Etale

end AlgebraicGeometry
