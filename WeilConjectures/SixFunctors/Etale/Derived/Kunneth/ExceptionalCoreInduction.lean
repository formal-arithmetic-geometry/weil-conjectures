/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.ExceptionalCore
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!

# The exceptional Künneth formula for constant coefficients: affine spaces, affine schemes and
the induction

This file completes the proof that the canonical maps of `AlgebraicGeometry.Etale.CoreProp` are
isomorphisms for every `X` separated of finite type over a field `k`:

- for the affine space `𝔸ⁿ_k`, which is smooth, by cohomological smoothness (`sk-prop-cohsm`)
  and smooth base change for `R^!` (`prop-asd-smooth-base-change`);
- for a closed subscheme of `X` once they are for `X`, by supported localization and the
  ordinary Künneth formula (`AlgebraicGeometry.Etale.coreProp_comp_of_isClosedImmersion`);
- hence for affine `X`, a closed subscheme of some `𝔸ⁿ_k`;
- and for general `X` by induction on the number of affine opens covering `X`, through the
  open–closed decomposition `X = U ⊔ Z` with `U` one of them
  (`AlgebraicGeometry.Etale.coreProp_of_isClosedImmersion_of_isOpenImmersion`).

## Main statements

- `AlgebraicGeometry.Etale.coreProp`
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

/-- An affine scheme of finite type over a field `k` is a closed subscheme of an affine space
`𝔸ⁿ_k` over `k`: a finite set of generators of its ring of functions as a `k`-algebra gives a
closed immersion `V ⟶ 𝔸ⁿ_k` over `k`. -/
theorem exists_isClosedImmersion_affineSpace_of_isAffine {k : Type u} [Field k] {V : Scheme.{u}}
    [IsAffine V] (aV : V ⟶ Spec (.of k)) [LocallyOfFiniteType aV] :
    ∃ (n : Type u) (_ : Finite n) (ι : V ⟶ 𝔸(n; Spec (.of k))),
      IsClosedImmersion ι ∧ ι ≫ 𝔸(n; Spec (.of k)) ↘ Spec (.of k) = aV := by
  have hft : aV.appTop.hom.FiniteType :=
    (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).mp inferInstance
  let := aV.appTop.hom.toAlgebra
  obtain ⟨s, hs⟩ := hft.out
  refine ⟨s, inferInstance, AffineSpace.homOfVector aV (Subtype.val : s → Γ(V, ⊤)), ?_,
    AffineSpace.homOfVector_over _ _⟩
  refine AffineSpace.isClosedImmersion_homOfVector _ _ ?_
  have h := congrArg Subalgebra.toSubring hs
  rw [Algebra.adjoin_eq_ring_closure, Algebra.top_toSubring] at h
  rw [eq_top_iff, ← h]
  refine Subring.closure_mono ?_
  rintro y (⟨a, rfl⟩ | hy)
  · exact Or.inl ⟨a, rfl⟩
  · exact Or.inr ⟨⟨y, hy⟩, rfl⟩

namespace Etale

open _root_.AlgebraicGeometry.Etale.DerivedCategory

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

-- Search the braiding through the symmetric structure, as in the definition of the derived
-- tensor product: otherwise the monoidal structures found by instance search differ from the
-- ones of the canonical maps, and unifying them is very expensive.
attribute [local instance high] SymmetricCategory.toBraidedCategory

variable {k : Type u} [Field k] [HasInvertibleExponent Λ (Spec (.of k))]
  {T : Scheme.{u}} (b : T ⟶ Spec (.of k)) [IsSeparated b] [LocallyOfFiniteType b]
  [QuasiCompact b]

section ClosedImmersion

variable {X Z : Scheme.{u}} (a : X ⟶ Spec (.of k)) [IsSeparated a] [LocallyOfFiniteType a]
  [QuasiCompact a] (i : Z ⟶ X) [IsClosedImmersion i]

/-- The base change map of `Ri^!` along the projection `X ×_k T ⟶ X`, at the dualizing complex
`ω_X`, is an isomorphism, for a closed immersion `i`
(`AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekBaseChangeMap_app_of_isClosedImmersion`
and the ordinary Künneth formula with an identity factor). -/
lemma isIso_rightDerivedUpperShriekBaseChangeMap_pullbackMapLeft_dualizingComplex :
    IsIso ((rightDerivedUpperShriekBaseChangeMap Λ (isPullback_pullbackMapLeft a b i)).app
      ((R(a)^![ModuleCat.{u + 1} Λ]).obj (𝟙_ _))) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace a
  have : IsNoetherian X := { __ := LocallyOfFiniteType.isLocallyNoetherian a }
  obtain ⟨U, hiU, -⟩ := exists_openImmersion_range_compl i
  have : TopologicalSpace.NoetherianSpace U := U.ι.isOpenEmbedding.isInducing.noetherianSpace
  have : QuasiCompact U.ι := ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  have hω : constructibleFiniteTor (ModuleCat.{u + 1} Λ) X (dualizingComplex _ a) :=
    constructibleFiniteTor_dualizingComplex Λ (𝟙 _) a (constructibleFiniteTor_tensorUnit Λ _)
  have hdisj : Disjoint (Set.range (pullbackMapLeft a b i).base)
      (Set.range (pullbackMapLeft a b U.ι).base) := by
    rw [range_pullbackMapLeft_eq_compl a b i U.ι hiU]; exact disjoint_compl_left
  exact isIso_rightDerivedUpperShriekBaseChangeMap_app_of_isClosedImmersion Λ
    (isPullback_pullbackMapLeft a b i) U.ι hiU (pullbackMapLeft a b U.ι) hdisj _
    ⟨_, nonempty_iso_leftDerivedUpperStar_fst_rightDerivedLowerStar Λ b a U.ι
      (constructibleFiniteTor_leftDerivedUpperStar _ U.ι hω)⟩

/-- The tensor map of the base change `i' : Z ×_k T ⟶ X ×_k T` of a closed immersion `i`, at
`(ω_π, Lπ^* M)` for the projection `π : X ×_k T ⟶ T`, is an isomorphism once `ω_π` is pulled
back from `ω_X` (`AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekTensorMap_of_isClosedImmersion`
and the ordinary Künneth formula with an identity factor). -/
lemma isIso_rightDerivedUpperShriekTensorMap_pullbackMapLeft
    (hA : IsIso ((rightDerivedUpperShriekBaseChangeMap Λ (IsPullback.of_hasPullback a b)).app
      (𝟙_ _)))
    {M : _root_.DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hM : constructibleFiniteTor (ModuleCat.{u + 1} Λ) T M) :
    IsIso (rightDerivedUpperShriekTensorMap (pullbackMapLeft a b i)
      ((R(pullback.snd a b)^![ModuleCat.{u + 1} Λ]).obj (𝟙_ _))
      ((L((pullback.snd a b)^*[ModuleCat.{u + 1} Λ])).obj M)) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace a
  have : IsNoetherian X := { __ := LocallyOfFiniteType.isLocallyNoetherian a }
  obtain ⟨U, hiU, -⟩ := exists_openImmersion_range_compl i
  have : TopologicalSpace.NoetherianSpace U := U.ι.isOpenEmbedding.isInducing.noetherianSpace
  have : QuasiCompact U.ι := ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  have hω : constructibleFiniteTor (ModuleCat.{u + 1} Λ) X (dualizingComplex _ a) :=
    constructibleFiniteTor_dualizingComplex Λ (𝟙 _) a (constructibleFiniteTor_tensorUnit Λ _)
  let eω : (R(pullback.snd a b)^![ModuleCat.{u + 1} Λ]).obj (𝟙_ _) ≅
      (L((pullback.fst a b)^*[ModuleCat.{u + 1} Λ])).obj (dualizingComplex _ a) :=
    ((R(pullback.snd a b)^![ModuleCat.{u + 1} Λ]).mapIso
      (leftDerivedUpperStarUnitIso _ b)).symm ≪≫
      (asIso ((rightDerivedUpperShriekBaseChangeMap Λ (IsPullback.of_hasPullback a b)).app
        (𝟙_ _))).symm
  exact isIso_rightDerivedUpperShriekTensorMap_of_isClosedImmersion Λ (pullbackMapLeft a b i)
    (pullbackMapLeft a b U.ι) (range_pullbackMapLeft_eq_compl a b i U.ι hiU) _ _
    (exists_nonempty_iso_derivedTensor_rightDerivedLowerStar Λ b a U.ι hω eω hM)

/-- **Closed subschemes.** If the canonical maps of `AlgebraicGeometry.Etale.CoreProp` are
isomorphisms for `X`, then they are for every closed subscheme `i : Z ⟶ X`: by the coherent
composition law they are, for `Z`, the composites of those for `X` after `Ri'^!` with the base
change map of `i` at `ω_X` and the tensor map of `i'` at `(ω_π, Lπ^* M)`, isomorphisms by
supported localization. -/
theorem coreProp_comp_of_isClosedImmersion (hE : RightDerivedLowerShriekCompCoherence Λ)
    (hX : CoreProp Λ b a _ _ (IsPullback.of_hasPullback a b)) :
    CoreProp Λ b (i ≫ a) _ _ (IsPullback.of_hasPullback (i ≫ a) b) := by
  have wi : pullbackMapLeft a b i ≫ pullback.snd a b = pullback.snd (i ≫ a) b := by simp
  have hA := hX.1
  refine ⟨(isIso_rightDerivedUpperShriekBaseChangeMap_comp_iff_of_coherence
    (isPullback_pullbackMapLeft a b i) (IsPullback.of_hasPullback a b)
    (IsPullback.of_hasPullback (i ≫ a) b) rfl wi hE (𝟙_ _)
    (isIso_rightDerivedUpperShriekBaseChangeMap_pullbackMapLeft_dualizingComplex Λ b a i)).2
      inferInstance, fun M hM ↦ ?_⟩
  have := hX.2 M hM
  exact (isIso_dualizingComplexTensorMap_comp_iff hE (pullbackMapLeft a b i) (pullback.snd a b)
    (pullback.snd (i ≫ a) b) wi M
    (isIso_rightDerivedUpperShriekTensorMap_pullbackMapLeft Λ b a i hA hM)).2 inferInstance

end ClosedImmersion

/-- **Affine spaces.** The canonical maps of `AlgebraicGeometry.Etale.CoreProp` are isomorphisms
for the affine space `𝔸ⁿ_k`, which is smooth of relative dimension `n` over `k`: the base change
map by smooth base change for `R^!` (`prop-asd-smooth-base-change`), and `θ` for the smooth
projection `𝔸ⁿ_T ⟶ T` by cohomological smoothness (`sk-prop-cohsm`). -/
theorem coreProp_affineSpace (n : Type u) [Finite n] :
    CoreProp Λ b (𝔸(n; Spec (.of k)) ↘ Spec (.of k)) _ _
      (IsPullback.of_hasPullback (𝔸(n; Spec (.of k)) ↘ Spec (.of k)) b) := by
  have : HasInvertibleExponent Λ 𝔸(n; Spec (.of k)) :=
    .of_hom (𝔸(n; Spec (.of k)) ↘ Spec (.of k))
  have : HasInvertibleExponent Λ (pullback (𝔸(n; Spec (.of k)) ↘ Spec (.of k)) b) :=
    .of_hom (pullback.fst _ _ ≫ (𝔸(n; Spec (.of k)) ↘ Spec (.of k)))
  have : SmoothOfRelativeDimension (Nat.card n)
      (pullback.snd (𝔸(n; Spec (.of k)) ↘ Spec (.of k)) b) :=
    have := smoothOfRelativeDimension_isStableUnderBaseChange (n := Nat.card n)
    MorphismProperty.pullback_snd _ _ inferInstance
  refine ⟨?_, fun M _ ↦ isIso_dualizingComplexTensorMap_of_smoothOfRelativeDimension Λ _
    (d := Nat.card n) M⟩
  have := isIso_rightDerivedUpperShriekBaseChangeMap_of_smoothOfRelativeDimension Λ
    (𝔸(n; Spec (.of k)) ↘ Spec (.of k)) (Nat.card n) (IsPullback.of_hasPullback _ b)
  infer_instance

/-- **Affine schemes.** The canonical maps of `AlgebraicGeometry.Etale.CoreProp` are
isomorphisms for affine `X` of finite type over `k`, a closed subscheme of an affine space
(`AlgebraicGeometry.exists_isClosedImmersion_affineSpace_of_isAffine`). -/
theorem coreProp_of_isAffine (hE : RightDerivedLowerShriekCompCoherence Λ) {X : Scheme.{u}}
    [IsAffine X] (a : X ⟶ Spec (.of k)) [IsSeparated a] [LocallyOfFiniteType a]
    [QuasiCompact a] : CoreProp Λ b a _ _ (IsPullback.of_hasPullback a b) := by
  obtain ⟨n, _, ι, _, h⟩ := exists_isClosedImmersion_affineSpace_of_isAffine a
  subst h
  exact coreProp_comp_of_isClosedImmersion Λ b _ ι hE (coreProp_affineSpace Λ b n)

/-- **The induction on the number of affine opens.** If `X` is covered by at most `n` affine
opens, the canonical maps of `AlgebraicGeometry.Etale.CoreProp` are isomorphisms for `X`: for
an affine open `U` of the cover with closed complement `Z` (reduced), `Z` is covered by the
remaining `n - 1` affine opens, and the dévissage step
(`AlgebraicGeometry.Etale.coreProp_of_isClosedImmersion_of_isOpenImmersion`) applies. -/
theorem coreProp_of_card_le (hE : RightDerivedLowerShriekCompCoherence Λ) (n : ℕ) :
    ∀ {X : Scheme.{u}} (a : X ⟶ Spec (.of k)) [IsSeparated a] [LocallyOfFiniteType a]
      [QuasiCompact a] (t : Finset X.affineOpens), (∀ x : X, ∃ U ∈ t, x ∈ U.1) →
      t.card ≤ n → CoreProp Λ b a _ _ (IsPullback.of_hasPullback a b) := by
  classical
  induction n with
  | zero =>
    intro X a _ _ _ t ht hn
    have : IsEmpty X := ⟨fun x ↦ by
      obtain ⟨U, hU, -⟩ := ht x
      rw [Finset.card_eq_zero.1 (Nat.le_zero.1 hn)] at hU
      simp at hU⟩
    exact coreProp_of_isAffine Λ b hE a
  | succ n ih =>
    intro X a _ _ _ t ht hn
    by_cases hX : IsEmpty X
    · exact coreProp_of_isAffine Λ b hE a
    obtain ⟨x₀⟩ := not_isEmpty_iff.1 hX
    obtain ⟨U₀, hU₀, -⟩ := ht x₀
    have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace a
    have : IsNoetherian X := { __ := LocallyOfFiniteType.isLocallyNoetherian a }
    let j := U₀.1.ι
    have : TopologicalSpace.NoetherianSpace U₀.1 := j.isOpenEmbedding.isInducing.noetherianSpace
    have : QuasiCompact j := ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
    have : IsAffine U₀.1 := U₀.2
    let C : TopologicalSpace.Closeds X := ⟨(U₀.1 : Set X)ᶜ, U₀.1.isOpen.isClosed_compl⟩
    let i := (Scheme.IdealSheafData.vanishingIdeal C).subschemeι
    have hij : Set.range i.base = (Set.range j.base)ᶜ := by
      simp [i, j, C, Scheme.IdealSheafData.range_subschemeι,
        Scheme.IdealSheafData.coe_support_vanishingIdeal]
    let t' : Finset (Scheme.IdealSheafData.vanishingIdeal C).subscheme.affineOpens :=
      (t.erase U₀).image fun U ↦ ⟨i ⁻¹ᵁ U.1, U.2.preimage i⟩
    have ht' : ∀ z, ∃ U ∈ t', z ∈ (U.1 : Scheme.Opens _) := by
      intro z
      have hz : i.base z ∉ Set.range j.base := by
        rw [← Set.mem_compl_iff, ← hij]; exact ⟨z, rfl⟩
      obtain ⟨U, hU, hzU⟩ := ht (i.base z)
      refine ⟨⟨i ⁻¹ᵁ U.1, U.2.preimage i⟩, Finset.mem_image_of_mem _
        (Finset.mem_erase.2 ⟨?_, hU⟩), hzU⟩
      rintro rfl
      exact hz (by rw [Scheme.Opens.range_ι]; exact hzU)
    have hcard : t'.card ≤ n := by
      refine Finset.card_image_le.trans ?_
      rw [Finset.card_erase_of_mem hU₀]
      omega
    exact coreProp_of_isClosedImmersion_of_isOpenImmersion Λ b hE a i j hij
      (ih (i ≫ a) t' ht' hcard) (coreProp_of_isAffine Λ b hE (j ≫ a))

/-- The canonical maps of `AlgebraicGeometry.Etale.CoreProp` are isomorphisms for every `X`
separated of finite type over `k` (`prop-trf-exceptional-kunneth`, constant auxiliary
coefficient): `X` is covered by finitely many affine opens. -/
theorem coreProp (hE : RightDerivedLowerShriekCompCoherence Λ) {X : Scheme.{u}}
    (a : X ⟶ Spec (.of k)) [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a] :
    CoreProp Λ b a _ _ (IsPullback.of_hasPullback a b) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace a
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun U : X.affineOpens ↦ ((U : X.Opens) : Set X)) (fun U ↦ U.1.isOpen) (fun x _ ↦ by
      obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
      exact Set.mem_iUnion.2 ⟨⟨U, hU⟩, hxU⟩)
  refine coreProp_of_card_le Λ b hE t.card a t (fun x ↦ ?_) le_rfl
  obtain ⟨U, hU, hx⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
  exact ⟨U, hU, hx⟩

end Etale

end AlgebraicGeometry
