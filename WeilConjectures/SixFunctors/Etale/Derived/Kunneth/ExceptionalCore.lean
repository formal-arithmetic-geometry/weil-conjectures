/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.CanonicalMapsComp
public import WeilConjectures.EtaleCohomology.Purity.Smooth.CohomologicalSmoothness

/-!

# The exceptional Künneth formula for constant coefficients: the dévissage on the source

Let `k` be a field, `Λ` a finite ring whose exponent is invertible in `k`, `X` and `T` separated
of finite type over `k`, with structure morphisms `a`, `b`, and let `π : X ×_k T ⟶ T` and
`q : X ×_k T ⟶ X` be the projections. This file proves that

* the base change map `Lq^* ω_X ⟶ ω_π` of the dualizing complexes is an isomorphism, and
* the canonical map `θ_{π, M} : ω_π ⊗ᴸ Lπ^* M ⟶ Rπ^! M` is an isomorphism for every
  `M ∈ Dctf(T, Λ)`,

so that `Rπ^! M ≅ ω_X ⊠ M`: this is the exceptional Künneth map `α` of
`prop-trf-exceptional-kunneth` for `a × 𝟙_T` and the coefficients `(Λ, M)`, the case of a constant
auxiliary coefficient in the blueprint proof.

The proof is the blueprint's: smooth morphisms are handled by smooth purity (here in the form
of cohomological smoothness, `sk-prop-cohsm`), closed immersions by supported localization and
the ordinary Künneth formula
(`AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekTensorMap_of_isClosedImmersion`,
`AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekBaseChangeMap_app_of_isClosedImmersion`), and
an affine `X` embeds as a closed subscheme of an affine space. A general `X` is reduced to affine
ones through the open–closed decomposition `X = U ⊔ Z` with `U` affine
(`AlgebraicGeometry.Etale.isIso_of_isIso_rightDerivedUpperShriek_map_of_isIso_map`), by
induction on the number of affine opens covering `X`. The compatibility of the canonical maps
with composition is the coherent composition law for `Rf_!`
(`AlgebraicGeometry.Etale.RightDerivedLowerShriekCompCoherence`).

## Main statements

- `AlgebraicGeometry.Etale.CoreProp`: the two statements above for `X`.
- `AlgebraicGeometry.Etale.coreProp_of_isClosedImmersion_of_isOpenImmersion`: the dévissage step.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

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

section Range

variable {S Y₁ Y₂ Z : Scheme.{u}} (b₁ : Y₁ ⟶ S) (b₂ : Y₂ ⟶ S)

/-- A point of `Y₁ ×_S Y₂` lies in the range of the base change `i × 𝟙` of `i : Z ⟶ Y₁` if and
only if its first projection lies in the range of `i`. -/
lemma mem_range_pullbackMapLeft_iff (i : Z ⟶ Y₁) (x : ↥(pullback b₁ b₂)) :
    x ∈ Set.range (pullbackMapLeft b₁ b₂ i).base ↔
      (pullback.fst b₁ b₂).base x ∈ Set.range i.base := by
  have hpb := isPullback_pullbackMapLeft b₁ b₂ i
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨(pullback.fst (i ≫ b₁) b₂).base y, by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hpb.w]⟩
  · intro hx
    obtain ⟨y, hy⟩ : x ∈ Set.range (pullback.snd i (pullback.fst b₁ b₂)).base := by
      rw [Scheme.Pullback.range_snd]; exact hx
    refine ⟨hpb.isoPullback.inv.base y, ?_⟩
    rw [← Scheme.Hom.comp_apply, hpb.isoPullback_inv_snd, hy]

/-- The base changes of complementary immersions have complementary ranges. -/
lemma range_pullbackMapLeft_eq_compl {U : Scheme.{u}} (i : Z ⟶ Y₁) (j : U ⟶ Y₁)
    (hij : Set.range i.base = (Set.range j.base)ᶜ) :
    Set.range (pullbackMapLeft b₁ b₂ i).base =
      (Set.range (pullbackMapLeft b₁ b₂ j).base)ᶜ := by
  ext x
  rw [Set.mem_compl_iff, mem_range_pullbackMapLeft_iff, mem_range_pullbackMapLeft_iff, hij]
  rfl

end Range

variable {k : Type u} [Field k] [HasInvertibleExponent Λ (Spec (.of k))]
  {T : Scheme.{u}} (b : T ⟶ Spec (.of k)) [IsSeparated b] [LocallyOfFiniteType b]
  [QuasiCompact b]

section Kunneth

variable {X U : Scheme.{u}} (a : X ⟶ Spec (.of k)) [IsSeparated a] [LocallyOfFiniteType a]
  [QuasiCompact a] (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]

/-- The ordinary Künneth formula with an identity factor (`sk-lem-sf-kunneth-star`) for the
constant coefficient `Λ_T`: base change of `Rj_* D` along the projection `X ×_k T ⟶ X`. -/
lemma nonempty_iso_leftDerivedUpperStar_fst_rightDerivedLowerStar
    {D : _root_.DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hD : constructibleFiniteTor (ModuleCat.{u + 1} Λ) U D) :
    Nonempty ((L((pullback.fst a b)^*[ModuleCat.{u + 1} Λ])).obj
        ((R((j)_*[ModuleCat.{u + 1} Λ])).obj D) ≅
      (R((pullbackMapLeft a b j)_*[ModuleCat.{u + 1} Λ])).obj
        ((L((pullback.fst (j ≫ a) b)^*[ModuleCat.{u + 1} Λ])).obj D)) := by
  obtain ⟨e⟩ := nonempty_iso_externalProduct_rightDerivedLowerStar Λ a b j hD
    (constructibleFiniteTor_tensorUnit Λ T)
  let r (P : Scheme.{u}) (p : P ⟶ T) (K : _root_.DerivedCategory
      (Sheaf P.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
      ((derivedTensor (ModuleCat.{u + 1} Λ) P).obj K).obj
        ((L((p)^*[ModuleCat.{u + 1} Λ])).obj (𝟙_ _)) ≅ K :=
    ((derivedTensor _ _).obj _).mapIso (leftDerivedUpperStarUnitIso _ _) ≪≫ ρ_ _
  exact ⟨(r _ _ _).symm ≪≫ e ≪≫ (R((pullbackMapLeft a b j)_*[ModuleCat.{u + 1} Λ])).mapIso
    (r _ _ _)⟩

/-- The ordinary Künneth formula with an identity factor (`sk-lem-sf-kunneth-star`), in the form
needed for the tensor map of a closed immersion: if `C ≅ Lq^* D₀` is pulled back from `X`, then
`Rj'_* Lj'^* C ⊗ᴸ Lπ^* M` is of the form `Rj'_* E` for the base change `j'` of `j`. -/
lemma exists_nonempty_iso_derivedTensor_rightDerivedLowerStar
    {C : _root_.DerivedCategory (Sheaf (pullback a b).smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {D₀ : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hD₀ : constructibleFiniteTor (ModuleCat.{u + 1} Λ) X D₀)
    (eC : C ≅ (L((pullback.fst a b)^*[ModuleCat.{u + 1} Λ])).obj D₀)
    {M : _root_.DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hM : constructibleFiniteTor (ModuleCat.{u + 1} Λ) T M) :
    ∃ E, Nonempty (((derivedTensor (ModuleCat.{u + 1} Λ) (pullback a b)).obj
        ((R((pullbackMapLeft a b j)_*[ModuleCat.{u + 1} Λ])).obj
          ((L((pullbackMapLeft a b j)^*[ModuleCat.{u + 1} Λ])).obj C))).obj
            ((L((pullback.snd a b)^*[ModuleCat.{u + 1} Λ])).obj M) ≅
      (R((pullbackMapLeft a b j)_*[ModuleCat.{u + 1} Λ])).obj E) := by
  have hD : constructibleFiniteTor (ModuleCat.{u + 1} Λ) U
      ((L((j)^*[ModuleCat.{u + 1} Λ])).obj D₀) :=
    constructibleFiniteTor_leftDerivedUpperStar _ j hD₀
  obtain ⟨e₁⟩ := nonempty_iso_leftDerivedUpperStar_fst_rightDerivedLowerStar Λ b a j hD
  obtain ⟨e₂⟩ := nonempty_iso_externalProduct_rightDerivedLowerStar Λ a b j hD hM
  let c : (L((pullbackMapLeft a b j)^*[ModuleCat.{u + 1} Λ])).obj C ≅
      (L((pullback.fst (j ≫ a) b)^*[ModuleCat.{u + 1} Λ])).obj
        ((L((j)^*[ModuleCat.{u + 1} Λ])).obj D₀) :=
    (L((pullbackMapLeft a b j)^*[ModuleCat.{u + 1} Λ])).mapIso eC ≪≫
      ((leftDerivedUpperStarComp _ (pullbackMapLeft a b j) (pullback.fst a b)
        (pullback.fst (j ≫ a) b ≫ j) (isPullback_pullbackMapLeft a b j).w).app D₀).symm ≪≫
      (leftDerivedUpperStarComp _ (pullback.fst (j ≫ a) b) j).app D₀
  exact ⟨_, ⟨((derivedTensor _ _).mapIso
    ((R((pullbackMapLeft a b j)_*[ModuleCat.{u + 1} Λ])).mapIso c ≪≫ e₁.symm)).app _ ≪≫ e₂⟩⟩

end Kunneth

/-- The two canonical maps of the exceptional Künneth formula for constant coefficients, for
`X` separated of finite type over `k` with structure morphism `a` and the projections
`q : X ×_k T ⟶ X`, `π : X ×_k T ⟶ T`:

* the base change map `Lq^* Ra^! Λ ⟶ Rπ^! Lb^* Λ` is an isomorphism;
* `θ_{π, M} : ω_π ⊗ᴸ Lπ^* M ⟶ Rπ^! M` is an isomorphism for all `M ∈ Dctf(T, Λ)`.

Together they give `Rπ^! M ≅ ω_X ⊠ M` (`prop-trf-exceptional-kunneth`, constant auxiliary
coefficient). -/
def CoreProp {X P : Scheme.{u}} (a : X ⟶ Spec (.of k)) (q : P ⟶ X) (π : P ⟶ T)
    (sq : IsPullback q π a b) [HasCompactification a] [HasCompactification π]
    [QuasiCompact π] : Prop :=
  IsIso ((rightDerivedUpperShriekBaseChangeMap Λ sq).app (𝟙_ _)) ∧
    ∀ M : _root_.DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      constructibleFiniteTor (ModuleCat.{u + 1} Λ) T M →
        IsIso (dualizingComplexTensorMap Λ π M)

/-- **The dévissage step.** Let `i : Z ⟶ X` be a closed immersion with open complement
`j : U ⟶ X`. If the canonical maps of `CoreProp` are isomorphisms for `Z` and for `U`, then they
are for `X`: after `Ri'^!` and `Lj'^*`, for the base changes `i'`, `j'` of `i`, `j`, they become
the canonical maps for `Z` and `U` (by the coherent composition law, the base change map of `i`
and the tensor map of `i'` being isomorphisms by supported localization and the ordinary
Künneth formula), and a map is an isomorphism if it is so after `Ri'^!` and `Lj'^*`. -/
theorem coreProp_of_isClosedImmersion_of_isOpenImmersion
    (hE : RightDerivedLowerShriekCompCoherence Λ) {X Z U : Scheme.{u}}
    (a : X ⟶ Spec (.of k)) [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (hZ : CoreProp Λ b (i ≫ a) _ _ (IsPullback.of_hasPullback (i ≫ a) b))
    (hU : CoreProp Λ b (j ≫ a) _ _ (IsPullback.of_hasPullback (j ≫ a) b)) :
    CoreProp Λ b a _ _ (IsPullback.of_hasPullback a b) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace a
  have : HasInvertibleExponent Λ X := .of_hom a
  have : HasCompactification j := (Compactification.ofIsOpenImmersion j).hasCompactification
  have : HasCompactification (pullbackMapLeft a b j) :=
    (Compactification.ofIsOpenImmersion _).hasCompactification
  have : HasInvertibleExponent Λ U := .of_hom (j ≫ a)
  have hω : constructibleFiniteTor (ModuleCat.{u + 1} Λ) X (dualizingComplex _ a) :=
    constructibleFiniteTor_dualizingComplex Λ (𝟙 _) a (constructibleFiniteTor_tensorUnit Λ _)
  have hij' := range_pullbackMapLeft_eq_compl a b i j hij
  have hdisj : Disjoint (Set.range (pullbackMapLeft a b i).base)
      (Set.range (pullbackMapLeft a b j).base) := by
    rw [hij']; exact disjoint_compl_left
  have : QuasiCompact (pullbackMapLeft a b j) :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) (isPullback_pullbackMapLeft a b j)
      inferInstance
  have sqi := isPullback_pullbackMapLeft a b i
  have sqj := isPullback_pullbackMapLeft a b j
  have sqX := IsPullback.of_hasPullback a b
  have wi : pullbackMapLeft a b i ≫ pullback.snd a b = pullback.snd (i ≫ a) b := by simp
  have wj : pullbackMapLeft a b j ≫ pullback.snd a b = pullback.snd (j ≫ a) b := by simp
  -- the base change maps of `i` and `j` at `ω_X`
  have hβi : IsIso ((rightDerivedUpperShriekBaseChangeMap Λ sqi).app
      ((R(a)^![ModuleCat.{u + 1} Λ]).obj (𝟙_ _))) :=
    isIso_rightDerivedUpperShriekBaseChangeMap_app_of_isClosedImmersion Λ sqi j hij
      (pullbackMapLeft a b j) hdisj _
      ⟨_, nonempty_iso_leftDerivedUpperStar_fst_rightDerivedLowerStar Λ b a j
        (constructibleFiniteTor_leftDerivedUpperStar _ j hω)⟩
  have hβj : IsIso ((rightDerivedUpperShriekBaseChangeMap Λ sqj).app
      ((R(a)^![ModuleCat.{u + 1} Λ]).obj (𝟙_ _))) := by
    have := isIso_rightDerivedUpperShriekBaseChangeMap_of_smoothOfRelativeDimension Λ j 0 sqj
    infer_instance
  -- the base change map for `X`
  have hA : IsIso ((rightDerivedUpperShriekBaseChangeMap Λ sqX).app (𝟙_ _)) := by
    refine isIso_of_isIso_rightDerivedUpperShriek_map_of_isIso_map Λ (pullbackMapLeft a b i)
      (pullbackMapLeft a b j) hij' _
      ((isIso_rightDerivedUpperShriekBaseChangeMap_comp_iff_of_coherence sqi sqX
        (IsPullback.of_hasPullback (i ≫ a) b) rfl wi hE (𝟙_ _) hβi).1 hZ.1) ?_
    exact (NatIso.isIso_map_iff (rightDerivedUpperShriekIsoLeftDerivedUpperStar Λ
      (pullbackMapLeft a b j)) _).1
      ((isIso_rightDerivedUpperShriekBaseChangeMap_comp_iff_of_coherence sqj sqX
        (IsPullback.of_hasPullback (j ≫ a) b) rfl wj hE (𝟙_ _) hβj).1 hU.1)
  refine ⟨hA, fun M hM ↦ ?_⟩
  -- `ω_π` is pulled back from `X`
  let eω : (R(pullback.snd a b)^![ModuleCat.{u + 1} Λ]).obj (𝟙_ _) ≅
      (L((pullback.fst a b)^*[ModuleCat.{u + 1} Λ])).obj (dualizingComplex _ a) :=
    ((R(pullback.snd a b)^![ModuleCat.{u + 1} Λ]).mapIso
      (leftDerivedUpperStarUnitIso _ b)).symm ≪≫
      (asIso ((rightDerivedUpperShriekBaseChangeMap Λ sqX).app (𝟙_ _))).symm
  have hτi : IsIso (rightDerivedUpperShriekTensorMap (pullbackMapLeft a b i)
      ((R(pullback.snd a b)^![ModuleCat.{u + 1} Λ]).obj (𝟙_ _))
      ((L((pullback.snd a b)^*[ModuleCat.{u + 1} Λ])).obj M)) :=
    isIso_rightDerivedUpperShriekTensorMap_of_isClosedImmersion Λ (pullbackMapLeft a b i)
      (pullbackMapLeft a b j) hij' _ _
      (exists_nonempty_iso_derivedTensor_rightDerivedLowerStar Λ b a j hω eω hM)
  have hτj : IsIso (rightDerivedUpperShriekTensorMap (pullbackMapLeft a b j)
      ((R(pullback.snd a b)^![ModuleCat.{u + 1} Λ]).obj (𝟙_ _))
      ((L((pullback.snd a b)^*[ModuleCat.{u + 1} Λ])).obj M)) :=
    isIso_rightDerivedUpperShriekTensorMap_of_isOpenImmersion Λ (pullbackMapLeft a b j)
      (pullbackMapLeft a b i) hij' _ _
  refine isIso_of_isIso_rightDerivedUpperShriek_map_of_isIso_map Λ (pullbackMapLeft a b i)
    (pullbackMapLeft a b j) hij' _
    ((isIso_dualizingComplexTensorMap_comp_iff hE (pullbackMapLeft a b i) (pullback.snd a b)
      (pullback.snd (i ≫ a) b) wi M hτi).1 (hZ.2 M hM)) ?_
  exact (NatIso.isIso_map_iff (rightDerivedUpperShriekIsoLeftDerivedUpperStar Λ
    (pullbackMapLeft a b j)) _).1
    ((isIso_dualizingComplexTensorMap_comp_iff hE (pullbackMapLeft a b j) (pullback.snd a b)
      (pullback.snd (j ≫ a) b) wj M hτj).1 (hU.2 M hM))

end Etale

end AlgebraicGeometry
