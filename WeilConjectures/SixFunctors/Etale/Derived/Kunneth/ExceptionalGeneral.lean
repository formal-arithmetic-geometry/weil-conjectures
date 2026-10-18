/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.ExceptionalCoreInduction

/-!

# The exceptional Künneth formula for general morphisms

For `f₁ : X₁ ⟶ Y₁`, `f₂ : X₂ ⟶ Y₂` admitting compactifications, with `Y₁`, `Y₂` separated of
finite type over a field `k`, and `N₁ ∈ Dctf(Y₁, Λ)`, `N₂ ∈ Dctf(Y₂, Λ)`,

`Rf₁^! N₁ ⊠ Rf₂^! N₂ ≅ R(f₁ × f₂)^! (N₁ ⊠ N₂)`

(`prop-trf-exceptional-kunneth`). As `f₁ × f₂ = (f₁ × 𝟙) ∘ (𝟙 × f₂)`, it suffices to treat
`f × 𝟙`. Factor `f : X ⟶ Y` as its graph `Γ : X ⟶ X ×_k Y`, a closed immersion since `Y` is
separated, followed by the projection `π : X ×_k Y ⟶ Y`. The closed immersion `Γ` is handled by
supported localization
(`AlgebraicGeometry.Etale.exceptionalKunneth_pullbackMapLeft_of_isClosedImmersion`), and the
projection `π`, a base change of the structure morphism `a : X ⟶ Spec k`, by the constant
coefficient case `Rπ^! K ≅ ω_X ⊠ K` (`AlgebraicGeometry.Etale.coreProp`), applied over `Y` and
over `Y ×_k W`.

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_of_isPullback`:
  `Rπ^! N ≅ Lq^* ω_X ⊗ᴸ Lπ^* N` for any base change `π` of `a`.
- `AlgebraicGeometry.Etale.exceptionalKunneth_pullbackMapLeft`: the case `f × 𝟙`.
- `AlgebraicGeometry.Etale.exceptionalKunneth_mapOverBase`: the general case.
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


variable {k : Type u} [Field k] [HasInvertibleExponent Λ (Spec (.of k))]

-- The coefficient category `ModuleCat Λ`.
set_option hygiene false in
local notation "𝓜" => ModuleCat.{u + 1} Λ

/-- The base change `f × 𝟙 : X ×_S W ⟶ Y ×_S W` of a compactifiable morphism admits a
compactification. -/
theorem hasCompactification_pullbackMapLeft {S X Y W : Scheme.{u}} (b : Y ⟶ S) (c : W ⟶ S)
    (f : X ⟶ Y) [HasCompactification f] : HasCompactification (pullbackMapLeft b c f) :=
  .of_isPullback (isPullback_pullbackMapLeft b c f)

/-- The base change `f × 𝟙 : X ×_S W ⟶ Y ×_S W` of a quasi-compact morphism is quasi-compact. -/
theorem quasiCompact_pullbackMapLeft {S X Y W : Scheme.{u}} (b : Y ⟶ S) (c : W ⟶ S)
    (f : X ⟶ Y) [QuasiCompact f] : QuasiCompact (pullbackMapLeft b c f) :=
  MorphismProperty.of_isPullback (P := @QuasiCompact) (isPullback_pullbackMapLeft b c f)
    inferInstance

attribute [local instance] hasCompactification_pullbackMapLeft quasiCompact_pullbackMapLeft

/-- `Rf^!` preserves `Dctf` (`thm-sf-ctf-stability` (v)), for a target of finite type over
`k`. -/
lemma constructibleFiniteTor_rightDerivedUpperShriek_of_comp {X Y : Scheme.{u}}
    (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY] (f : X ⟶ Y)
    [HasCompactification f] [QuasiCompact f]
    (N : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hN : constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y N) :
    constructibleFiniteTor (ModuleCat.{u + 1} Λ) X ((R(f)^![ModuleCat.{u + 1} Λ]).obj N) :=
  have : HasInvertibleExponent Λ Y := .of_hom aY
  constructibleFiniteTor_rightDerivedUpperShriek Λ aY f hN

/-- **The constant coefficient case** (`prop-trf-exceptional-kunneth`): for `X`, `T` separated
of finite type over `k` and any cartesian square `q : P ⟶ X`, `π : P ⟶ T` over `a : X ⟶ Spec k`
and `b : T ⟶ Spec k`, and `N ∈ Dctf(T, Λ)`,

`Rπ^! N ≅ Lq^* ω_X ⊗ᴸ Lπ^* N`.

It is `θ_{π, N}` composed with the base change isomorphism `Lq^* ω_X ≅ ω_π`
(`AlgebraicGeometry.Etale.coreProp`). -/
theorem nonempty_iso_rightDerivedUpperShriek_of_isPullback
    (hE : RightDerivedLowerShriekCompCoherence Λ) {X P T : Scheme.{u}}
    (a : X ⟶ Spec (.of k)) [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    (b : T ⟶ Spec (.of k)) [IsSeparated b] [LocallyOfFiniteType b] [QuasiCompact b]
    (q : P ⟶ X) (π : P ⟶ T) (sq : IsPullback q π a b) [HasCompactification π] [QuasiCompact π]
    {N : _root_.DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hN : constructibleFiniteTor (ModuleCat.{u + 1} Λ) T N) :
    Nonempty ((R(π)^![ModuleCat.{u + 1} Λ]).obj N ≅
      ((derivedTensor (ModuleCat.{u + 1} Λ) P).obj ((L((q)^*[ModuleCat.{u + 1} Λ])).obj
        (dualizingComplex (ModuleCat.{u + 1} Λ) a))).obj
          ((L((π)^*[ModuleCat.{u + 1} Λ])).obj N)) := by
  obtain ⟨hA, hθ⟩ := coreProp Λ b hE a
  have := hθ N hN
  let e := sq.isoPullback
  obtain ⟨c⟩ := nonempty_iso_rightDerivedUpperShriek_comp_of_eq Λ e.hom (pullback.snd a b) π
    sq.isoPullback_hom_snd
  let eω : dualizingComplex (ModuleCat.{u + 1} Λ) (pullback.snd a b) ≅
      (L((pullback.fst a b)^*[ModuleCat.{u + 1} Λ])).obj (dualizingComplex _ a) :=
    ((R(pullback.snd a b)^![ModuleCat.{u + 1} Λ]).mapIso
      (leftDerivedUpperStarUnitIso _ b)).symm ≪≫
      (asIso ((rightDerivedUpperShriekBaseChangeMap Λ (IsPullback.of_hasPullback a b)).app
        (𝟙_ _))).symm
  exact ⟨c.app N ≪≫ (rightDerivedUpperShriekIsoOfIso _ e).app _ ≪≫
    (L((e.hom)^*[ModuleCat.{u + 1} Λ])).mapIso
      ((asIso (dualizingComplexTensorMap Λ (pullback.snd a b) N)).symm ≪≫
        ((derivedTensor _ _).mapIso eω).app _) ≪≫
    leftDerivedUpperStarTensorIso _ e.hom _ _ ≪≫ derivedTensorMapIso Λ
      ((leftDerivedUpperStarComp _ e.hom (pullback.fst a b) q
        sq.isoPullback_hom_fst.symm).app _).symm
      ((leftDerivedUpperStarComp _ e.hom (pullback.snd a b) π
        sq.isoPullback_hom_snd.symm).app _).symm⟩

section Left

variable {X Y W : Scheme.{u}} (b : Y ⟶ Spec (.of k)) [IsSeparated b] [LocallyOfFiniteType b]
  [QuasiCompact b] (c : W ⟶ Spec (.of k)) [IsSeparated c] [LocallyOfFiniteType c]
  [QuasiCompact c]

/-- **Projections** (`prop-trf-exceptional-kunneth`): the projection `π : X ×_k Y ⟶ Y` has the
exceptional Künneth property over `(π, 𝟙_W)`: both sides are computed by the constant coefficient
case (`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_of_isPullback`), over `Y`
for `Rπ^! K` and over `Y ×_k W` for `R(π × 𝟙)^!(K ⊠ M)`. -/
theorem exceptionalKunneth_pullbackMapLeft_snd (hE : RightDerivedLowerShriekCompCoherence Λ)
    (a : X ⟶ Spec (.of k)) [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a] :
    ExceptionalKunneth Λ (pullback.fst (pullback.snd a b ≫ b) c)
      (pullback.snd (pullback.snd a b ≫ b) c) (pullback.fst b c) (pullback.snd b c)
      (pullback.snd a b) (𝟙 W) (pullbackMapLeft b c (pullback.snd a b)) := by
  intro K M hK hM
  have sqP : IsPullback (pullback.fst (pullback.snd a b ≫ b) c ≫ pullback.fst a b)
      (pullbackMapLeft b c (pullback.snd a b)) a (pullback.fst b c ≫ b) :=
    (isPullback_pullbackMapLeft b c (pullback.snd a b)).paste_horiz
      (IsPullback.of_hasPullback a b)
  have hKM : constructibleFiniteTor 𝓜 (pullback b c)
      (((derivedTensor 𝓜 (pullback b c)).obj ((L((pullback.fst b c)^*[𝓜])).obj K)).obj
        ((L((pullback.snd b c)^*[𝓜])).obj M)) :=
    constructibleFiniteTor_tensor Λ _ (constructibleFiniteTor_leftDerivedUpperStar _ _ hK)
      (constructibleFiniteTor_leftDerivedUpperStar _ _ hM)
  obtain ⟨c₁⟩ := nonempty_iso_rightDerivedUpperShriek_of_isPullback Λ hE a b (pullback.fst a b)
    (pullback.snd a b) (IsPullback.of_hasPullback a b) hK
  obtain ⟨c₂⟩ := nonempty_iso_rightDerivedUpperShriek_of_isPullback Λ hE a
    (pullback.fst b c ≫ b) _ (pullbackMapLeft b c (pullback.snd a b)) sqP hKM
  let A₁ := (L((pullback.fst (pullback.snd a b ≫ b) c)^*[𝓜])).obj
    ((L((pullback.fst a b)^*[𝓜])).obj (dualizingComplex 𝓜 a))
  let B₁ := (L((pullback.fst (pullback.snd a b ≫ b) c)^*[𝓜])).obj
    ((L((pullback.snd a b)^*[𝓜])).obj K)
  let C₁ := (L((pullback.snd (pullback.snd a b ≫ b) c)^*[𝓜])).obj M
  let s₁ : ((derivedTensor 𝓜 _).obj ((L((pullback.fst (pullback.snd a b ≫ b) c)^*[𝓜])).obj
      ((R(pullback.snd a b)^![𝓜]).obj K))).obj
        ((L((pullback.snd (pullback.snd a b ≫ b) c)^*[𝓜])).obj ((R(𝟙 W)^![𝓜]).obj M)) ≅
      ((derivedTensor 𝓜 _).obj (((derivedTensor 𝓜 _).obj A₁).obj B₁)).obj C₁ :=
    derivedTensorMapIso Λ ((L((pullback.fst (pullback.snd a b ≫ b) c)^*[𝓜])).mapIso c₁ ≪≫
      leftDerivedUpperStarTensorIso _ _ _ _)
      ((L((pullback.snd (pullback.snd a b ≫ b) c)^*[𝓜])).mapIso
        ((rightDerivedUpperShriekIdIsoOfFinite Λ W).app M))
  let s₂ := derivedTensorAssociator 𝓜 (pullback (pullback.snd a b ≫ b) c) A₁ B₁ C₁
  let s₃ : ((derivedTensor 𝓜 _).obj B₁).obj C₁ ≅
      (L((pullbackMapLeft b c (pullback.snd a b))^*[𝓜])).obj (((derivedTensor 𝓜 _).obj
        ((L((pullback.fst b c)^*[𝓜])).obj K)).obj ((L((pullback.snd b c)^*[𝓜])).obj M)) :=
    derivedTensorMapIso Λ (Iso.refl _) ((L((pullback.snd (pullback.snd a b ≫ b) c)^*[𝓜])).mapIso
        ((leftDerivedUpperStarId _ W).app M).symm) ≪≫
      (leftDerivedUpperStarDerivedTensorPullbackIso Λ (pullback.fst (pullback.snd a b ≫ b) c)
        (pullback.snd (pullback.snd a b ≫ b) c) (pullback.fst b c) (pullback.snd b c)
        (pullback.snd a b) (𝟙 W) (pullbackMapLeft b c (pullback.snd a b))
        (isPullback_pullbackMapLeft b c (pullback.snd a b)).w.symm (by simp) K M).symm
  let s₄ : A₁ ≅ (L((pullback.fst (pullback.snd a b ≫ b) c ≫ pullback.fst a b)^*[𝓜])).obj
      (dualizingComplex 𝓜 a) :=
    ((leftDerivedUpperStarComp _ (pullback.fst (pullback.snd a b ≫ b) c)
      (pullback.fst a b)).app _).symm
  exact ⟨s₁ ≪≫ s₂ ≪≫ derivedTensorMapIso Λ s₄ s₃ ≪≫ c₂.symm⟩

/-- **The exceptional Künneth formula for `f × 𝟙`** (`prop-trf-exceptional-kunneth`): for
`f : X ⟶ Y` admitting a compactification and `Y`, `W` separated of finite type over `k`, the
base change `f × 𝟙 : X ×_k W ⟶ Y ×_k W` has the exceptional Künneth property over `(f, 𝟙_W)`.
Factor `f` as its graph `Γ : X ⟶ X ×_k Y`, a closed immersion, followed by the projection
`π : X ×_k Y ⟶ Y`. -/
theorem exceptionalKunneth_pullbackMapLeft (hE : RightDerivedLowerShriekCompCoherence Λ)
    (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f] :
    ExceptionalKunneth Λ (pullback.fst (f ≫ b) c) (pullback.snd (f ≫ b) c) (pullback.fst b c)
      (pullback.snd b c) f (𝟙 W) (pullbackMapLeft b c f) := by
  have : HasInvertibleExponent Λ Y := .of_hom b
  have hΓ : pullback.lift (𝟙 _) f (Category.id_comp (f ≫ b)) ≫ pullback.snd (f ≫ b) b = f := by
    simp
  have h₁ := ExceptionalKunneth.of_isOpenImmersion (Λ := Λ) (pullback.fst (f ≫ b) c)
    (pullback.snd (f ≫ b) c)
    (pullback.fst (pullback.lift (𝟙 _) f (Category.id_comp (f ≫ b)) ≫
      pullback.snd (f ≫ b) b ≫ b) c)
    (pullback.snd (pullback.lift (𝟙 _) f (Category.id_comp (f ≫ b)) ≫
      pullback.snd (f ≫ b) b ≫ b) c) (𝟙 X) (𝟙 W)
    (pullback.congrHom (by rw [← Category.assoc, hΓ]) rfl).hom (by simp) (by simp)
  have h₂ := exceptionalKunneth_pullbackMapLeft_of_isClosedImmersion Λ
    (pullback.snd (f ≫ b) b ≫ b) c (pullback.lift (𝟙 _) f (Category.id_comp (f ≫ b)))
  have h₃ := exceptionalKunneth_pullbackMapLeft_snd Λ b c hE (f ≫ b)
  have h₁₂ := ExceptionalKunneth.comp h₁ h₂
    (constructibleFiniteTor_rightDerivedUpperShriek_of_comp Λ (pullback.snd (f ≫ b) b ≫ b)
      (pullback.lift (𝟙 _) f (Category.id_comp (f ≫ b))))
    (constructibleFiniteTor_rightDerivedUpperShriek_of_comp Λ c (𝟙 W))
    (pullback.lift (𝟙 _) f (Category.id_comp (f ≫ b))) (𝟙 W)
    ((pullback.congrHom (by rw [← Category.assoc, hΓ]) rfl).hom ≫
      pullbackMapLeft (pullback.snd (f ≫ b) b ≫ b) c
        (pullback.lift (𝟙 _) f (Category.id_comp (f ≫ b)))) (by simp) (by simp) rfl
  exact ExceptionalKunneth.comp h₁₂ h₃
    (constructibleFiniteTor_rightDerivedUpperShriek_of_comp Λ b (pullback.snd (f ≫ b) b))
    (constructibleFiniteTor_rightDerivedUpperShriek_of_comp Λ c (𝟙 W)) f (𝟙 W)
    (pullbackMapLeft b c f) hΓ (by simp) (by apply pullback.hom_ext <;> simp)

end Left

/-- The base change `𝟙 × f : X ×_S Y ⟶ X ×_S Z` of a compactifiable morphism admits a
compactification. -/
theorem hasCompactification_pullbackMapRight {S X Y Z : Scheme.{u}} (b : X ⟶ S) (c : Z ⟶ S)
    (f : Y ⟶ Z) [HasCompactification f] : HasCompactification (pullbackMapRight b c f) :=
  .of_isPullback (isPullback_pullbackMapRight b c f)

/-- The base change `𝟙 × f : X ×_S Y ⟶ X ×_S Z` of a quasi-compact morphism is quasi-compact. -/
theorem quasiCompact_pullbackMapRight {S X Y Z : Scheme.{u}} (b : X ⟶ S) (c : Z ⟶ S)
    (f : Y ⟶ Z) [QuasiCompact f] : QuasiCompact (pullbackMapRight b c f) :=
  MorphismProperty.of_isPullback (P := @QuasiCompact) (isPullback_pullbackMapRight b c f)
    inferInstance

attribute [local instance] hasCompactification_pullbackMapRight quasiCompact_pullbackMapRight

/-- **The exceptional Künneth formula for `𝟙 × f`** (`prop-trf-exceptional-kunneth`): the
mirror image of `AlgebraicGeometry.Etale.exceptionalKunneth_pullbackMapLeft`, by the symmetry
of the derived tensor product and of fibre products. -/
theorem exceptionalKunneth_pullbackMapRight (hE : RightDerivedLowerShriekCompCoherence Λ)
    {X₁ X₂ Y₂ : Scheme.{u}} (c : X₁ ⟶ Spec (.of k)) [IsSeparated c] [LocallyOfFiniteType c]
    [QuasiCompact c] (b₂ : Y₂ ⟶ Spec (.of k)) [IsSeparated b₂] [LocallyOfFiniteType b₂]
    [QuasiCompact b₂] (f₂ : X₂ ⟶ Y₂) [HasCompactification f₂] [QuasiCompact f₂] :
    ExceptionalKunneth Λ (pullback.fst c (f₂ ≫ b₂)) (pullback.snd c (f₂ ≫ b₂))
      (pullback.fst c b₂) (pullback.snd c b₂) (𝟙 X₁) f₂ (pullbackMapRight c b₂ f₂) := by
  have h₂ := (exceptionalKunneth_pullbackMapLeft Λ b₂ c hE f₂).symm
  have h₁ := ExceptionalKunneth.of_isOpenImmersion (Λ := Λ) (pullback.fst c (f₂ ≫ b₂))
    (pullback.snd c (f₂ ≫ b₂)) (pullback.snd (f₂ ≫ b₂) c) (pullback.fst (f₂ ≫ b₂) c)
    (𝟙 X₁) (𝟙 X₂) (pullbackSymmetry c (f₂ ≫ b₂)).hom (by simp) (by simp)
  have h₃ := ExceptionalKunneth.of_isOpenImmersion (Λ := Λ) (pullback.snd b₂ c)
    (pullback.fst b₂ c) (pullback.fst c b₂) (pullback.snd c b₂) (𝟙 X₁) (𝟙 Y₂)
    (pullbackSymmetry b₂ c).hom (by simp) (by simp)
  have : HasCompactification ((pullbackSymmetry c (f₂ ≫ b₂)).hom ≫ pullbackMapLeft b₂ c f₂) :=
    HasCompactification.comp_of_isOpenImmersion _ _
  have h₁₂ := ExceptionalKunneth.comp h₁ h₂
    (constructibleFiniteTor_rightDerivedUpperShriek_of_comp Λ c (𝟙 X₁))
    (constructibleFiniteTor_rightDerivedUpperShriek_of_comp Λ b₂ f₂) (𝟙 X₁) f₂
    ((pullbackSymmetry c (f₂ ≫ b₂)).hom ≫ pullbackMapLeft b₂ c f₂) (by simp) (by simp) rfl
  exact ExceptionalKunneth.comp h₁₂ h₃
    (constructibleFiniteTor_rightDerivedUpperShriek_of_comp Λ c (𝟙 X₁))
    (constructibleFiniteTor_rightDerivedUpperShriek_of_comp Λ b₂ (𝟙 Y₂)) (𝟙 X₁) f₂
    (pullbackMapRight c b₂ f₂) (by simp) (by simp) (by apply pullback.hom_ext <;> simp)

/-- **The exceptional Künneth formula** (`prop-trf-exceptional-kunneth`): for `f₁ : X₁ ⟶ Y₁`,
`f₂ : X₂ ⟶ Y₂` admitting compactifications and `Y₁`, `Y₂` separated of finite type over `k`,
`f₁ × f₂ : X₁ ×_k X₂ ⟶ Y₁ ×_k Y₂` has the exceptional Künneth property: for
`N₁ ∈ Dctf(Y₁, Λ)`, `N₂ ∈ Dctf(Y₂, Λ)`, `Rf₁^! N₁ ⊠ Rf₂^! N₂ ≅ R(f₁ × f₂)^! (N₁ ⊠ N₂)`. It is
the composite of the cases `𝟙 × f₂` and `f₁ × 𝟙`. -/
theorem exceptionalKunneth_mapOverBase (hE : RightDerivedLowerShriekCompCoherence Λ)
    {X₁ X₂ Y₁ Y₂ : Scheme.{u}} (b₁ : Y₁ ⟶ Spec (.of k)) (b₂ : Y₂ ⟶ Spec (.of k))
    [IsSeparated b₁] [LocallyOfFiniteType b₁] [QuasiCompact b₁]
    [IsSeparated b₂] [LocallyOfFiniteType b₂] [QuasiCompact b₂]
    (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) [HasCompactification f₁] [HasCompactification f₂]
    [QuasiCompact f₁] [QuasiCompact f₂]
    [HasCompactification (pullback.mapOverBase f₁ f₂ b₁ b₂)] :
    ExceptionalKunneth Λ (pullback.fst (f₁ ≫ b₁) (f₂ ≫ b₂)) (pullback.snd (f₁ ≫ b₁) (f₂ ≫ b₂))
      (pullback.fst b₁ b₂) (pullback.snd b₁ b₂) f₁ f₂ (pullback.mapOverBase f₁ f₂ b₁ b₂) := by
  have : QuasiCompact (pullback.mapOverBase f₁ f₂ b₁ b₂) := by
    have h : pullbackMapRight (f₁ ≫ b₁) b₂ f₂ ≫ pullbackMapLeft b₁ b₂ f₁ =
        pullback.mapOverBase f₁ f₂ b₁ b₂ := by
      apply pullback.hom_ext <;> simp
    rw [← h]; infer_instance
  exact ExceptionalKunneth.comp
    (exceptionalKunneth_pullbackMapRight Λ hE (f₁ ≫ b₁) b₂ f₂)
    (exceptionalKunneth_pullbackMapLeft Λ b₁ b₂ hE f₁)
    (constructibleFiniteTor_rightDerivedUpperShriek_of_comp Λ b₁ f₁)
    (constructibleFiniteTor_rightDerivedUpperShriek_of_comp Λ b₂ (𝟙 Y₂)) f₁ f₂
    (pullback.mapOverBase f₁ f₂ b₁ b₂) (by simp) (by simp)
    (by apply pullback.hom_ext <;> simp)

end Etale

end AlgebraicGeometry
