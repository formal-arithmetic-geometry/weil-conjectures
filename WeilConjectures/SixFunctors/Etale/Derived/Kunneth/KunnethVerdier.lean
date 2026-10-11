/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.DualReduction
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.ExternalHomMap
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek
public import WeilConjectures.SixFunctors.Etale.Derived.PointDualizing
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek

/-!

# The Künneth–Verdier isomorphism

Over a field `k`, for a finite coefficient ring `Λ` whose exponent is invertible in `k`, and
for separated finite-type `k`-schemes `X`, `Y` with projections `p_X`, `p_Y` of `X ×_k Y`, the
Künneth–Verdier isomorphism (`thm-trf-kunneth-verdier`) reads

`κ : M ⊠ 𝔻_Y N ≅ RHom(p_Y^* N, Rp_X^! M)`

for `M ∈ Dctf(X, Λ)`, `N ∈ Dctf(Y, Λ)`. As in the blueprint it is the external Hom isomorphism
`β` (`prop-trf-external-hom`) for the pairs `(Λ_X, M)` and `(N, ω_Y)`, followed by the
exceptional Künneth isomorphism `α` (`prop-trf-exceptional-kunneth`) for `𝟙_X × a_Y`, which
reads `M ⊠ ω_Y ≅ Rp_X^! M`.

## Main definitions

- `AlgebraicGeometry.Etale.verdierDualEvaluation` (`def-trf-dualizing-complex`): the
  evaluation `M ⊗ᴸ 𝔻_X M ⟶ ω_X`.

## Main statements

- `AlgebraicGeometry.Etale.isIso_externalHomMap`, `AlgebraicGeometry.Etale.nonempty_iso_externalHom`
  (`prop-trf-external-hom`): `β`.
- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_pullbackFst`: `α` for
  `𝟙_X × a_Y`, `Rp_X^! M ≅ M ⊠ ω_Y`.
- `AlgebraicGeometry.Etale.nonempty_iso_kunnethVerdier` (`thm-trf-kunneth-verdier`): `κ`.
- `AlgebraicGeometry.Etale.kunnethVerdier`, `AlgebraicGeometry.Etale.verdierDualExternalProduct`
  (`rem-sf-kv-formal`): `κ` and its formal equivalent `𝔻(P ⊠ Q) ≅ 𝔻P ⊠ 𝔻Q`.

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

/-- Blueprint `def-trf-dualizing-complex`: Dualizing complex and Verdier dual, the evaluation.

For `a : X ⟶ S` with dualizing complex `ω_X = Ra^! Λ_S`
(`AlgebraicGeometry.Etale.dualizingComplex`) and Verdier dual `𝔻_X = RHom(-, ω_X)`
(`AlgebraicGeometry.Etale.verdierDual`), the evaluation `M ⊗ᴸ 𝔻_X M ⟶ ω_X` is the transpose of
the identity of `𝔻_X M` under the tensor–internal-Hom adjunction
`Hom(M ⊗ᴸ 𝔻_X M, ω_X) ≅ Hom(𝔻_X M, RHom(M, ω_X))`. (The blueprint writes the two factors in the
other order, `𝔻_X M ⊗ᴸ M`; the adjunction of the library tensors on the left.) -/
noncomputable def verdierDualEvaluation {X S : Scheme.{u}} (a : X ⟶ S) [HasCompactification a]
    (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    ((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj M).obj ((verdierDual _ a).obj (op M)) ⟶
      dualizingComplex _ a :=
  (derivedTensorHomAdjunction _ M).counit.app (dualizingComplex _ a)

/-- The unit `Λ_X` lies in `Dctf(X, Λ)`: it is the constant sheaf `Λ` placed in degree `0`,
which is constructible and flat. -/
theorem constructibleFiniteTor_unit (X : Scheme.{u}) :
    constructibleFiniteTor (ModuleCat.{u + 1} Λ) X (𝟙_ _) :=
  ⟨(boundedConstructible _ X).prop_of_iso (_root_.DerivedCategory.singleFunctorObjUnitIso _)
      (boundedConstructible_singleFunctor_obj _ 0), 0, 0,
    (torAmplitudeIn _ X 0 0).prop_of_iso (_root_.DerivedCategory.singleFunctorObjUnitIso _)
      (_root_.DerivedCategory.torAmplitudeIn_singleFunctor_obj_of_flat
        (ObjectProperty.flat_of_isDualizable isDualizable_unit))⟩

/-- The internal hom out of the unit is the identity, `RHom(Λ_X, -) ≅ 𝟭`: both are right
adjoint to `Λ_X ⊗ᴸ - ≅ 𝟭`. -/
noncomputable def derivedHomUnitIso (X : Scheme.{u}) :
    (RHom(X)[ModuleCat.{u + 1} Λ]).obj (op (𝟙_ _)) ≅ 𝟭 _ :=
  (derivedTensorHomAdjunction _ (𝟙_ _)).rightAdjointUniq
    (Adjunction.id.ofNatIsoLeft (derivedTensorLeftUnitorNatIso _ X).symm)

/-- The external product with the unit in the first factor is the pullback of the second factor:
`Λ_X ⊠ N ≅ p_Y^* N`. -/
noncomputable def externalProductUnitLeftIso {B X Y : Scheme.{u}} (f : X ⟶ B) (g : Y ⟶ B)
    (N : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    externalProduct (ModuleCat.{u + 1} Λ) f g (𝟙_ _) N ≅
      (L((pullback.snd f g)^*[ModuleCat.{u + 1} Λ])).obj N :=
  ((derivedTensor _ _).mapIso (leftDerivedUpperStarUnitIso _ (pullback.fst f g))).app _ ≪≫
    derivedTensorLeftUnitor _ _ _

/-- The external product with the unit in the second factor is the pullback of the first factor:
`K ⊠ Λ_Y ≅ p_X^* K`. -/
noncomputable def externalProductUnitRightIso {B X Y : Scheme.{u}} (f : X ⟶ B) (g : Y ⟶ B)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    externalProduct (ModuleCat.{u + 1} Λ) f g K (𝟙_ _) ≅
      (L((pullback.fst f g)^*[ModuleCat.{u + 1} Λ])).obj K :=
  ((derivedTensor _ _).obj _).mapIso (leftDerivedUpperStarUnitIso _ (pullback.snd f g)) ≪≫
    derivedTensorRightUnitor _ _ _

/-- For an isomorphism of schemes `e`, the exceptional inverse image is the derived pullback,
`Re^! ≅ Le^*`: an isomorphism is a quasi-compact open immersion, for which
`Re^! ≅ D(e^*)` (`AlgebraicGeometry.Etale.rightDerivedUpperShriekIsoOfIsOpenImmersion`). -/
noncomputable def rightDerivedUpperShriekIsoOfIsIso {X Y : Scheme.{u}} (e : X ⟶ Y) [IsIso e]
    [HasCompactification e] :
    R(e)^![ModuleCat.{u + 1} Λ] ≅ L((e)^*[ModuleCat.{u + 1} Λ]) :=
  rightDerivedUpperShriekIsoOfIsOpenImmersion Λ e ≪≫
    (leftDerivedUpperStarIsoMapDerivedCategory _ e).symm

variable {k : Type u} [Field k]

/-- TEMPORARY: to be replaced by kv-alpha's result.

Blueprint `prop-trf-exceptional-kunneth`: the exceptional Künneth map `α` is an isomorphism. The
statement is exactly the `exceptional` field of `AlgebraicGeometry.Etale.HasKunnethComparisons`
over `S = Spec k`, for a finite coefficient ring whose exponent is invertible in `k`. -/
theorem nonempty_iso_exceptional_temp [HasInvertibleExponent Λ (Spec (.of k))]
    {X₁ X₂ Y₁ Y₂ : Scheme.{u}} (b₁ : Y₁ ⟶ Spec (.of k)) (b₂ : Y₂ ⟶ Spec (.of k))
    [LocallyOfFiniteType b₁] [QuasiCompact b₁] [LocallyOfFiniteType b₂] [QuasiCompact b₂]
    (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) [HasCompactification f₁] [HasCompactification f₂]
    [QuasiCompact f₁] [QuasiCompact f₂]
    [HasCompactification (pullback.mapOverBase f₁ f₂ b₁ b₂)]
    [(R(f₁)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint] [(R(f₂)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint]
    [(R(pullback.mapOverBase f₁ f₂ b₁ b₂)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint]
    {N₁ : _root_.DerivedCategory (Sheaf Y₁.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {N₂ : _root_.DerivedCategory (Sheaf Y₂.smallEtaleTopology (ModuleCat.{u + 1} Λ))} :
    constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y₁ N₁ →
    constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y₂ N₂ →
    Nonempty (externalProduct (ModuleCat.{u + 1} Λ) (f₁ ≫ b₁) (f₂ ≫ b₂)
        ((R(f₁)^![ModuleCat.{u + 1} Λ]).obj N₁) ((R(f₂)^![ModuleCat.{u + 1} Λ]).obj N₂) ≅
      (R(pullback.mapOverBase f₁ f₂ b₁ b₂)^![ModuleCat.{u + 1} Λ]).obj
        (externalProduct (ModuleCat.{u + 1} Λ) b₁ b₂ N₁ N₂)) :=
  sorry

/-- Blueprint `prop-trf-external-hom`: External Hom; the `β` map.

Over a field `k`, for a finite coefficient ring `Λ` of invertible exponent, separated
finite-type `k`-schemes `Z₁`, `Z₂` and `Eᵢ, Nᵢ ∈ Dctf(Zᵢ, Λ)`, the external Hom map of
`def-sf-kv-maps` (iii) (`AlgebraicGeometry.Etale.externalHomMap`)

`β : RHom(E₁, N₁) ⊠ RHom(E₂, N₂) ⟶ RHom(E₁ ⊠ E₂, N₁ ⊠ N₂)`

is an isomorphism. -/
theorem isIso_externalHomMap [HasInvertibleExponent Λ (Spec (.of k))] {Z₁ Z₂ : Scheme.{u}}
    (c₁ : Z₁ ⟶ Spec (.of k)) (c₂ : Z₂ ⟶ Spec (.of k))
    [IsSeparated c₁] [LocallyOfFiniteType c₁] [QuasiCompact c₁]
    [IsSeparated c₂] [LocallyOfFiniteType c₂] [QuasiCompact c₂]
    {E₁ N₁ : _root_.DerivedCategory (Sheaf Z₁.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {E₂ N₂ : _root_.DerivedCategory (Sheaf Z₂.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hE₁ : constructibleFiniteTor (ModuleCat.{u + 1} Λ) Z₁ E₁)
    (hE₂ : constructibleFiniteTor (ModuleCat.{u + 1} Λ) Z₂ E₂)
    (hN₁ : constructibleFiniteTor (ModuleCat.{u + 1} Λ) Z₁ N₁)
    (hN₂ : constructibleFiniteTor (ModuleCat.{u + 1} Λ) Z₂ N₂) :
    IsIso (externalHomMap (ModuleCat.{u + 1} Λ) c₁ c₂ E₁ N₁ E₂ N₂) :=
  sorry

/-- Blueprint `prop-trf-external-hom`: External Hom; the `β` map, as an isomorphism
`RHom(E₁, N₁) ⊠ RHom(E₂, N₂) ≅ RHom(E₁ ⊠ E₂, N₁ ⊠ N₂)`
(`AlgebraicGeometry.Etale.isIso_externalHomMap`). -/
theorem nonempty_iso_externalHom [HasInvertibleExponent Λ (Spec (.of k))] {Z₁ Z₂ : Scheme.{u}}
    (c₁ : Z₁ ⟶ Spec (.of k)) (c₂ : Z₂ ⟶ Spec (.of k))
    [IsSeparated c₁] [LocallyOfFiniteType c₁] [QuasiCompact c₁]
    [IsSeparated c₂] [LocallyOfFiniteType c₂] [QuasiCompact c₂]
    {E₁ N₁ : _root_.DerivedCategory (Sheaf Z₁.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {E₂ N₂ : _root_.DerivedCategory (Sheaf Z₂.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hE₁ : constructibleFiniteTor (ModuleCat.{u + 1} Λ) Z₁ E₁)
    (hE₂ : constructibleFiniteTor (ModuleCat.{u + 1} Λ) Z₂ E₂)
    (hN₁ : constructibleFiniteTor (ModuleCat.{u + 1} Λ) Z₁ N₁)
    (hN₂ : constructibleFiniteTor (ModuleCat.{u + 1} Λ) Z₂ N₂) :
    Nonempty (externalProduct (ModuleCat.{u + 1} Λ) c₁ c₂
        ((RHom(Z₁)[ModuleCat.{u + 1} Λ].obj (op E₁)).obj N₁)
        ((RHom(Z₂)[ModuleCat.{u + 1} Λ].obj (op E₂)).obj N₂) ≅
      (RHom(pullback c₁ c₂)[ModuleCat.{u + 1} Λ].obj
          (op (externalProduct (ModuleCat.{u + 1} Λ) c₁ c₂ E₁ E₂))).obj
        (externalProduct (ModuleCat.{u + 1} Λ) c₁ c₂ N₁ N₂)) :=
  have := isIso_externalHomMap Λ c₁ c₂ hE₁ hE₂ hN₁ hN₂
  ⟨asIso (externalHomMap (ModuleCat.{u + 1} Λ) c₁ c₂ E₁ N₁ E₂ N₂)⟩

/-- Transport of an exceptional inverse image along a factorization through an isomorphism:
if `φ ≫ π = ψ` with `π` an isomorphism of schemes, then `Rψ^! M ≅ Rφ^! (Lπ^* M)`. -/
theorem nonempty_iso_rightDerivedUpperShriek_of_comp_isIso {P Q X : Scheme.{u}} (φ : P ⟶ Q)
    (π : Q ⟶ X) (ψ : P ⟶ X) [IsIso π] [HasCompactification φ] [HasCompactification π]
    [HasCompactification ψ] [HasCompactification (φ ≫ π)] [QuasiCompact (φ ≫ π)]
    (h : φ ≫ π = ψ)
    (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Nonempty ((R(ψ)^![ModuleCat.{u + 1} Λ]).obj M ≅
      (R(φ)^![ModuleCat.{u + 1} Λ]).obj ((L((π)^*[ModuleCat.{u + 1} Λ])).obj M)) := by
  have hcongr : ∀ (χ : P ⟶ X) [HasCompactification χ], χ = φ ≫ π →
      Nonempty (R(χ)^![ModuleCat.{u + 1} Λ] ≅ R(φ ≫ π)^![ModuleCat.{u + 1} Λ]) := by
    rintro χ _ rfl
    exact ⟨Iso.refl _⟩
  obtain ⟨c₀⟩ := hcongr ψ h.symm
  obtain ⟨c₁⟩ := nonempty_iso_rightDerivedUpperShriek_comp Λ φ π
  exact ⟨c₀.app M ≪≫ c₁.app M ≪≫
    (R(φ)^![ModuleCat.{u + 1} Λ]).mapIso ((rightDerivedUpperShriekIsoOfIsIso Λ π).app M)⟩

/-- The exceptional Künneth isomorphism `α` for `𝟙_X × b`: for `a : X ⟶ Spec k`,
`b : Y ⟶ Spec k` and `M ∈ Dctf(X, Λ)`, with `p_X : X ×_k Y ⟶ X` the first projection,

`Rp_X^! M ≅ M ⊠ ω_Y`.

This is `α` (`prop-trf-exceptional-kunneth`) for `f₁ = 𝟙_X`, `f₂ = b` and the coefficients
`(M, Λ_k)`, read through `R(𝟙_X)^! ≅ 𝟭`, `X ×_k k ≅ X` and the composition law for `R^!`. -/
theorem nonempty_iso_rightDerivedUpperShriek_pullbackFst
    [HasInvertibleExponent Λ (Spec (.of k))] {X Y : Scheme.{u}} (a : X ⟶ Spec (.of k))
    (b : Y ⟶ Spec (.of k)) [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    [HasCompactification b] [QuasiCompact b] [HasCompactification (pullback.fst a b)]
    {M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hM : constructibleFiniteTor (ModuleCat.{u + 1} Λ) X M) :
    Nonempty ((R(pullback.fst a b)^![ModuleCat.{u + 1} Λ]).obj M ≅
      externalProduct (ModuleCat.{u + 1} Λ) a b M (dualizingComplex _ b)) := by
  -- `π : X ×_k k ⟶ X` is an isomorphism
  obtain ⟨π, hπ⟩ : ∃ π, π = pullback.fst a (𝟙 (Spec (.of k))) := ⟨_, rfl⟩
  have : IsIso π := hπ ▸ inferInstance
  have : HasCompactification (b ≫ 𝟙 (Spec (.of k))) := HasCompactification.comp_of_isProper _
  have hφ : pullback.fst (𝟙 X ≫ a) (b ≫ 𝟙 (Spec (.of k))) ≫ (𝟙 X ≫ inv π) =
      pullback.mapOverBase (𝟙 X) b a (𝟙 (Spec (.of k))) := by
    rw [← cancel_mono π, hπ]
    simp
  have : HasCompactification (pullback.fst (𝟙 X ≫ a) (b ≫ 𝟙 (Spec (.of k))) ≫ (𝟙 X ≫ inv π)) :=
    HasCompactification.comp_of_isProper _
  have : HasCompactification (pullback.mapOverBase (𝟙 X) b a (𝟙 (Spec (.of k)))) := .of_eq hφ
  obtain ⟨e₀⟩ := nonempty_iso_exceptional_temp Λ a (𝟙 _) (𝟙 X) b hM
    (constructibleFiniteTor_unit Λ _)
  -- transport along `𝟙 X ≫ a = a` and `b ≫ 𝟙 = b`
  have key : ∀ (a' : X ⟶ Spec (.of k)) (b' : Y ⟶ Spec (.of k)), a' = a → b' = b →
      ∀ (φ : pullback a' b' ⟶ pullback a (𝟙 (Spec (.of k)))) [HasCompactification φ]
        [QuasiCompact (φ ≫ π)] [HasCompactification (φ ≫ π)], φ ≫ π = pullback.fst a' b' →
      Nonempty (externalProduct (ModuleCat.{u + 1} Λ) a' b'
          ((R(𝟙 X)^![ModuleCat.{u + 1} Λ]).obj M) (dualizingComplex _ b) ≅
        (R(φ)^![ModuleCat.{u + 1} Λ]).obj
          (externalProduct (ModuleCat.{u + 1} Λ) a (𝟙 _) M (𝟙_ _))) →
      Nonempty ((R(pullback.fst a b)^![ModuleCat.{u + 1} Λ]).obj M ≅
        externalProduct (ModuleCat.{u + 1} Λ) a b M (dualizingComplex _ b)) := by
    rintro a' b' rfl rfl φ _ _ _ h ⟨e⟩
    obtain ⟨c⟩ := nonempty_iso_rightDerivedUpperShriek_of_comp_isIso Λ φ π _ h M
    subst hπ
    exact ⟨c ≪≫ (R(φ)^![ModuleCat.{u + 1} Λ]).mapIso
        (externalProductUnitRightIso Λ a (𝟙 _) M).symm ≪≫ e.symm ≪≫
      externalProductMapIso _ a' b' ((rightDerivedUpperShriekIdIso Λ X).app M) (Iso.refl _)⟩
  have hφπ : pullback.mapOverBase (𝟙 X) b a (𝟙 (Spec (.of k))) ≫ π =
      pullback.fst (𝟙 X ≫ a) (b ≫ 𝟙 (Spec (.of k))) := by
    rw [hπ, pullback.mapOverBase_fst, Category.comp_id]
  have : HasCompactification (pullback.mapOverBase (𝟙 X) b a (𝟙 (Spec (.of k))) ≫ π) :=
    .of_eq hφπ.symm
  have : QuasiCompact (pullback.mapOverBase (𝟙 X) b a (𝟙 (Spec (.of k))) ≫ π) := by
    rw [hφπ]
    infer_instance
  exact key _ _ (Category.id_comp a) (Category.comp_id b) _ hφπ e₀

/-- Blueprint `thm-trf-kunneth-verdier`: Künneth–Verdier isomorphism; the `κ` map.

For `X`, `Y` separated of finite type over a field `k`, `Λ` finite of invertible exponent,
`M ∈ Dctf(X, Λ)` and `N ∈ Dctf(Y, Λ)`,

`κ : M ⊠ 𝔻_Y N ≅ RHom(p_Y^* N, Rp_X^! M)`.

As in the blueprint it is the external Hom isomorphism `β` (`prop-trf-external-hom`) for the
pairs `(Λ_X, M)` and `(N, ω_Y)`, using the unit identifications `RHom(Λ_X, M) ≅ M` and
`Λ_X ⊠ N ≅ p_Y^* N`, followed by `RHom(1, α)` for the identification `M ⊠ ω_Y ≅ Rp_X^! M` of
`prop-trf-exceptional-kunneth`. -/
theorem nonempty_iso_kunnethVerdier [HasInvertibleExponent Λ (Spec (.of k))] {X Y : Scheme.{u}}
    (a : X ⟶ Spec (.of k)) (b : Y ⟶ Spec (.of k)) [IsSeparated a] [LocallyOfFiniteType a]
    [QuasiCompact a] [HasCompactification b] [QuasiCompact b]
    [HasCompactification (pullback.fst a b)]
    {M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {N : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hM : constructibleFiniteTor (ModuleCat.{u + 1} Λ) X M)
    (hN : constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y N) :
    Nonempty (externalProduct (ModuleCat.{u + 1} Λ) a b M
        ((verdierDual (ModuleCat.{u + 1} Λ) b).obj (op N)) ≅
      (RHom(pullback a b)[ModuleCat.{u + 1} Λ].obj
          (op ((L((pullback.snd a b)^*[ModuleCat.{u + 1} Λ])).obj N))).obj
        ((R(pullback.fst a b)^![ModuleCat.{u + 1} Λ]).obj M)) := by
  have hω : constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y (dualizingComplex _ b) :=
    constructibleFiniteTor_dualizingComplex Λ (𝟙 _) b (constructibleFiniteTor_unit Λ _)
  obtain ⟨β⟩ := nonempty_iso_externalHom Λ a b (constructibleFiniteTor_unit Λ X) hN hM hω
  obtain ⟨α⟩ := nonempty_iso_rightDerivedUpperShriek_pullbackFst Λ a b hM
  exact ⟨externalProductMapIso _ a b ((derivedHomUnitIso Λ X).app M).symm (Iso.refl _) ≪≫ β ≪≫
    ((RHom(pullback a b)[ModuleCat.{u + 1} Λ]).mapIso
      (externalProductUnitLeftIso Λ a b N).op).app _ ≪≫
    ((RHom(pullback a b)[ModuleCat.{u + 1} Λ]).obj _).mapIso α.symm⟩

/-- The Künneth–Verdier isomorphism over `k` for all separated finite-type `k`-schemes
(`thm-trf-kunneth-verdier`), in the form of `AlgebraicGeometry.Etale.KunnethVerdier`. -/
theorem kunnethVerdier [HasInvertibleExponent Λ (Spec (.of k))] : KunnethVerdier Λ k :=
  fun _ _ a b _ _ _ _ _ _ _ _ hM hN ↦ nonempty_iso_kunnethVerdier Λ a b hM hN

/-- Verdier duality commutes with external products over `k` (`rem-sf-kv-formal`):
`𝔻_{X ×_k Y} (P ⊠ Q) ≅ 𝔻_X P ⊠ 𝔻_Y Q`, from the Künneth–Verdier isomorphism by
`AlgebraicGeometry.Etale.verdierDualExternalProduct_iff_kunnethVerdier`. -/
theorem verdierDualExternalProduct [HasInvertibleExponent Λ (Spec (.of k))] :
    VerdierDualExternalProduct Λ k :=
  (kunnethVerdier Λ).verdierDualExternalProduct

end Etale

end AlgebraicGeometry
