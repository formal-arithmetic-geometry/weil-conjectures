/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Closed.ExternalIhom
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategorySymmetric
public import WeilConjectures.SixFunctors.Etale.Derived.GenericPerfect
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Exceptional.Local
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.ExternalHomMap
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Braided

/-!
# The external Hom map `β` is an isomorphism

Over a field `k`, for a finite coefficient ring `Λ` whose exponent is invertible in `k`, separated
finite-type `k`-schemes `Z₁`, `Z₂` and `Eᵢ ∈ Dctf(Zᵢ, Λ)`, the external Hom map
(`AlgebraicGeometry.Etale.externalHomMap`, `def-sf-kv-maps` (iii))

`β : RHom(E₁, L₁) ⊠ RHom(E₂, L₂) ⟶ RHom(E₁ ⊠ E₂, L₁ ⊠ L₂)`

is an isomorphism (`AlgebraicGeometry.Etale.isIso_externalHomMap`, `prop-trf-external-hom`).

## Strategy

Instead of the dévissage of the blueprint along distinguished triangles in the `Eᵢ`, which would
need `β` to be a morphism of triangulated functors in the contravariant variables, we argue by
Noetherian induction on the support, through the exceptional inverse images along the strata:

* for a morphism `g₁ : Z₁' ⟶ Z₁` with base change `g = g₁ × 𝟙 : Z₁' ×_k Z₂ ⟶ Z₁ ×_k Z₂`, the map
  `Rg^! β(E₁, L₁, E₂, L₂)` is identified with `β(Lg₁^* E₁, Rg₁^! L₁, E₂, L₂)`, through the
  exceptional Künneth formula (`AlgebraicGeometry.Etale.isExceptionalKunneth`: the base change
  map and the tensor map of `Rg^!` are isomorphisms) and the compatibility of the tensor maps with
  base change (`CategoryTheory.Adjunction.isIso_map_externalIhomMap_iff`);
* for an open immersion `j` and the complementary closed immersion `i`, `Rj^!` and `Ri^!` are
  jointly conservative (the supported localization triangle);
* on a dense open, `E₁` has a dual (`AlgebraicGeometry.Etale.exists_dense_open_exactPairing`),
  and the external Hom map of objects with duals is an isomorphism by a formal argument
  (`CategoryTheory.MonoidalClosed.isIso_externalIhomMap_of_exactPairing`);
* the second variable is treated in the same way after exchanging the factors
  (`CategoryTheory.MonoidalClosed.isIso_externalIhomMap_swap_iff`).
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite Functor.LaxMonoidal Functor.OplaxMonoidal

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

open _root_.AlgebraicGeometry.Etale.DerivedCategory

namespace Etale

section Braided

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [UpperStarPreservesFlat A]

attribute [local instance] derivedBraidedCategory

/-- The derived pullback `Lg^*` as a braided monoidal functor, for its monoidal structure
`AlgebraicGeometry.Etale.leftDerivedUpperStarMonoidal` and the derived braidings
(`AlgebraicGeometry.Etale.leftDerivedUpperStar_μ_map_braiding_hom`). -/
@[instance_reducible]
noncomputable def leftDerivedUpperStarBraidedFunctor {Z Y : Scheme.{u}} (g : Z ⟶ Y) :
    (L((g)^*[A])).Braided :=
  { leftDerivedUpperStarMonoidal A g with
    braided := leftDerivedUpperStar_μ_map_braiding_hom A g }

attribute [local instance] leftDerivedUpperStarBraidedFunctor in
/-- The composition isomorphism `L(g₁ ≫ g₂)^* ≅ Lg₂^* ⋙ Lg₁^*` is monoidal: its inverse is
compatible with the tensor structures. -/
lemma μ_comp_map_μ_comp_leftDerivedUpperStarComp_inv_app {T S R : Scheme.{u}} (g₁ : T ⟶ S)
    (g₂ : S ⟶ R) (K M : _root_.DerivedCategory (Sheaf R.smallEtaleTopology A)) :
    μ L((g₁)^*[A]) (L((g₂)^*[A]).obj K) (L((g₂)^*[A]).obj M) ≫ L((g₁)^*[A]).map (μ _ K M) ≫
        (leftDerivedUpperStarComp A g₁ g₂ (g₁ ≫ g₂) rfl).inv.app (K ⊗ M) =
      ((leftDerivedUpperStarComp A g₁ g₂ (g₁ ≫ g₂) rfl).inv.app K ⊗ₘ
        (leftDerivedUpperStarComp A g₁ g₂ (g₁ ≫ g₂) rfl).inv.app M) ≫ μ L((g₁ ≫ g₂)^*[A]) K M := by
  have h : δ L((g₁ ≫ g₂)^*[A]) K M ≫
      ((leftDerivedUpperStarComp A g₁ g₂ (g₁ ≫ g₂) rfl).hom.app K ⊗ₘ
        (leftDerivedUpperStarComp A g₁ g₂ (g₁ ≫ g₂) rfl).hom.app M) =
      (leftDerivedUpperStarComp A g₁ g₂ (g₁ ≫ g₂) rfl).hom.app (K ⊗ M) ≫
        L((g₁)^*[A]).map (δ L((g₂)^*[A]) K M) ≫ δ L((g₁)^*[A]) _ _ :=
    leftDerivedUpperStarTensorComparison_comp A g₁ g₂ (g₁ ≫ g₂) rfl K M
  rw [← cancel_epi (δ L((g₁ ≫ g₂)^*[A]) K M ≫
    ((leftDerivedUpperStarComp A g₁ g₂ (g₁ ≫ g₂) rfl).hom.app K ⊗ₘ
      (leftDerivedUpperStarComp A g₁ g₂ (g₁ ≫ g₂) rfl).hom.app M))]
  simp only [Category.assoc]
  rw [tensorHom_comp_tensorHom_assoc, Iso.hom_inv_id_app, Iso.hom_inv_id_app, id_tensorHom_id,
    Category.id_comp, reassoc_of% h, Functor.Monoidal.δ_μ_assoc, ← Functor.map_comp_assoc,
    Functor.Monoidal.δ_μ, CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id_app,
    Functor.Monoidal.δ_μ]

end Braided

section BaseChange

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [UpperStarPreservesFlat A]
  {FC : A → A → Type*} {CC : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

attribute [local instance high] SymmetricCategory.toBraidedCategory

attribute [local instance] _root_.DerivedCategory.symmetricCategory
  leftDerivedUpperStarBraidedFunctor

/-- **`β` under the exceptional inverse image, abstractly.** Let `g : P' ⟶ P` be the base change
of `g₁ : Z₁' ⟶ Z₁` along `p₁ : P ⟶ Z₁`, with `p₁' : P' ⟶ Z₁'`, and let `p₂ : P ⟶ Z₂`. Given an
invertible base change map `Ex : Lp₁^* Rg₁_! ⟶ Rg_! Lp₁'^*` compatible with the projection maps,
whose mate `Lp₁'^* Rg₁^! ⟶ Rg^! Lp₁^*` is invertible, and assuming that the projection maps are
invertible and associative and that the tensor maps of `Rg^!` at `(Lp₁^* M, Lp₂^* N)` are
invertible, `Rg^!` of the external Hom map of `(E₁, L₁, E₂, L₂)` is an isomorphism if and only if
the external Hom map of `(Lg₁^* E₁, Rg₁^! L₁, E₂, L₂)` over `P'` is. -/
theorem isIso_map_externalIhomMap_iff_of_baseChange {Z₁ Z₂ P Z₁' P' : Scheme.{u}}
    {p₁ : P ⟶ Z₁} {p₂ : P ⟶ Z₂} {g₁ : Z₁' ⟶ Z₁} [HasCompactification g₁] {p₁' : P' ⟶ Z₁'}
    {g : P' ⟶ P} [HasCompactification g] [IsIso (projectionMap A g)]
    [IsIso (projectionMap A g₁)] (sq : CommSq p₁' g g₁ p₁)
    (Ex : R(g₁)_![A] ⋙ L((p₁)^*[A]) ⟶ L((p₁')^*[A]) ⋙ R(g)_![A]) [IsIso Ex]
    (hEx : ∀ (M : _root_.DerivedCategory (Sheaf Z₁'.smallEtaleTopology A))
      (N : _root_.DerivedCategory (Sheaf Z₁.smallEtaleTopology A)),
      (L((p₁)^*[A])).map (X := (R(g₁)_![A]).obj M ⊗ N)
          (Y := (R(g₁)_![A]).obj (M ⊗ (L((g₁)^*[A])).obj N)) (((projectionMap A g₁).app M).app N) ≫
        Ex.app (M ⊗ (L((g₁)^*[A])).obj N) ≫
        (R(g)_![A]).map (δ L((p₁')^*[A]) M ((L((g₁)^*[A])).obj N)) ≫
        (R(g)_![A]).map ((L((p₁')^*[A])).obj M ◁ derivedSquareUpperStarIsoInvApp A sq N) =
      δ L((p₁)^*[A]) ((R(g₁)_![A]).obj M) N ≫
        CategoryStruct.comp (Y := (R(g)_![A]).obj ((L((p₁')^*[A])).obj M) ⊗ (L((p₁)^*[A])).obj N)
          (Z := (R(g)_![A]).obj ((L((p₁')^*[A])).obj M ⊗
            (L((g)^*[A])).obj ((L((p₁)^*[A])).obj N)))
          (Ex.app M ▷ (L((p₁)^*[A])).obj N)
          (((projectionMap A g).app ((L((p₁')^*[A])).obj M)).app ((L((p₁)^*[A])).obj N)))
    (hBC : ∀ N, IsIso ((mateEquiv (rightDerivedUpperShriekAdjunction A g₁)
      (rightDerivedUpperShriekAdjunction A g) (inv Ex)).natTrans.app N))
    (hτ : ∀ M N, IsIso ((rightDerivedUpperShriekAdjunction A g).projectionTensorMap
      (fun M N ↦ ((projectionMap A g).app M).app N) ((L((p₁)^*[A])).obj M)
      ((L((p₂)^*[A])).obj N)))
    (hassoc : ProjectionMapAssociativity A g)
    (E₁ L₁ : _root_.DerivedCategory (Sheaf Z₁.smallEtaleTopology A))
    (E₂ L₂ : _root_.DerivedCategory (Sheaf Z₂.smallEtaleTopology A)) :
    IsIso ((R(g)^![A]).map (MonoidalClosed.externalIhomMap
      (L((p₁)^*[A])) (L((p₂)^*[A])) E₁ L₁ E₂ L₂)) ↔
      IsIso (MonoidalClosed.externalIhomMap (L((p₁')^*[A])) (L((g ≫ p₂)^*[A]))
        ((L((g₁)^*[A])).obj E₁) ((R(g₁)^![A]).obj L₁) E₂ L₂) := by
  have : ∀ N, IsIso (derivedSquareUpperStarIsoInvApp A sq N) := fun N ↦ by
    unfold derivedSquareUpperStarIsoInvApp
    infer_instance
  exact Adjunction.isIso_map_externalIhomMap_iff (rightDerivedUpperShriekAdjunction A g)
    (fun M N ↦ ((projectionMap A g).app M).app N) (rightDerivedUpperShriekAdjunction A g₁)
    (fun M N ↦ ((projectionMap A g₁).app M).app N)
    (projectionMap_app_app_naturality_left g) (projectionMap_app_app_naturality_left g₁)
    Ex (inv Ex) (fun M ↦ by simp [NatIso.isIso_inv_app])
    (fun N ↦ derivedSquareUpperStarIsoInvApp A sq N) hEx
    (projectionMap_app_app_naturality_right g) hassoc.assoc
    (leftDerivedUpperStarComp _ g p₂ (g ≫ p₂) rfl).symm
    (μ_comp_map_μ_comp_leftDerivedUpperStarComp_inv_app _ g p₂) E₁ L₁ E₂ L₂

end BaseChange

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] (k : Type u) [Field k]

-- Search the braiding of `ModuleCat Λ` through its symmetric structure, as in the generic
-- definitions of the derived tensor product.
attribute [local instance high] SymmetricCategory.toBraidedCategory

-- As in `WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.BaseChange`, so that the
-- compatibility of the projection map with base change matches syntactically.
attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint ModuleCat.hasColimitsOfShape
  ModuleCat.hasColimitsOfSize

attribute [local instance] _root_.DerivedCategory.symmetricCategory
  leftDerivedUpperStarBraidedFunctor

-- Give instance search the canonical larger-universe model of the small étale site.
local instance essentiallySmall_etale_externalHom (X : Scheme.{u}) :
    EssentiallySmall.{u + 1} X.Etale :=
  have : LocallySmall.{u + 1} X.Etale :=
    @locallySmall_of_univLE X.Etale _ (@univLE_of_max.{u, u + 1} UnivLE.self)
  essentiallySmall_of_small_of_locallySmall _

attribute [local instance 20000] Etale.sheafBraidedCategory

section Devissage

variable [HasInvertibleExponent Λ (Spec (.of k))]

/-- **`β` under the exceptional inverse image along a stratum.** Let `P = Z₁ ×_k Z₂` with
projections `p₁`, `p₂`, let `g₁ : Z₁' ⟶ Z₁` be quasi-compact and compactifiable, and let
`g : P' ⟶ P` be its base change along `p₁`, with `p₁' : P' ⟶ Z₁'`. Then `Rg^!` of the external
Hom map of `(E₁, L₁, E₂, L₂)` is an isomorphism if and only if the external Hom map of
`(Lg₁^* E₁, Rg₁^! L₁, E₂, L₂)` over `P'` is. -/
theorem isIso_map_externalIhomMap_iff_of_isPullback {Z₁ Z₂ P Z₁' P' : Scheme.{u}}
    (c₁ : Z₁ ⟶ Spec (.of k)) (c₂ : Z₂ ⟶ Spec (.of k)) [LocallyOfFiniteType c₁] [QuasiCompact c₁]
    [LocallyOfFiniteType c₂] [QuasiCompact c₂] {p₁ : P ⟶ Z₁} {p₂ : P ⟶ Z₂}
    (sqP : IsPullback p₁ p₂ c₁ c₂) (g₁ : Z₁' ⟶ Z₁) [HasCompactification g₁] [QuasiCompact g₁]
    {p₁' : P' ⟶ Z₁'} {g : P' ⟶ P} (sq : IsPullback p₁' g g₁ p₁) [HasCompactification g]
    [QuasiCompact g]
    (E₁ L₁ : _root_.DerivedCategory (Sheaf Z₁.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (E₂ L₂ : _root_.DerivedCategory (Sheaf Z₂.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso ((R(g)^![ModuleCat.{u + 1} Λ]).map (MonoidalClosed.externalIhomMap
      (L((p₁)^*[ModuleCat.{u + 1} Λ])) (L((p₂)^*[ModuleCat.{u + 1} Λ])) E₁ L₁ E₂ L₂)) ↔
      IsIso (MonoidalClosed.externalIhomMap (L((p₁')^*[ModuleCat.{u + 1} Λ]))
        (L((g ≫ p₂)^*[ModuleCat.{u + 1} Λ])) ((L((g₁)^*[ModuleCat.{u + 1} Λ])).obj E₁)
        ((R(g₁)^![ModuleCat.{u + 1} Λ]).obj L₁) E₂ L₂) := by
  obtain ⟨hBC, hτ⟩ := isExceptionalKunneth Λ k g₁ c₁ c₁ c₂ sqP sq
  have := isIso_rightDerivedLowerShriekBaseChangeMap Λ sq
  exact isIso_map_externalIhomMap_iff_of_baseChange sq.toCommSq
    (rightDerivedLowerShriekBaseChangeMap Λ sq)
    (projectionMap_rightDerivedLowerShriekBaseChangeMap Λ sq) hBC (fun M N ↦ hτ M N)
    (projectionMapAssociativity Λ g) E₁ L₁ E₂ L₂

/-- The ranges of the base changes, along a morphism `q`, of complementary open and closed
immersions are complementary. -/
lemma range_eq_compl_range_of_isPullback {Y Q Z U ZQ UQ : Scheme.{u}} {i : Z ⟶ Y} {j : U ⟶ Y}
    (hij : Set.range i.base = (Set.range j.base)ᶜ) {q : Q ⟶ Y} {qZ : ZQ ⟶ Z} {iQ : ZQ ⟶ Q}
    (sqZ : IsPullback qZ iQ i q) {qU : UQ ⟶ U} {jQ : UQ ⟶ Q} (sqU : IsPullback qU jQ j q) :
    Set.range iQ.base = (Set.range jQ.base)ᶜ := by
  have hr {T T' : Scheme.{u}} {a : T ⟶ Y} {a' : T' ⟶ T} {b : T' ⟶ Q}
      (s : IsPullback a' b a q) : Set.range b.base = q.base ⁻¹' Set.range a.base := by
    rw [← s.isoPullback_hom_snd, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Set.range_eq_univ.2 s.isoPullback.hom.surjective, Set.image_univ]
    exact Scheme.Pullback.range_snd a q
  rw [hr sqZ, hr sqU, hij, Set.preimage_compl]

/-- **Joint conservativity of `Rj^!` and `Ri^!`.** For a closed immersion `i` and the
complementary open immersion `j`, a morphism `f` of `D(X_ét, Λ)` is an isomorphism as soon as
`Rj^! f` and `Ri^! f` are: by the supported localization triangle
`Ri_! Ri^! ⟶ 𝟭 ⟶ Rj_* Lj^* ⟶`, and `Rj^! ≅ Lj^*`. -/
theorem isIso_of_isIso_rightDerivedUpperShriek_map_of_range_eq_compl {Z X U : Scheme.{u}}
    (i : Z ⟶ X) (j : U ⟶ X)
    [IsClosedImmersion i] [HasCompactification i] [IsOpenImmersion j] [HasCompactification j]
    [QuasiCompact j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    {M N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))} (f : M ⟶ N)
    (hj : IsIso ((R(j)^![ModuleCat.{u + 1} Λ]).map f))
    (hi : IsIso ((R(i)^![ModuleCat.{u + 1} Λ]).map f)) : IsIso f := by
  have : IsIso ((L((j)^*[ModuleCat.{u + 1} Λ])).map f) := by
    have : IsIso ((D((j)^*[ModuleCat.{u + 1} Λ])).map f) :=
      (NatIso.isIso_map_iff (rightDerivedUpperShriekIsoOfIsOpenImmersion Λ j) f).1 hj
    exact (NatIso.isIso_map_iff (leftDerivedUpperStarIsoMapDerivedCategory _ j) f).2 this
  have hM := supportedLocalizationTriangle_mem_distTriang (ModuleCat.{u + 1} Λ) i j hij M
  have hN := supportedLocalizationTriangle_mem_distTriang (ModuleCat.{u + 1} Λ) i j hij N
  obtain ⟨τ, h₁, h₂, h₃⟩ := exists_triangleHom_supportedLocalization (ModuleCat.{u + 1} Λ) i j
    (hij ▸ disjoint_compl_left) f hM hN
  have := Pretriangulated.isIso₂_of_isIso₁₃ τ hM hN (by rw [h₁]; infer_instance)
    (by rw [h₃]; infer_instance)
  rwa [h₂] at this
omit [Finite Λ] in
/-- Every morphism between objects of `D(X_ét, Λ)` on an empty scheme is an isomorphism. -/
lemma isIso_of_isEmpty {X : Scheme.{u}} [IsEmpty X]
    {M N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (f : M ⟶ N) : IsIso f :=
  (isZero_derivedCategory_of_isEmpty _ X M).isIso (isZero_derivedCategory_of_isEmpty _ X N) f

/-- **Dévissage of `β` in the first variable.** Fix `E₂, L₂` on `Z₂`. If `β(E₁, L₁, E₂, L₂)` is an
isomorphism whenever `E₁` has a left dual (on any scheme of finite type over `k`), then it is an
isomorphism for every `E₁ ∈ Dctf(Z₁, Λ)`: by Noetherian induction on the support, `E₁` has a left
dual on a dense open `V` (`AlgebraicGeometry.Etale.exists_dense_open_exactPairing`), and `Rg^! β`
for `g` the base change of the inclusion of `V` or of its closed complement is `β` for the
restricted data (`AlgebraicGeometry.Etale.isIso_map_externalIhomMap_iff_of_isPullback`). -/
theorem isIso_externalIhomMap_of_forall_exactPairing {Z₂ : Scheme.{u}} (c₂ : Z₂ ⟶ Spec (.of k))
    [LocallyOfFiniteType c₂] [QuasiCompact c₂]
    (E₂ L₂ : _root_.DerivedCategory (Sheaf Z₂.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (H : ∀ {Z₁ P : Scheme.{u}} (c₁ : Z₁ ⟶ Spec (.of k)) [LocallyOfFiniteType c₁]
      [QuasiCompact c₁] {p₁ : P ⟶ Z₁} {p₂ : P ⟶ Z₂} (_ : IsPullback p₁ p₂ c₁ c₂)
      (D E₁ L₁ : _root_.DerivedCategory (Sheaf Z₁.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
      [ExactPairing D E₁],
      IsIso (MonoidalClosed.externalIhomMap (L((p₁)^*[ModuleCat.{u + 1} Λ]))
        (L((p₂)^*[ModuleCat.{u + 1} Λ])) E₁ L₁ E₂ L₂))
    {Z₁ P : Scheme.{u}} (c₁ : Z₁ ⟶ Spec (.of k)) [LocallyOfFiniteType c₁] [QuasiCompact c₁]
    {p₁ : P ⟶ Z₁} {p₂ : P ⟶ Z₂} (sqP : IsPullback p₁ p₂ c₁ c₂)
    {E₁ : _root_.DerivedCategory (Sheaf Z₁.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hE₁ : constructibleFiniteTor (ModuleCat.{u + 1} Λ) Z₁ E₁)
    (L₁ : _root_.DerivedCategory (Sheaf Z₁.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso (MonoidalClosed.externalIhomMap (L((p₁)^*[ModuleCat.{u + 1} Λ]))
      (L((p₂)^*[ModuleCat.{u + 1} Λ])) E₁ L₁ E₂ L₂) := by
  have : CompactSpace Z₁ := QuasiCompact.compactSpace_of_compactSpace c₁
  have : IsNoetherian Z₁ := { __ := LocallyOfFiniteType.isLocallyNoetherian c₁ }
  suffices key : ∀ (T : TopologicalSpace.Closeds Z₁) {Y : Scheme.{u}} (ι : Y ⟶ Z₁)
      [IsClosedImmersion ι], Set.range ι.base = T → ∀ {Q : Scheme.{u}} {q₁ : Q ⟶ Y}
      {q₂ : Q ⟶ Z₂} (_ : IsPullback q₁ q₂ (ι ≫ c₁) c₂)
      {E : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
      (_ : constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y E)
      (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      IsIso (MonoidalClosed.externalIhomMap (L((q₁)^*[ModuleCat.{u + 1} Λ]))
        (L((q₂)^*[ModuleCat.{u + 1} Λ])) E L E₂ L₂) by
    exact key ⊤ (𝟙 Z₁) (by simp) (by simpa using sqP) hE₁ L₁
  intro T
  induction T using WellFoundedLT.induction with
  | ind T ih =>
  intro Y ι _ hT Q q₁ q₂ sqQ E hE L
  by_cases hY : IsEmpty Y
  · have : IsEmpty Q := ⟨fun x ↦ hY.false (q₁ x)⟩
    exact isIso_of_isEmpty Λ _
  rw [not_isEmpty_iff] at hY
  have : TopologicalSpace.NoetherianSpace Y := ι.isClosedEmbedding.isInducing.noetherianSpace
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (ι ≫ c₁)
  have : IsNoetherian Y := { __ := LocallyOfFiniteType.isLocallyNoetherian (ι ≫ c₁) }
  obtain ⟨V, hVd, hV⟩ := exists_dense_open_exactPairing Λ hE
  obtain ⟨D, -, ⟨hD⟩⟩ := hV V le_rfl
  have : TopologicalSpace.NoetherianSpace V := V.ι.isOpenEmbedding.isInducing.noetherianSpace
  have : QuasiCompact V.ι := ⟨fun U _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  have : HasCompactification V.ι := (Compactification.ofIsOpenImmersion V.ι).hasCompactification
  -- the base changes of the open immersion `V ⟶ Y` and of its closed complement
  have sqV := IsPullback.of_hasPullback V.ι q₁
  have sqC := IsPullback.of_hasPullback V.closedComplement q₁
  have : HasCompactification (pullback.snd V.ι q₁) := .of_isPullback sqV
  have : HasCompactification (pullback.snd V.closedComplement q₁) := .of_isPullback sqC
  have : QuasiCompact (pullback.snd V.ι q₁) := MorphismProperty.of_isPullback sqV inferInstance
  have : QuasiCompact (pullback.snd V.closedComplement q₁) :=
    MorphismProperty.of_isPullback sqC inferInstance
  have : IsOpenImmersion (pullback.snd V.ι q₁) := MorphismProperty.of_isPullback sqV inferInstance
  have : IsClosedImmersion (pullback.snd V.closedComplement q₁) :=
    MorphismProperty.of_isPullback sqC inferInstance
  have : LocallyOfFiniteType (ι ≫ c₁) := inferInstance
  refine isIso_of_isIso_rightDerivedUpperShriek_map_of_range_eq_compl Λ
    (pullback.snd V.closedComplement q₁)
    (pullback.snd V.ι q₁) (range_eq_compl_range_of_isPullback (by simp) sqC sqV) _ ?_ ?_
  · -- the open part: `E` has a left dual on `V`
    rw [isIso_map_externalIhomMap_iff_of_isPullback Λ k (ι ≫ c₁) c₂ sqQ V.ι sqV]
    exact H (V.ι ≫ ι ≫ c₁) (sqV.paste_vert sqQ) D _ _
  · -- the closed part: by induction on the support
    rw [isIso_map_externalIhomMap_iff_of_isPullback Λ k (ι ≫ c₁) c₂ sqQ V.closedComplement sqC]
    have hlt : (⟨Set.range (V.closedComplement ≫ ι).base,
        (V.closedComplement ≫ ι).isClosedEmbedding.isClosed_range⟩ :
          TopologicalSpace.Closeds Z₁) < T := by
      rw [← SetLike.coe_ssubset_coe, TopologicalSpace.Closeds.coe_mk, ← hT, Scheme.Hom.comp_base,
        TopCat.coe_comp, Set.range_comp]
      refine (Set.image_subset_range _ _).ssubset_of_ne fun h ↦ ?_
      obtain ⟨z, hz⟩ := hVd.nonempty
      obtain ⟨y, hy, hyz⟩ : ι.base z ∈ ι.base '' Set.range V.closedComplement.base :=
        h ▸ ⟨z, rfl⟩
      rw [ι.isClosedEmbedding.injective hyz, V.range_closedComplement] at hy
      exact hy hz
    exact ih _ hlt (V.closedComplement ≫ ι) rfl (by simpa using sqC.paste_vert sqQ)
      (constructibleFiniteTor_leftDerivedUpperStar _ _ hE) _

end Devissage

variable {k}

/-- Blueprint `prop-trf-external-hom`: External Hom; the `β` map.

Over a field `k`, for a finite coefficient ring `Λ` of invertible exponent, separated
finite-type `k`-schemes `Z₁`, `Z₂` and `Eᵢ, Nᵢ ∈ Dctf(Zᵢ, Λ)`, the external Hom map of
`def-sf-kv-maps` (iii) (`AlgebraicGeometry.Etale.externalHomMap`)

`β : RHom(E₁, N₁) ⊠ RHom(E₂, N₂) ⟶ RHom(E₁ ⊠ E₂, N₁ ⊠ N₂)`

is an isomorphism. (Only `Eᵢ ∈ Dctf` is used.)

The proof is a dévissage in each variable by Noetherian induction on the support
(`AlgebraicGeometry.Etale.isIso_externalIhomMap_of_forall_exactPairing`), the second variable
being reduced to the first by exchanging the factors
(`CategoryTheory.MonoidalClosed.isIso_externalIhomMap_swap_iff`), down to the case where both `Eᵢ`
have duals (`CategoryTheory.MonoidalClosed.isIso_externalIhomMap_of_exactPairing`). -/
theorem isIso_externalHomMap [HasInvertibleExponent Λ (Spec (.of k))] {Z₁ Z₂ : Scheme.{u}}
    (c₁ : Z₁ ⟶ Spec (.of k)) (c₂ : Z₂ ⟶ Spec (.of k))
    [IsSeparated c₁] [LocallyOfFiniteType c₁] [QuasiCompact c₁]
    [IsSeparated c₂] [LocallyOfFiniteType c₂] [QuasiCompact c₂]
    {E₁ N₁ : _root_.DerivedCategory (Sheaf Z₁.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {E₂ N₂ : _root_.DerivedCategory (Sheaf Z₂.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hE₁ : constructibleFiniteTor (ModuleCat.{u + 1} Λ) Z₁ E₁)
    (hE₂ : constructibleFiniteTor (ModuleCat.{u + 1} Λ) Z₂ E₂)
    (_hN₁ : constructibleFiniteTor (ModuleCat.{u + 1} Λ) Z₁ N₁)
    (_hN₂ : constructibleFiniteTor (ModuleCat.{u + 1} Λ) Z₂ N₂) :
    IsIso (externalHomMap (ModuleCat.{u + 1} Λ) c₁ c₂ E₁ N₁ E₂ N₂) := by
  refine isIso_externalIhomMap_of_forall_exactPairing Λ k c₂ E₂ N₂ ?_ c₁
    (IsPullback.of_hasPullback c₁ c₂) hE₁ N₁
  intro Z₁' P' c₁' _ _ p₁' p₂' sq' D' E₁' L₁' _
  rw [← MonoidalClosed.isIso_externalIhomMap_swap_iff]
  refine isIso_externalIhomMap_of_forall_exactPairing Λ k c₁' E₁' L₁' ?_ c₂ sq'.flip hE₂ N₂
  intro Z₂' P'' c₂' _ _ p₁'' p₂'' sq'' D'' E₂' L₂' _
  exact MonoidalClosed.isIso_externalIhomMap_of_exactPairing _ _ D'' E₂' L₂' D' E₁' L₁'

end Etale

end AlgebraicGeometry
