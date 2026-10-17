/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.Local
public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.SmoothBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMapsId
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence

/-!
# Smooth duality for étale morphisms

For an étale morphism `e : V ⟶ W` admitting a compactification, with the exponent of `Λ`
invertible on `V`, the canonical tensor map `θ_{e,K} : ω_e ⊗ᴸ Le^* K ⟶ Re^! K` is an isomorphism
for every `K` and `ω_e ≅ Λ_V`.

* For the identity `𝟙`, the adjunction `R(𝟙)_! ⊣ R(𝟙)^!` is an adjoint equivalence, and the
  tensor maps, adjoint transposes of isomorphisms, are isomorphisms.
* In general, the base change of `e` along itself has the diagonal `Δ : V ⟶ V ×_W V` as a
  section, which is an open immersion. The canonical base change map of `R^!` is an isomorphism
  (`prop-asd-smooth-base-change`) and respects the tensor maps, so `θ_e` pulled back to
  `V ×_W V` is the tensor map of the projection; pulled back further along `Δ`, this is the
  tensor map of `Δ ≫ pr = 𝟙`. This applies first when `e` is an open immersion, where `Δ` is an
  isomorphism, and then to all étale `e`, where `Δ` is an open immersion.

## Main statements

- `AlgebraicGeometry.Etale.isIso_dualizingComplexTensorMap_id`
- `AlgebraicGeometry.Etale.isIso_leftDerivedUpperStar_map_dualizingComplexTensorMap_of_isPullback`
- `AlgebraicGeometry.Etale.isIso_dualizingComplexTensorMap_of_etale`,
  `AlgebraicGeometry.Etale.nonempty_dualizingComplex_iso_of_etale`
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]

-- Search the braiding of `ModuleCat Λ` through its symmetric structure, as in the generic
-- definitions of the derived tensor product.
attribute [local instance high] SymmetricCategory.toBraidedCategory

section BaseChange

-- As in `WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.BaseChange`.
attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint ModuleCat.hasColimitsOfShape
  ModuleCat.hasColimitsOfSize

variable {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
  (sq : IsPullback g' f' f g) [HasCompactification f] [HasCompactification f'] [QuasiCompact f']

/-- **The base change map respects the tensor maps** (blueprint `det-sf-cohsm-base-change`,
clause 2). For a cartesian square `g' ≫ f = f' ≫ g` with quasi-compact `f'`, the pullback along
`g'` of the tensor map `τ_f(M, N) : Rf^! M ⊗ᴸ Lf^* N ⟶ Rf^!(M ⊗ᴸ N)` is, through the base change
maps `β`, the tensor map of `f'` at `(Lg^* M, Lg^* N)`, up to the tensor comparisons of the
pullbacks:
`R'(δ) ∘ β_{M ⊗ N} ∘ Lg'^* τ_f(M, N) = τ_{f'}(Lg^* M, Lg^* N) ∘ (Rf'^! Lg^* M ◁ κ_N) ∘
(β_M ▷ _) ∘ δ`. -/
theorem leftDerivedUpperStar_map_rightDerivedUpperShriekTensorMap
    (M N : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (L((g')^*[ModuleCat.{u + 1} Λ])).map (rightDerivedUpperShriekTensorMap f M N) ≫
        (rightDerivedUpperShriekBaseChangeMap Λ sq).app (M ⊗ N) ≫
        (R(f')^![ModuleCat.{u + 1} Λ]).map (leftDerivedUpperStarTensorIso _ g M N).hom =
      (leftDerivedUpperStarTensorIso _ g' _ _).hom ≫
        (rightDerivedUpperShriekBaseChangeMap Λ sq).app M ▷ _ ≫
        _ ◁ derivedSquareUpperStarIsoInvApp (ModuleCat.{u + 1} Λ) sq.toCommSq N ≫
        rightDerivedUpperShriekTensorMap f' ((L((g)^*[ModuleCat.{u + 1} Λ])).obj M)
          ((L((g)^*[ModuleCat.{u + 1} Λ])).obj N) := by
  have := isIso_rightDerivedLowerShriekBaseChangeMap Λ sq
  have hlib := projectionMap_rightDerivedLowerShriekBaseChangeMap Λ sq
  simp only [← leftDerivedUpperStarTensorIso_hom] at hlib
  exact Adjunction.projectionTensorMap_mateEquiv
    (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) f)
    (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) f')
    (fun M N ↦ ((projectionMap (ModuleCat.{u + 1} Λ) f).app M).app N)
    (fun M N ↦ ((projectionMap (ModuleCat.{u + 1} Λ) f').app M).app N)
    (projectionMap_app_app_naturality_left f')
    (fun M M' ↦ (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) g' M M').hom)
    (fun N N' ↦ (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) g N N').hom)
    (fun φ N'' ↦ leftDerivedUpperStarTensorIso_hom_naturality_left g φ N'')
    (fun N ↦ derivedSquareUpperStarIsoInvApp (ModuleCat.{u + 1} Λ) sq.toCommSq N)
    (rightDerivedLowerShriekBaseChangeMap Λ sq) (inv (rightDerivedLowerShriekBaseChangeMap Λ sq))
    (fun M ↦ by simp [NatIso.isIso_inv_app]) hlib M N

/-- Blueprint `det-sf-cohsm-base-change`: Base change for the exceptional inverse image of a
smooth morphism.

Let `f : X ⟶ Y` be smooth of pure relative dimension `d`, admitting a compactification, with the
exponent of `Λ` invertible on `X`, and let `g' ≫ f = f' ≫ g` be a cartesian square with `f'`
quasi-compact. Then:
1. the canonical base change map `β : Lg'^* Rf^! ⟶ Rf'^! Lg^*`
   (`AlgebraicGeometry.Etale.rightDerivedUpperShriekBaseChangeMap`, the transpose of the inverse
   compact-support base change followed by the pulled back counit) is an isomorphism; in
   particular `β_Λ : Lg'^* ω_f ≅ ω_{f'}`;
2. for every `N`, the square formed by `Lg'^*` of the tensor map `ω_f ⊗ᴸ Lf^* N ⟶ Rf^! N`, the
   tensor map of `f'` at `Lg^* N`, `β_N` and `β_Λ ⊗ 1` (through `Lg'^* Lf^* N ≅ Lf'^* Lg^* N`)
   commutes. The tensor maps are written as
   `AlgebraicGeometry.Etale.rightDerivedUpperShriekTensorMap`
   at `(Λ_Y, N)`, of which the canonical tensor map is the composite with the left unitor.

The blueprint asks `g` to be of finite type; what is used is that the base change `f'` is
quasi-compact and admits a compactification. Clause 1 is smooth base change for `R^!`
(`AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekBaseChangeMap_of_smoothOfRelativeDimension`,
`prop-asd-smooth-base-change`), clause 2 is
`AlgebraicGeometry.Etale.leftDerivedUpperStar_map_rightDerivedUpperShriekTensorMap`. -/
theorem isIso_rightDerivedUpperShriekBaseChangeMap_and_tensorMap (d : ℕ)
    [SmoothOfRelativeDimension d f] [HasInvertibleExponent Λ X] :
    IsIso (rightDerivedUpperShriekBaseChangeMap Λ sq) ∧
      ∀ N : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
        (L((g')^*[ModuleCat.{u + 1} Λ])).map (rightDerivedUpperShriekTensorMap f (𝟙_ _) N) ≫
            (rightDerivedUpperShriekBaseChangeMap Λ sq).app (𝟙_ _ ⊗ N) ≫
            (R(f')^![ModuleCat.{u + 1} Λ]).map (leftDerivedUpperStarTensorIso _ g (𝟙_ _) N).hom =
          (leftDerivedUpperStarTensorIso _ g' _ _).hom ≫
            (rightDerivedUpperShriekBaseChangeMap Λ sq).app (𝟙_ _) ▷ _ ≫
            _ ◁ derivedSquareUpperStarIsoInvApp (ModuleCat.{u + 1} Λ) sq.toCommSq N ≫
            rightDerivedUpperShriekTensorMap f' ((L((g)^*[ModuleCat.{u + 1} Λ])).obj (𝟙_ _))
              ((L((g)^*[ModuleCat.{u + 1} Λ])).obj N) :=
  ⟨isIso_rightDerivedUpperShriekBaseChangeMap_of_smoothOfRelativeDimension Λ f d sq,
    fun N ↦ leftDerivedUpperStar_map_rightDerivedUpperShriekTensorMap sq (𝟙_ _) N⟩

/-- **Base change of the tensor maps.** For a cartesian square `g' ≫ f = f' ≫ g` with
quasi-compact `f'` whose base change map `β : Lg'^* Rf^! ⟶ Rf'^! Lg^*` is an isomorphism, and a
functor `Φ` out of `D(X'_ét, Λ)`: if `Φ` of the tensor map `θ_{f', Lg^* N}` is an isomorphism,
then so is `Φ (Lg'^* θ_{f, N})`. For `Φ = 𝟭`: `Lg'^* θ_{f, N}` is an isomorphism as soon as
`θ_{f', Lg^* N}` is one. -/
theorem isIso_map_leftDerivedUpperStar_map_dualizingComplexTensorMap_of_isPullback
    [IsIso (rightDerivedUpperShriekBaseChangeMap Λ sq)] {D : Type*} [Category* D]
    (Φ : _root_.DerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤ D)
    (N : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (h : IsIso (Φ.map (dualizingComplexTensorMap Λ f' ((L((g)^*[ModuleCat.{u + 1} Λ])).obj N)))) :
    IsIso (Φ.map ((L((g')^*[ModuleCat.{u + 1} Λ])).map (dualizingComplexTensorMap Λ f N))) := by
  have key := Φ.congr_map (leftDerivedUpperStar_map_rightDerivedUpperShriekTensorMap sq (𝟙_ _) N)
  have : IsIso (Φ.map (rightDerivedUpperShriekTensorMap f' (𝟙_ _)
      ((L((g)^*[ModuleCat.{u + 1} Λ])).obj N))) := by
    change IsIso (Φ.map (dualizingComplexTensorMapOfIsIso f' _)) at h
    rw [dualizingComplexTensorMapOfIsIso_eq, Φ.map_comp] at h
    exact IsIso.of_isIso_comp_right _ (Φ.map ((R(f')^![ModuleCat.{u + 1} Λ]).map (λ_ _).hom))
  have hn := Φ.congr_map (Adjunction.projectionTensorMap_naturality_left
    (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) f') _
    (projectionMap_app_app_naturality_left f')
    (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} Λ) g).hom
    ((L((g)^*[ModuleCat.{u + 1} Λ])).obj N))
  simp only [Functor.map_comp] at hn
  have : IsIso (Φ.map (rightDerivedUpperShriekTensorMap f'
      ((L((g)^*[ModuleCat.{u + 1} Λ])).obj (𝟙_ _)) ((L((g)^*[ModuleCat.{u + 1} Λ])).obj N))) := by
    have : IsIso (Φ.map (rightDerivedUpperShriekTensorMap f'
        ((L((g)^*[ModuleCat.{u + 1} Λ])).obj (𝟙_ _)) ((L((g)^*[ModuleCat.{u + 1} Λ])).obj N)) ≫
        Φ.map ((R(f')^![ModuleCat.{u + 1} Λ]).map
          ((leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} Λ) g).hom ▷ _))) := by
      erw [← hn]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (Φ.map ((R(f')^![ModuleCat.{u + 1} Λ]).map
      ((leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} Λ) g).hom ▷ _)))
  have : ∀ N, IsIso (derivedSquareUpperStarIsoInvApp (ModuleCat.{u + 1} Λ) sq.toCommSq N) :=
    fun N ↦ by
      unfold derivedSquareUpperStarIsoInvApp
      infer_instance
  simp only [Functor.map_comp] at key
  have h₂ : IsIso (Φ.map ((L((g')^*[ModuleCat.{u + 1} Λ])).map
      (rightDerivedUpperShriekTensorMap f (𝟙_ _) N)) ≫
        Φ.map ((rightDerivedUpperShriekBaseChangeMap Λ sq).app (𝟙_ _ ⊗ N)) ≫
        Φ.map ((R(f')^![ModuleCat.{u + 1} Λ]).map
          (leftDerivedUpperStarTensorIso _ g (𝟙_ _) N).hom)) := by
    rw [key]
    infer_instance
  rw [← Category.assoc, isIso_comp_right_iff, isIso_comp_right_iff] at h₂
  change IsIso (Φ.map ((L((g')^*[ModuleCat.{u + 1} Λ])).map
    (dualizingComplexTensorMapOfIsIso f N)))
  rw [dualizingComplexTensorMapOfIsIso_eq, Functor.map_comp, Φ.map_comp]
  infer_instance

/-- The base change map of the dualizing complexes is an isomorphism when the base change map
of `R^!` is. -/
noncomputable def dualizingComplexBaseChangeIso
    [IsIso (rightDerivedUpperShriekBaseChangeMap Λ sq)] :
    (L((g')^*[ModuleCat.{u + 1} Λ])).obj (dualizingComplex (ModuleCat.{u + 1} Λ) f) ≅
      dualizingComplex (ModuleCat.{u + 1} Λ) f' :=
  have := (isIso_dualizingComplexBaseChangeMap_iff Λ sq).2 inferInstance
  asIso (dualizingComplexBaseChangeMap Λ sq)

end BaseChange

section Etale

-- As in the section `BaseChange`: the base change lemmas are stated with these instances.
attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint ModuleCat.hasColimitsOfShape
  ModuleCat.hasColimitsOfSize

/-- **Smooth duality for open immersions.** For an open immersion `j : U ⟶ X`, with the exponent
of `Λ` invertible on `U`, the canonical tensor map `θ_{j,K}` is an isomorphism for every `K`. The
square `𝟙 ≫ j = 𝟙 ≫ j` is cartesian, its base change map is an isomorphism
(`prop-asd-smooth-base-change`), and the tensor map of `𝟙_U` is an isomorphism. -/
theorem isIso_dualizingComplexTensorMap_of_isOpenImmersion {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] [HasCompactification j] [HasInvertibleExponent Λ U]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso (dualizingComplexTensorMap Λ j K) := by
  have sq : IsPullback (𝟙 U) (𝟙 U) j j := IsKernelPair.id_of_mono j
  have := isIso_rightDerivedUpperShriekBaseChangeMap_of_smoothOfRelativeDimension Λ j 0 sq
  have h := isIso_map_leftDerivedUpperStar_map_dualizingComplexTensorMap_of_isPullback sq
    (𝟭 _) K (isIso_dualizingComplexTensorMap_id Λ U _)
  exact (NatIso.isIso_map_iff (leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) U) _).1 h

/-- For an open immersion `j : U ⟶ X`, with the exponent of `Λ` invertible on `U`, the dualizing
complex is trivial: `ω_j ≅ L(𝟙_U)^* ω_j ≅ ω_{𝟙_U} ≅ Λ_U`. -/
theorem nonempty_dualizingComplex_iso_of_isOpenImmersion {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] [HasCompactification j] [HasInvertibleExponent Λ U] :
    Nonempty (dualizingComplex (ModuleCat.{u + 1} Λ) j ≅ 𝟙_ _) := by
  have sq : IsPullback (𝟙 U) (𝟙 U) j j := IsKernelPair.id_of_mono j
  have := isIso_rightDerivedUpperShriekBaseChangeMap_of_smoothOfRelativeDimension Λ j 0 sq
  exact ⟨(leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) U).symm.app _ ≪≫
    dualizingComplexBaseChangeIso sq ≪≫ (nonempty_dualizingComplex_id_iso Λ U).some⟩

/-- The dualizing complex of an open immersion `j`, with the exponent of `Λ` invertible on its
source, is invertible. -/
lemma isInvertible_dualizingComplex_of_isOpenImmersion {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] [HasCompactification j] [HasInvertibleExponent Λ U] :
    DerivedCategory.isInvertible Λ U (dualizingComplex (ModuleCat.{u + 1} Λ) j) :=
  .of_iso (nonempty_dualizingComplex_iso_of_isOpenImmersion j).some.symm
    (DerivedCategory.isInvertible_unit Λ U)

/-- The diagonal step of smooth duality for étale morphisms, before pullback: for a
quasi-compact étale `e : V ⟶ W`, with the exponent of `Λ` invertible on `V`, the tensor maps of
the second projection `pr₂ : V ×_W V ⟶ V` become isomorphisms after `RΔ^!` along the diagonal
`Δ`, an open immersion with `Δ ≫ pr₂ = 𝟙_V`. -/
theorem isIso_rightDerivedUpperShriek_diagonal_map_dualizingComplexTensorMap_snd
    {V W : Scheme.{u}} (e : V ⟶ W) [_root_.AlgebraicGeometry.Etale e] [QuasiCompact e]
    [HasCompactification e] [HasCompactification (pullback.diagonal e)]
    [HasInvertibleExponent Λ V]
    (P : _root_.DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso ((R(pullback.diagonal e)^![ModuleCat.{u + 1} Λ]).map
      (dualizingComplexTensorMap Λ (pullback.snd e e) P)) := by
  obtain ⟨E, hPF, -⟩ := exists_rightDerivedLowerShriekCompIso Λ
  exact isIso_map_dualizingComplexTensorMapOfIsIso_of_comp (pullback.diagonal e)
    (pullback.snd e e) (𝟙 V) (pullback.diagonal_snd e) (E _ _ _ (pullback.diagonal_snd e))
    (hPF _ _ _ (pullback.diagonal_snd e))
    (projectionMapAssociativity Λ (pullback.diagonal e))
    (isIso_dualizingComplexTensorMap_of_isOpenImmersion (pullback.diagonal e)) P
    (isIso_dualizingComplexTensorMap_id Λ V P)

/-- The diagonal step of smooth duality for étale morphisms: for a quasi-compact étale
`e : V ⟶ W`, with the exponent of `Λ` invertible on `V`, the tensor maps of the second
projection `pr₂ : V ×_W V ⟶ V` become isomorphisms after pullback along the diagonal `Δ`, an open
immersion with `Δ ≫ pr₂ = 𝟙_V`. -/
theorem isIso_leftDerivedUpperStar_diagonal_map_dualizingComplexTensorMap_snd {V W : Scheme.{u}}
    (e : V ⟶ W) [_root_.AlgebraicGeometry.Etale e] [QuasiCompact e] [HasCompactification e]
    [HasInvertibleExponent Λ V]
    (P : _root_.DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso ((L((pullback.diagonal e)^*[ModuleCat.{u + 1} Λ])).map
      (dualizingComplexTensorMap Λ (pullback.snd e e) P)) := by
  have : HasCompactification (pullback.diagonal e) :=
    (Compactification.ofIsOpenImmersion _).hasCompactification
  exact isIso_leftDerivedUpperStar_map_of_isIso_rightDerivedUpperShriek_map
    (pullback.diagonal e) (isIso_dualizingComplexTensorMap_of_isOpenImmersion (pullback.diagonal e))
    ((isInvertible_iff_exists_derivedTensor _).2
      (isInvertible_dualizingComplex_of_isOpenImmersion (pullback.diagonal e))) _
    (isIso_rightDerivedUpperShriek_diagonal_map_dualizingComplexTensorMap_snd e P)

/-- **Smooth duality for étale morphisms.** For a quasi-compact étale morphism `e : V ⟶ W`
admitting a compactification, with the exponent of `Λ` invertible on `V`, the canonical tensor
map `θ_{e,K}` is an isomorphism for every `K`.

The base change of `e` along itself, `pr₂ : V ×_W V ⟶ V`, has the diagonal `Δ` as a section,
which is an open immersion. The base change map of `R^!` along this square is an isomorphism
(`prop-asd-smooth-base-change`) and respects the tensor maps, so `LΔ^* Lpr₁^* θ_{e,K}` is an
isomorphism as soon as `LΔ^* θ_{pr₂, Le^* K}` is one; and `θ_{pr₂}` pulled back along `Δ` is
determined by the tensor map of `Δ ≫ pr₂ = 𝟙_V`, an isomorphism. -/
theorem isIso_dualizingComplexTensorMap_of_etale {V W : Scheme.{u}} (e : V ⟶ W)
    [_root_.AlgebraicGeometry.Etale e] [QuasiCompact e] [HasCompactification e]
    [HasInvertibleExponent Λ V]
    (K : _root_.DerivedCategory (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso (dualizingComplexTensorMap Λ e K) := by
  have sq := IsPullback.of_hasPullback e e
  have := isIso_rightDerivedUpperShriekBaseChangeMap_of_smoothOfRelativeDimension Λ e 0 sq
  -- the object `Le^* K` is left to unification, so that it is the one of the base change lemma
  have h₃ := isIso_map_leftDerivedUpperStar_map_dualizingComplexTensorMap_of_isPullback sq
    (L((pullback.diagonal e)^*[ModuleCat.{u + 1} Λ])) K
    (isIso_leftDerivedUpperStar_diagonal_map_dualizingComplexTensorMap_snd e _)
  exact (NatIso.isIso_map_iff ((leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) V).symm ≪≫
    leftDerivedUpperStarComp _ (pullback.diagonal e) (pullback.fst e e) (𝟙 V)
      (pullback.diagonal_fst e).symm) _).2 h₃

/-- For an étale morphism `e : V ⟶ W` admitting a compactification, with the exponent of `Λ`
invertible on `V`, the dualizing complex is trivial:
`ω_e ≅ LΔ^* Lpr₁^* ω_e ≅ LΔ^* ω_{pr₂} ≅ ω_{Δ ≫ pr₂} = ω_{𝟙_V} ≅ Λ_V`, through the base change
isomorphism of `R^!` (`prop-asd-smooth-base-change`) for the square of `e` along itself. -/
theorem nonempty_dualizingComplex_iso_of_etale {V W : Scheme.{u}} (e : V ⟶ W)
    [_root_.AlgebraicGeometry.Etale e] [HasCompactification e] [HasInvertibleExponent Λ V] :
    Nonempty (dualizingComplex (ModuleCat.{u + 1} Λ) e ≅ 𝟙_ _) := by
  have sq := IsPullback.of_hasPullback e e
  obtain ⟨b⟩ := nonempty_iso_rightDerivedUpperShriek_comp_leftDerivedUpperStar Λ e 0 sq
  have : HasCompactification (pullback.diagonal e) :=
    (Compactification.ofIsOpenImmersion _).hasCompactification
  obtain ⟨c⟩ := nonempty_dualizingComplex_comp_iso_leftDerivedUpperStar Λ (pullback.diagonal e)
    (pullback.snd e e) (𝟙 V) (pullback.diagonal_snd e)
    (isIso_dualizingComplexTensorMap_of_isOpenImmersion _ _)
    (nonempty_dualizingComplex_iso_of_isOpenImmersion _)
  exact ⟨(leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) V).symm.app _ ≪≫
    (leftDerivedUpperStarComp _ (pullback.diagonal e) (pullback.fst e e) (𝟙 V)
      (pullback.diagonal_fst e).symm).app _ ≪≫
    (L((pullback.diagonal e)^*[ModuleCat.{u + 1} Λ])).mapIso (b.app (𝟙_ _) ≪≫
      (R(pullback.snd e e)^![ModuleCat.{u + 1} Λ]).mapIso
        (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} Λ) e)) ≪≫
    c.symm ≪≫ (nonempty_dualizingComplex_id_iso Λ V).some⟩

end Etale

end Etale

end AlgebraicGeometry
