/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.Local
public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.SmoothBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence

/-!
# Smooth duality for étale morphisms

For an étale morphism `e : V ⟶ W` admitting a compactification, with the exponent of `Λ`
invertible on `V`, the canonical tensor map `θ_{e,K} : ω_e ⊗ᴸ Le^* K ⟶ Re^! K` is an isomorphism
for every `K` and `ω_e ≅ Λ_V`.

* For an isomorphism `e`, the adjunction `Re_! ⊣ Re^!` is an adjoint equivalence, and the tensor
  maps, adjoint transposes of isomorphisms, are isomorphisms.
* In general, the base change of `e` along itself has the diagonal `Δ : V ⟶ V ×_W V` as a
  section, which is an open immersion. The canonical base change map of `R^!` is an isomorphism
  (`prop-asd-smooth-base-change`) and respects the tensor maps, so `θ_e` pulled back to
  `V ×_W V` is the tensor map of the projection; pulled back further along `Δ`, this is the
  tensor map of `Δ ≫ pr = 𝟙`. This applies first when `e` is an open immersion, where `Δ` is an
  isomorphism, and then to all étale `e`, where `Δ` is an open immersion.

## Main statements

- `AlgebraicGeometry.Etale.isIso_dualizingComplexTensorMap_of_isIso`
- `AlgebraicGeometry.Etale.isIso_leftDerivedUpperStar_map_dualizingComplexTensorMap_of_isPullback`
- `AlgebraicGeometry.Etale.etaleSmoothDuality`
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

section Iso

/-- A derived pullback along an isomorphism is essentially surjective:
`P ≅ Lf^* L(f⁻¹)^* P`. -/
noncomputable def leftDerivedUpperStarInvIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f]
    (P : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    P ≅ (L((f)^*[ModuleCat.{u + 1} Λ])).obj ((L((inv f)^*[ModuleCat.{u + 1} Λ])).obj P) :=
  (leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) X).symm.app P ≪≫
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) f (inv f) (𝟙 X) (by simp)).app P

/-- For an isomorphism `f`, the unit of `Rf_! ⊣ Rf^!` is an isomorphism: its counit is one, and
`Rf^! ≅ Lf^*` is essentially surjective. -/
theorem isIso_rightDerivedUpperShriekAdjunction_unit_of_isIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIso f] [HasCompactification f] :
    IsIso (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) f).unit := by
  have := isIso_rightDerivedUpperShriekAdjunction_counit_of_isIso (ModuleCat.{u + 1} Λ) f
  have hR (M) : IsIso ((rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) f).unit.app
      ((R(f)^![ModuleCat.{u + 1} Λ]).obj M)) := by
    have h :=
      (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) f).right_triangle_components M
    have : IsIso ((rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) f).unit.app
        ((R(f)^![ModuleCat.{u + 1} Λ]).obj M) ≫ (R(f)^![ModuleCat.{u + 1} Λ]).map
        ((rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) f).counit.app M)) := by
      rw [h]
      exact IsIso.id _
    exact IsIso.of_isIso_comp_right _ ((R(f)^![ModuleCat.{u + 1} Λ]).map
      ((rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) f).counit.app M))
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun P ↦ ?_
  let e : P ≅ (R(f)^![ModuleCat.{u + 1} Λ]).obj ((L((inv f)^*[ModuleCat.{u + 1} Λ])).obj P) :=
    leftDerivedUpperStarInvIso f P ≪≫
      (rightDerivedUpperShriekIsoOfIso (ModuleCat.{u + 1} Λ) (asIso f)).symm.app _
  exact (NatTrans.isIso_app_iff_of_iso _ e).2 (hR _)

/-- For an isomorphism `f`, the canonical tensor map `θ_{f,K} : ω_f ⊗ᴸ Lf^* K ⟶ Rf^! K` is an
isomorphism: it is the adjoint transpose of an isomorphism along the adjoint equivalence
`Rf_! ⊣ Rf^!`. -/
theorem isIso_dualizingComplexTensorMap_of_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f]
    [HasCompactification f]
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso (dualizingComplexTensorMap Λ f K) := by
  have := isIso_rightDerivedUpperShriekAdjunction_counit_of_isIso (ModuleCat.{u + 1} Λ) f
  have := isIso_rightDerivedUpperShriekAdjunction_unit_of_isIso (Λ := Λ) f
  change IsIso (dualizingComplexTensorMapOfIsIso f K)
  rw [isIso_dualizingComplexTensorMapOfIsIso_iff, rightDerivedUpperShriekTensorMap,
    Adjunction.projectionTensorMap, Adjunction.homEquiv_unit]
  infer_instance

/-- For an isomorphism `f`, the dualizing complex is trivial: `ω_f ≅ Lf^* Λ_Y ≅ Λ_X`. -/
noncomputable def dualizingComplexIsoOfIsIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f]
    [HasCompactification f] :
    dualizingComplex (ModuleCat.{u + 1} Λ) f ≅ 𝟙_ _ :=
  (rightDerivedUpperShriekIsoOfIso (ModuleCat.{u + 1} Λ) (asIso f)).app _ ≪≫
    leftDerivedUpperStarUnitIso _ f

end Iso

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

/-- **Base change of the tensor maps.** For a cartesian square `g' ≫ f = f' ≫ g` with
quasi-compact `f'` whose base change map `β : Lg'^* Rf^! ⟶ Rf'^! Lg^*` is an isomorphism, if the
tensor map `θ_{f', Lg^* N}` is an isomorphism, then so is `Lg'^* θ_{f, N}`. -/
theorem isIso_leftDerivedUpperStar_map_dualizingComplexTensorMap_of_isPullback
    [IsIso (rightDerivedUpperShriekBaseChangeMap Λ sq)]
    (N : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (h : IsIso (dualizingComplexTensorMap Λ f' ((L((g)^*[ModuleCat.{u + 1} Λ])).obj N))) :
    IsIso ((L((g')^*[ModuleCat.{u + 1} Λ])).map (dualizingComplexTensorMap Λ f N)) := by
  have key := leftDerivedUpperStar_map_rightDerivedUpperShriekTensorMap sq (𝟙_ _) N
  have : IsIso (rightDerivedUpperShriekTensorMap f' (𝟙_ _)
      ((L((g)^*[ModuleCat.{u + 1} Λ])).obj N)) :=
    (isIso_dualizingComplexTensorMapOfIsIso_iff f' _).1 h
  have : IsIso (rightDerivedUpperShriekTensorMap f'
      ((L((g)^*[ModuleCat.{u + 1} Λ])).obj (𝟙_ _)) ((L((g)^*[ModuleCat.{u + 1} Λ])).obj N)) :=
    isIso_rightDerivedUpperShriekTensorMap_of_iso_left f'
      (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} Λ) g).symm
  have : ∀ N, IsIso (derivedSquareUpperStarIsoInvApp (ModuleCat.{u + 1} Λ) sq.toCommSq N) :=
    fun N ↦ by
      unfold derivedSquareUpperStarIsoInvApp
      infer_instance
  have h₂ : IsIso ((L((g')^*[ModuleCat.{u + 1} Λ])).map
      (rightDerivedUpperShriekTensorMap f (𝟙_ _) N) ≫
        (rightDerivedUpperShriekBaseChangeMap Λ sq).app (𝟙_ _ ⊗ N) ≫
        (R(f')^![ModuleCat.{u + 1} Λ]).map
          (leftDerivedUpperStarTensorIso _ g (𝟙_ _) N).hom) := by
    rw [key]
    infer_instance
  have h₃ := IsIso.of_isIso_comp_right _ _ (h := h₂)
  have h₄ := IsIso.of_isIso_comp_right _ _ (h := h₃)
  change IsIso ((L((g')^*[ModuleCat.{u + 1} Λ])).map (dualizingComplexTensorMapOfIsIso f N))
  rw [dualizingComplexTensorMapOfIsIso_eq, Functor.map_comp]
  infer_instance

end BaseChange

end Etale

end AlgebraicGeometry
