/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Localization
public import WeilConjectures.SixFunctors.Etale.Derived.ShiftAdjunction
public import WeilConjectures.SixFunctors.Etale.Derived.Supports

/-!
# Base change of the supported localization triangle

Let `i : Z ⟶ X` be a closed immersion with open complement `j : V ⟶ X`, and let `e : U ⟶ X` be a
morphism, with base changes `i' : Z' ⟶ U` and `j' : V' ⟶ U`. The derived pullback `Le^*` carries
the supported localization triangle `Ri_! Ri^! L ⟶ L ⟶ Rj_* Lj^* L ⟶ [1]` of `L` to a
distinguished triangle on `U`, which maps to the supported localization triangle of `Le^* L`:
on the first term by the restriction of supports
(`AlgebraicGeometry.Etale.supportedRestriction`), on the last term by the derived base change
map `Ex_* : Le^* Rj_* ⟶ Rj'_* Le₁^*`. The compatibility with the connecting maps is the base
change of the boundary `AlgebraicGeometry.Etale.supportedLocalizationBoundary`.

## Main statements

- `AlgebraicGeometry.Etale.supportedLocalizationBoundary_baseChange`
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [HasSmallSiteSheafify A]

omit [HasSmallSiteSheafify A] in
/-- The derived pullback `Lg^*` is a triangulated functor, being isomorphic, compatibly with the
shifts, to the functor `D(g^*)` induced by the exact pullback. -/
instance isTriangulated_leftDerivedUpperStar {Z Y : Scheme.{u}} (g : Z ⟶ Y) :
    (L((g)^*[A])).IsTriangulated :=
  Functor.isTriangulated_of_iso (leftDerivedUpperStarIsoMapDerivedCategory A g).symm

variable {X U Z Z' V V' : Scheme.{u}}

/-- **Base change of the supported localization boundary.** Let `i : Z ⟶ X` be a closed
immersion with open complement `j : V ⟶ X`, `e : U ⟶ X` a morphism, `i' : Z' ⟶ U` the base
change of `i` with open complement `j' : V' ⟶ U`, and `e₁ : V' ⟶ V` with `e₁ ≫ j = j' ≫ e`. For
`L ∈ D(X_ét)` and an identification `τ : Le^* L ≅ L'`, the boundaries `δ_L` and `δ_{L'}` of the
supported localization triangles are compatible with the restriction of supports
`ψ = AlgebraicGeometry.Etale.supportedRestriction` and the derived base change map `Ex_*`:

```
  Le^* Rj_* Lj^* L ──Le^* δ_L──▶ Le^* ((Ri_! Ri^! L)[1]) ≅ (Le^* Ri_! Ri^! L)[1]
        │                                                      │
  Ex_*, τ                                                    ψ[1]
        ▼                                                      ▼
  Rj'_* Lj'^* L' ─────────────δ_{L'}──────────────▶ (Ri'_! Ri'^! L')[1]
```

The pulled back triangle is distinguished and its first term is supported on `Z'`, so the middle
map `τ` extends uniquely to a morphism of triangles towards the supported localization triangle
of `L'` [BBD, 1.1.9]; its outer components are `ψ` and the base change map, both characterized
by the commutation of the adjacent squares. -/
theorem supportedLocalizationBoundary_baseChange (e : U ⟶ X) (i : Z ⟶ X) (j : V ⟶ X)
    (i' : Z' ⟶ U) (j' : V' ⟶ U) (g : Z' ⟶ Z) (e₁ : V' ⟶ V)
    [IsClosedImmersion i] [(R(i)_![A]).IsLeftAdjoint] [IsOpenImmersion j]
    [IsClosedImmersion i'] [(R(i')_![A]).IsLeftAdjoint] [IsOpenImmersion j']
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (hij' : Set.range i'.base = (Set.range j'.base)ᶜ)
    (hg : IsPullback g i' i e) (sq : CommSq e₁ j' j e)
    (L : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (L' : DerivedCategory (Sheaf U.smallEtaleTopology A)) (τ : (L((e)^*[A])).obj L ≅ L') :
    (L((e)^*[A])).map (supportedLocalizationBoundary A i j hij L) ≫
        ((L((e)^*[A])).commShiftIso (1 : ℤ)).hom.app _ ≫
          (supportedRestriction A e i i' g hg L L' τ)⟦(1 : ℤ)⟧' =
      (derivedBaseChangeMap A sq).app _ ≫
        (R((j')_*[A])).map ((derivedSquareUpperStarIso A sq).inv.app L ≫
          (L((j')^*[A])).map τ.hom) ≫
          supportedLocalizationBoundary A i' j' hij' L' := by
  set T₁ := (L((e)^*[A])).mapTriangle.obj
    (supportedLocalizationTriangle A i j L (supportedLocalizationBoundary A i j hij L))
  have hT₁ : T₁ ∈ distTriang _ :=
    (L((e)^*[A])).map_distinguished _ (supportedLocalizationTriangle_mem_distTriang A i j hij L)
  have hT₂ := supportedLocalizationTriangle_mem_distTriang A i' j' hij' L'
  -- the pulled back supported term vanishes on `V'`
  have hz : IsZero ((L((j')^*[A])).obj T₁.obj₁) :=
    (isZero_leftDerivedUpperStar_obj_rightDerivedLowerShriek_of_disjoint A i j
      (by rw [hij]; exact disjoint_compl_left) (j' ≫ e)
      (by rintro _ ⟨x, rfl⟩; exact ⟨e₁ x, by rw [← sq.w]; simp⟩) _).of_iso
        ((leftDerivedUpperStarComp A j' e).app _).symm
  have hz₁ (n : ℤ) : IsZero ((L((j')^*[A])).obj (T₁.obj₁⟦n⟧)) :=
    ((shiftFunctor _ n).map_isZero hz).of_iso (((L((j')^*[A])).commShiftIso n).app _)
  have : Subsingleton (T₁.obj₁⟦(1 : ℤ)⟧ ⟶ (supportedLocalizationTriangle A i' j' L'
      (supportedLocalizationBoundary A i' j' hij' L')).obj₃) :=
    subsingleton_hom_rightDerivedLowerStar_of_isZero A j' (hz₁ 1) _
  -- the middle component `τ` extends to a morphism of triangles
  obtain ⟨φ, hφ⟩ := exists_triangleHom_of_comp_eq_zero hT₁ hT₂ τ.hom
    (@Subsingleton.elim _ (subsingleton_hom_rightDerivedLowerStar_of_isZero A j' hz _) _ _)
  -- its first component is the restriction of supports
  have h₁ : φ.hom₁ = supportedRestriction A e i i' g hg L L' τ :=
    (existsUnique_supportedRestriction A e i i' g hg L L' τ).unique
      (by have h := φ.comm₁; rw [hφ] at h; exact h.symm)
      (existsUnique_supportedRestriction A e i i' g hg L L' τ).exists.choose_spec
  -- its last component is the base change map
  have h₃ : φ.hom₃ = (derivedBaseChangeMap A sq).app _ ≫
      (R((j')_*[A])).map ((derivedSquareUpperStarIso A sq).inv.app L ≫
        (L((j')^*[A])).map τ.hom) := by
    refine Triangle.cancel_mor₂_of_subsingleton hT₁ ?_
    rw [φ.comm₂, hφ]
    change τ.hom ≫ (derivedUpperStarLowerStarAdjunction A j').unit.app L' =
      (L((e)^*[A])).map ((derivedUpperStarLowerStarAdjunction A j).unit.app L) ≫ _
    erw [map_unit_derivedBaseChangeMap_app_assoc]
    simp only [Functor.id_obj, ← Functor.map_comp, Iso.hom_inv_id_app_assoc]
    exact ((derivedUpperStarLowerStarAdjunction A j').unit.naturality τ.hom)
  have h := φ.comm₃
  rw [h₁, h₃] at h
  change ((L((e)^*[A])).map _ ≫ _) ≫ _ = _ at h
  simp only [Category.assoc] at h
  exact h

end Etale

end AlgebraicGeometry
