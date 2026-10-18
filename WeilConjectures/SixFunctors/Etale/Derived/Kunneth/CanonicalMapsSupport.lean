/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.CounitIso
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.ExceptionalComp
public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMapsCoherence

/-!

# The canonical maps of `Rf^!` along closed and open immersions

For a closed immersion `i : Z ⟶ X` with open complement `j : U ⟶ X`, the canonical maps of the
exceptional inverse image `Ri^!` — the base change map `Lg'^* Ri^! ⟶ Ri'^! Lg^*` and the tensor
map `Ri^! C ⊗ᴸ Li^* B ⟶ Ri^!(C ⊗ᴸ B)` — are recognised through the supported localization
triangle `Ri_* Ri^! C ⟶ C ⟶ Rj_* Lj^* C ⟶` (`sk-prop-sf-localization`): their transposes along
`Ri_! ⊣ Ri^!` are the first maps of the image of this triangle under `Lg^*`, resp. `- ⊗ᴸ B`, so
they are isomorphisms as soon as the third vertex of the image triangle is still of the form
`Rj'_* E` (`CategoryTheory.Pretriangulated.isIso_of_comp_counit_eq_of_subsingleton`). In the
applications the latter is the ordinary Künneth formula with an identity factor
(`sk-lem-sf-kunneth-star`).

For an open immersion `j` the tensor map `Rj^! C ⊗ᴸ Lj^* B ⟶ Rj^!(C ⊗ᴸ B)` is always an
isomorphism, by the same argument applied to the open–closed triangle
`Rj_! Rj^! C ⟶ C ⟶ Ri_* Li^* C ⟶` (`sk-prop-sf-open-closed-triangle`).

Finally, a morphism in `D(X_ét)` is an isomorphism if it is so after `Ri^!` and after `Lj^*`.

## Main statements

- `AlgebraicGeometry.Etale.isIso_of_isIso_rightDerivedUpperShriek_map_of_isIso_map`
- `AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekBaseChangeMap_app_of_isClosedImmersion`
- `AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekTensorMap_of_isClosedImmersion`
- `AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekTensorMap_of_isOpenImmersion`
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Pretriangulated

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- The left adjoint `Ri_!` of `Ri^!` is fully faithful for a closed immersion `i`
(`sk-prop-sf-closed-unit`). -/
noncomputable def rightDerivedLowerShriekFullyFaithfulOfIsClosedImmersion {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] : (R(i)_![ModuleCat.{u + 1} Λ]).FullyFaithful :=
  have := fun Y ↦ isIso_rightDerivedUpperShriekAdjunction_unit_app (ModuleCat.{u + 1} Λ) i Y
  have : IsIso (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) i).unit :=
    NatIso.isIso_of_isIso_app _
  (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) i).fullyFaithfulLOfIsIsoUnit

/-- **Open–closed detection of isomorphisms.** For a closed immersion `i` with open complement
`j`, a morphism `φ` of `D(X_ét, Λ)` is an isomorphism as soon as `Ri^! φ` and `Lj^* φ` are: the
supported localization triangles of the source and target are related by
`(Ri_* Ri^! φ, φ, Rj_* Lj^* φ)` (`sk-prop-sf-localization`). -/
theorem isIso_of_isIso_rightDerivedUpperShriek_map_of_isIso_map {X Z U : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    {L L' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (φ : L ⟶ L') (h₁ : IsIso ((R(i)^![ModuleCat.{u + 1} Λ]).map φ))
    (h₃ : IsIso ((L((j)^*[ModuleCat.{u + 1} Λ])).map φ)) : IsIso φ := by
  obtain ⟨τ, hτ₁, hτ₂, hτ₃⟩ := exists_triangleHom_supportedLocalization (ModuleCat.{u + 1} Λ)
    i j (by rw [hij]; exact disjoint_compl_left) φ
    (supportedLocalizationTriangle_mem_distTriang _ i j hij L)
    (supportedLocalizationTriangle_mem_distTriang _ i j hij L')
  have : IsIso τ.hom₁ := by rw [hτ₁]; infer_instance
  have : IsIso τ.hom₃ := by rw [hτ₃]; infer_instance
  have := isIso₂_of_isIso₁₃ τ (supportedLocalizationTriangle_mem_distTriang _ i j hij L)
    (supportedLocalizationTriangle_mem_distTriang _ i j hij L') inferInstance inferInstance
  rwa [hτ₂] at this

/-- **Base change of `Ri^!` along a closed immersion.** Let `i' : Z' ⟶ X'` be the base change of
a closed immersion `i : Z ⟶ X` along `g : X' ⟶ X`, `j` the open complement of `i` and `j'` an
open immersion disjoint from `i'`. If `Lg^* Rj_* Lj^* C` is of the form `Rj'_* E`, then the base
change map `Lg'^* Ri^! C ⟶ Ri'^! Lg^* C` is an isomorphism: its transpose along `Ri'_! ⊣ Ri'^!`
is, up to compact-support base change, `Lg^*` of the counit `Ri_! Ri^! C ⟶ C`, the first map of
the image under `Lg^*` of the supported localization triangle of `C`. -/
theorem isIso_rightDerivedUpperShriekBaseChangeMap_app_of_isClosedImmersion
    {X Z X' Z' U U' : Scheme.{u}} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X' ⟶ X} {g' : Z' ⟶ Z}
    (sq : IsPullback g' i' i g) [IsClosedImmersion i] [IsClosedImmersion i']
    (j : U ⟶ X) [IsOpenImmersion j] (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (j' : U' ⟶ X') [IsOpenImmersion j'] (hij' : Disjoint (Set.range i'.base) (Set.range j'.base))
    (C : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hC : ∃ E : _root_.DerivedCategory (Sheaf U'.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      Nonempty ((L((g)^*[ModuleCat.{u + 1} Λ])).obj ((R((j)_*[ModuleCat.{u + 1} Λ])).obj
        ((L((j)^*[ModuleCat.{u + 1} Λ])).obj C)) ≅ (R((j')_*[ModuleCat.{u + 1} Λ])).obj E)) :
    IsIso ((rightDerivedUpperShriekBaseChangeMap Λ sq).app C) := by
  obtain ⟨E, ⟨eE⟩⟩ := hC
  have hT := (L((g)^*[ModuleCat.{u + 1} Λ])).map_distinguished _
    (supportedLocalizationTriangle_mem_distTriang _ i j hij C)
  have := isIso_rightDerivedLowerShriekBaseChangeMap Λ sq
  refine isIso_of_comp_counit_eq_of_subsingleton
    (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) i')
    (rightDerivedLowerShriekFullyFaithfulOfIsClosedImmersion Λ i') hT (fun M n ↦ ?_)
    (asIso ((rightDerivedLowerShriekBaseChangeMap Λ sq).app _)).symm _ ?_
  · have := subsingleton_hom_shift_rightDerivedLowerShriek_rightDerivedLowerStar
      (ModuleCat.{u + 1} Λ) i' j' hij' M E n
    exact @Equiv.subsingleton _ _ ((Iso.refl _).homCongr eE) this
  · have h := mateEquiv_counit (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) i)
      (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) i')
      (inv (rightDerivedLowerShriekBaseChangeMap Λ sq)) C
    simp only [NatIso.isIso_inv_app] at h
    exact h

/-- **The tensor map of `Ri^!` for a closed immersion.** Let `i` be a closed immersion with open
complement `j`. If `Rj_* Lj^* C ⊗ᴸ B` is of the form `Rj_* E`, then the tensor map
`Ri^! C ⊗ᴸ Li^* B ⟶ Ri^!(C ⊗ᴸ B)` is an isomorphism: its transpose along `Ri_! ⊣ Ri^!` is, up to
the projection formula, the counit `Ri_! Ri^! C ⟶ C` tensored with `B`, the first map of the
image under `- ⊗ᴸ B` of the supported localization triangle of `C`. -/
theorem isIso_rightDerivedUpperShriekTensorMap_of_isClosedImmersion {X Z U : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (C B : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hC : ∃ E : _root_.DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      Nonempty (((derivedTensor (ModuleCat.{u + 1} Λ) X).obj ((R((j)_*[ModuleCat.{u + 1} Λ])).obj
        ((L((j)^*[ModuleCat.{u + 1} Λ])).obj C))).obj B ≅
          (R((j)_*[ModuleCat.{u + 1} Λ])).obj E)) :
    IsIso (rightDerivedUpperShriekTensorMap i C B) := by
  obtain ⟨E, ⟨eE⟩⟩ := hC
  have hT := ((derivedTensor (ModuleCat.{u + 1} Λ) X).flip.obj B).map_distinguished _
    (supportedLocalizationTriangle_mem_distTriang _ i j hij C)
  refine isIso_of_comp_counit_eq_of_subsingleton
    (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) i)
    (rightDerivedLowerShriekFullyFaithfulOfIsClosedImmersion Λ i) hT (fun M n ↦ ?_)
    (asIso (((projectionMap (ModuleCat.{u + 1} Λ) i).app _).app B)).symm _ ?_
  · have := subsingleton_hom_shift_rightDerivedLowerShriek_rightDerivedLowerStar
      (ModuleCat.{u + 1} Λ) i j (by rw [hij]; exact disjoint_compl_left) M E n
    exact @Equiv.subsingleton _ _ ((Iso.refl _).homCongr eE) this
  · exact Adjunction.map_projectionTensorMap_comp_counit _ _ _ _

section OpenImmersion

variable {X Z U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] [HasCompactification j]
  [QuasiCompact j] (i : Z ⟶ X) [IsClosedImmersion i]

/-- For a quasi-compact open immersion `j`, the left adjoint `Rj_! ≅ D(j_!)` of `Rj^!` is fully
faithful. -/
noncomputable def rightDerivedLowerShriekFullyFaithfulOfIsOpenImmersion :
    (R(j)_![ModuleCat.{u + 1} Λ]).FullyFaithful :=
  Functor.FullyFaithful.ofIso
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j).fullyFaithfulLOfIsIsoUnit
    (rightDerivedLowerShriekIsoOfIsOpenImmersion Λ j).symm

/-- Objects supported on the closed complement of `j` receive no maps from objects `Rj_! M`. -/
lemma subsingleton_hom_shift_rightDerivedLowerShriek_rightDerivedLowerStar_of_isOpenImmersion
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (M : _root_.DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (n : ℤ)
    (F : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Subsingleton (((R(j)_![ModuleCat.{u + 1} Λ]).obj M)⟦n⟧ ⟶
      (R((i)_*[ModuleCat.{u + 1} Λ])).obj F) := by
  have hz : IsZero (D((i)^*[ModuleCat.{u + 1} Λ]).obj (((R(j)_![ModuleCat.{u + 1} Λ]).obj M)⟦n⟧)) :=
    ((shiftFunctor _ n).map_isZero
      ((isZero_mapDerivedCategoryUpperStar_obj_openImmersionLowerShriek_of_disjoint_range
        (ModuleCat.{u + 1} Λ) j i (by rw [hij]; exact disjoint_compl_left) M).of_iso
        ((D((i)^*[ModuleCat.{u + 1} Λ])).mapIso
          ((rightDerivedLowerShriekIsoOfIsOpenImmersion Λ j).app M)))).of_iso
      ((D((i)^*[ModuleCat.{u + 1} Λ]).commShiftIso n).app _)
  have : Subsingleton (D((i)^*[ModuleCat.{u + 1} Λ]).obj
      (((R(j)_![ModuleCat.{u + 1} Λ]).obj M)⟦n⟧) ⟶ F) :=
    ⟨fun _ _ ↦ hz.eq_of_src _ _⟩
  exact ((mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i).homEquiv _ _).symm.subsingleton

/-- **The tensor map of `Rj^!` for an open immersion.** For a quasi-compact open immersion `j`
with closed complement `i`, the tensor map `Rj^! C ⊗ᴸ Lj^* B ⟶ Rj^!(C ⊗ᴸ B)` is an isomorphism:
the counit `Rj_! Rj^! C ⟶ C` is the first map of the open–closed triangle
`Rj_! Rj^! C ⟶ C ⟶ Ri_* Li^* C ⟶` (`sk-prop-sf-open-closed-triangle`), and its image under
`- ⊗ᴸ B` is the transpose of the tensor map up to the projection formula; its third vertex
`Ri_* Li^* C ⊗ᴸ B ≅ Ri_*(Li^* C ⊗ᴸ Li^* B)` receives no maps from objects `Rj_! M`. -/
theorem isIso_rightDerivedUpperShriekTensorMap_of_isOpenImmersion
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (C B : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso (rightDerivedUpperShriekTensorMap j C B) := by
  have hF := rightDerivedLowerShriekFullyFaithfulOfIsOpenImmersion Λ j
  obtain ⟨w, hw⟩ := exists_distTriang_openClosed (ModuleCat.{u + 1} Λ) j i hij C
  obtain ⟨w', hw'⟩ := exists_distTriang_counit_of_subsingleton
    (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) j) hF hw
    (fun M n ↦ subsingleton_hom_shift_rightDerivedLowerShriek_rightDerivedLowerStar_of_isOpenImmersion
      Λ j i hij M n _)
    ⟨_, ⟨(rightDerivedLowerShriekIsoOfIsOpenImmersion Λ j).app _⟩⟩
  have hT := ((derivedTensor (ModuleCat.{u + 1} Λ) X).flip.obj B).map_distinguished _ hw'
  have := isIso_rightDerivedLowerStarProjectionMap_of_finite Λ i
  refine isIso_of_comp_counit_eq_of_subsingleton
    (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) j) hF hT (fun M n ↦ ?_)
    (asIso (((projectionMap (ModuleCat.{u + 1} Λ) j).app _).app B)).symm _ ?_
  · have := subsingleton_hom_shift_rightDerivedLowerShriek_rightDerivedLowerStar_of_isOpenImmersion
      Λ j i hij M n (((derivedTensor (ModuleCat.{u + 1} Λ) Z).obj
        (D((i)^*[ModuleCat.{u + 1} Λ]).obj C)).obj ((L((i)^*[ModuleCat.{u + 1} Λ])).obj B))
    exact @Equiv.subsingleton _ _ ((Iso.refl _).homCongr
      (asIso (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} Λ) i).app _).app B))) this
  · exact Adjunction.map_projectionTensorMap_comp_counit _ _ _ _

end OpenImmersion

end Etale

end AlgebraicGeometry
