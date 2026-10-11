/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Localization
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar
public import WeilConjectures.SixFunctors.Etale.Derived.Triangulated
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Exceptional.BaseChange

/-!
# The base change Künneth map along a closed immersion

Let `g : T ⟶ S'` be a closed immersion with open complement `j : U ⟶ S'`, and consider the
base change squares of `g` and `j` along `f' : X' ⟶ S'`, with base changes `h : Y ⟶ X'`
(a closed immersion) and `j' : U' ⟶ X'`. If the base change maps `Ku` of `lem-kun-0f1n` are
invertible for both squares, the base change Künneth map
`α : Lh^* M ⊗ᴸ Le^*(g^× L) ⟶ h^×(M ⊗ᴸ Lf'^* L)` is an isomorphism for every `L`
(`AlgebraicGeometry.Etale.isIso_exceptionalBaseChange_of_isClosedImmersion`).

This is the closed-immersion case of the exceptional Künneth formula in the blueprint proof of
`prop-trf-exceptional-kunneth`: by the supported localization triangle
`Rg_* g^× L ⟶ L ⟶ Rj_* Lj^* L ⟶` (`sk-prop-sf-localization`), the cone of
`M ⊗ᴸ Lf'^*(Rg_* g^× L ⟶ L)` is `M ⊗ᴸ Lf'^* Rj_* Lj^* L ≅ Rj'_*(…)`, which is invisible to
`h^×` because `j'^* Rh_* = 0`; and `Rh_*` is fully faithful (`sk-prop-sf-closed-unit`).

-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Pretriangulated

open scoped CategoryTheory.Functor

namespace CategoryTheory.Pretriangulated.Triangle

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- If `Hom(X, T.obj₃) = 0` and `Hom(X⟦1⟧, T.obj₃) = 0` for a distinguished triangle `T`, then
composition with `T.mor₁` is a bijection `Hom(X, T.obj₁) ≃ Hom(X, T.obj₂)`. -/
lemma bijective_comp_mor₁_of_subsingleton {T : Triangle C} (hT : T ∈ distTriang C) {X : C}
    [Subsingleton (X⟦(1 : ℤ)⟧ ⟶ T.obj₃)] [h₀ : Subsingleton (X ⟶ T.obj₃)] :
    Function.Bijective (fun x : X ⟶ T.obj₁ ↦ x ≫ T.mor₁) :=
  ⟨fun _ _ hxy ↦ Triangle.cancel_mor₁_of_subsingleton hT hxy,
    fun y ↦ (Triangle.coyoneda_exact₂ T hT y (h₀.elim _ _)).imp fun _ hx ↦ hx.symm⟩

end CategoryTheory.Pretriangulated.Triangle

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [Etale.UpperStarPreservesFlat A]

noncomputable instance {X' S' : Scheme.{u}} (f' : X' ⟶ S')
    (M : DerivedCategory (Sheaf X'.smallEtaleTopology A)) :
    (tensorPullback A f' M).CommShift ℤ :=
  inferInstanceAs ((L((f')^*[A]) ⋙ (derivedTensor A X').obj M).CommShift ℤ)

instance {X' S' : Scheme.{u}} (f' : X' ⟶ S')
    (M : DerivedCategory (Sheaf X'.smallEtaleTopology A)) :
    (tensorPullback A f' M).IsTriangulated :=
  inferInstanceAs ((L((f')^*[A]) ⋙ (derivedTensor A X').obj M).IsTriangulated)

variable [HasSmallSiteSheafify A]

section Proper

variable {X Y : Scheme.{u}} (i : X ⟶ Y) [IsProper i] [HasCompactification i]
  [(R(i)_![A]).IsLeftAdjoint] [R((i)_*[A]).IsLeftAdjoint]

/-- For a proper `i`, the right adjoint `i^×` of `Ri_*` is the exceptional inverse image `Ri^!`:
the conjugate of `Ri_! ≅ Ri_*` (`sk-prop-sf-comp-proper`). -/
noncomputable def lowerStarRightAdjointIsoRightDerivedUpperShriek :
    lowerStarRightAdjoint A i ≅ R(i)^![A] :=
  conjugateIsoEquiv (lowerStarRightAdjunction A i) (rightDerivedUpperShriekAdjunction A i)
    (rightDerivedLowerShriekIsoRightDerivedLowerStar A i)

lemma lowerStarRightAdjunction_counit_app
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    (lowerStarRightAdjunction A i).counit.app L =
      (rightDerivedLowerShriekIsoRightDerivedLowerStar A i).inv.app _ ≫
        (R(i)_![A]).map ((lowerStarRightAdjointIsoRightDerivedUpperShriek A i).hom.app L) ≫
        (rightDerivedUpperShriekAdjunction A i).counit.app L := by
  rw [lowerStarRightAdjointIsoRightDerivedUpperShriek, conjugateIsoEquiv_apply_hom,
    conjugateEquiv_counit, Iso.inv_hom_id_app_assoc]

end Proper

section ClosedImmersion

variable {X Y : Scheme.{u}} (i : X ⟶ Y) [IsClosedImmersion i] [HasCompactification i]
  [(R(i)_![A]).IsLeftAdjoint] [R((i)_*[A]).IsLeftAdjoint]

/-- For a closed immersion `i`, the pushforward `Ri_*` is fully faithful, so the unit of
`Ri_* ⊣ i^×` is an isomorphism (`sk-prop-sf-closed-unit`). -/
instance isIso_lowerStarRightAdjunction_unit : IsIso (lowerStarRightAdjunction A i).unit := by
  have := isIso_rightDerivedUpperShriekAdjunction_unit_app A i
  have : IsIso (rightDerivedUpperShriekAdjunction A i).unit := NatIso.isIso_of_isIso_app _
  have hff := (rightDerivedUpperShriekAdjunction A i).fullyFaithfulLOfIsIsoUnit
  have := hff.full
  have := hff.faithful
  have : (R((i)_*[A])).Full := Functor.Full.of_iso (rightDerivedLowerShriekIsoRightDerivedLowerStar A i)
  have : (R((i)_*[A])).Faithful :=
    Functor.Faithful.of_iso (rightDerivedLowerShriekIsoRightDerivedLowerStar A i)
  infer_instance

/-- **The localization triangle for `Ri_* ⊣ i^×`.** For a closed immersion `i` with open
complement `j`, the counit `Ri_* i^× L ⟶ L` and the unit `L ⟶ Rj_* Lj^* L` extend to a
distinguished triangle: the supported localization triangle (`sk-prop-sf-localization`),
transported along `Ri_! ≅ Ri_*`. -/
theorem exists_distTriang_lowerStarRightAdjunction_counit {U : Scheme.{u}} (j : U ⟶ Y)
    [IsOpenImmersion j] (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    ∃ w, Triangle.mk ((lowerStarRightAdjunction A i).counit.app L)
      ((derivedUpperStarLowerStarAdjunction A j).unit.app L) w ∈ distTriang _ := by
  let e : (R((i)_*[A])).obj ((lowerStarRightAdjoint A i).obj L) ≅
      (R(i)_![A]).obj ((R(i)^![A]).obj L) :=
    (rightDerivedLowerShriekIsoRightDerivedLowerStar A i).symm.app _ ≪≫
      (R(i)_![A]).mapIso ((lowerStarRightAdjointIsoRightDerivedUpperShriek A i).app L)
  refine ⟨supportedLocalizationBoundary A i j hij L ≫ e.inv⟦(1 : ℤ)⟧',
    isomorphic_distinguished _ (supportedLocalizationTriangle_mem_distTriang A i j hij L) _
      (Triangle.isoMk _ _ e (Iso.refl _) (Iso.refl _) ?_ ?_ ?_)⟩
  · simp [e, lowerStarRightAdjunction_counit_app]
  · simp
  · simp [← Functor.map_comp]

end ClosedImmersion

section Square

variable {Y X' T S' U U' : Scheme.{u}} (h : Y ⟶ X') (e : Y ⟶ T) (f' : X' ⟶ S') (g : T ⟶ S')
  (w : h ≫ f' = e ≫ g) (j : U ⟶ S') (j' : U' ⟶ X') (eU : U' ⟶ U) (wU : j' ≫ f' = eU ≫ j)
  (M : DerivedCategory (Sheaf X'.smallEtaleTopology A))
  [IsClosedImmersion g] [HasCompactification g] [(R(g)_![A]).IsLeftAdjoint]
  [R((g)_*[A]).IsLeftAdjoint]
  [IsClosedImmersion h] [HasCompactification h] [(R(h)_![A]).IsLeftAdjoint]
  [R((h)_*[A]).IsLeftAdjoint] [IsOpenImmersion j] [IsOpenImmersion j']
  [IsIso (tensorBaseChangeNatTrans A h e f' g w M)]
  [IsIso (tensorBaseChangeNatTrans A j' eU f' j wU M)]

/-- **The base change Künneth map along a closed immersion is an isomorphism**, for every `L`,
provided the base change maps `Ku` of the closed immersion `g` and of its open complement `j`
are invertible (they are for finite-type schemes over a field and torsion coefficients,
`lem-kun-0f1n`). Part of the proof of `prop-trf-exceptional-kunneth` (closed immersions). -/
theorem isIso_exceptionalBaseChange_of_isClosedImmersion
    (hgj : Set.range g.base = (Set.range j.base)ᶜ)
    (hhj : Disjoint (Set.range h.base) (Set.range j'.base))
    (L : DerivedCategory (Sheaf S'.smallEtaleTopology A)) :
    IsIso ((exceptionalBaseChange A h e f' g w M).app L) := by
  obtain ⟨δ, hδ⟩ := exists_distTriang_lowerStarRightAdjunction_counit A g j hgj L
  let E := tensorPullback A f' M
  have hE := E.map_distinguished _ hδ
  -- the third vertex receives no maps from shifts of objects supported on `Y`
  have hsub (T₀ : DerivedCategory (Sheaf Y.smallEtaleTopology A)) (n : ℤ) :
      Subsingleton (((R((h)_*[A])).obj T₀)⟦n⟧ ⟶
        E.obj ((R((j)_*[A])).obj ((L((j)^*[A])).obj L))) := by
    have := subsingleton_hom_shift_rightDerivedLowerShriek_rightDerivedLowerStar A h j' hhj T₀
      ((tensorPullback A eU (L((j')^*[A]).obj M)).obj ((L((j)^*[A])).obj L)) n
    exact (Iso.homCongr
      ((shiftFunctor _ n).mapIso ((rightDerivedLowerShriekIsoRightDerivedLowerStar A h).app T₀))
      (asIso ((tensorBaseChangeNatTrans A j' eU f' j wU M).app
        ((L((j)^*[A])).obj L))).symm).symm.subsingleton
  have hbij (T₀ : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
      Function.Bijective (fun x : (R((h)_*[A])).obj T₀ ⟶
          E.obj ((R((g)_*[A])).obj ((lowerStarRightAdjoint A g).obj L)) ↦
        x ≫ E.map ((lowerStarRightAdjunction A g).counit.app L)) := by
    have := hsub T₀ 1
    have : Subsingleton ((R((h)_*[A])).obj T₀ ⟶
        E.obj ((R((j)_*[A])).obj ((L((j)^*[A])).obj L))) :=
      have := hsub T₀ 0
      ((shiftFunctorZero _ ℤ).app _).homFromEquiv.symm.subsingleton
    exact Triangle.bijective_comp_mor₁_of_subsingleton hE
  -- hence `h^×` of `E(counit)` is an isomorphism
  have hiso : IsIso ((lowerStarRightAdjoint A h).map
      (E.map ((lowerStarRightAdjunction A g).counit.app L))) := by
    refine isIso_of_yoneda_map_bijective _ fun T₀ ↦ ?_
    have hc : (fun x : T₀ ⟶ (lowerStarRightAdjoint A h).obj
          (E.obj ((R((g)_*[A])).obj ((lowerStarRightAdjoint A g).obj L))) ↦
        x ≫ (lowerStarRightAdjoint A h).map
          (E.map ((lowerStarRightAdjunction A g).counit.app L))) =
        ((lowerStarRightAdjunction A h).homEquiv _ _) ∘
          (fun x ↦ x ≫ E.map ((lowerStarRightAdjunction A g).counit.app L)) ∘
          ((lowerStarRightAdjunction A h).homEquiv _ _).symm := by
      ext x
      simp [Adjunction.homEquiv_naturality_right_symm]
    rw [hc]
    exact ((lowerStarRightAdjunction A h).homEquiv _ _).bijective.comp
      ((hbij T₀).comp ((lowerStarRightAdjunction A h).homEquiv _ _).symm.bijective)
  have : (exceptionalBaseChange A h e f' g w M).app L =
      (lowerStarRightAdjunction A h).unit.app _ ≫
        (lowerStarRightAdjoint A h).map ((inv (tensorBaseChangeNatTrans A h e f' g w M)).app _) ≫
        (lowerStarRightAdjoint A h).map (E.map ((lowerStarRightAdjunction A g).counit.app L)) := by
    simp [exceptionalBaseChange, E]
  rw [this]
  infer_instance

end Square

end Etale

end AlgebraicGeometry
