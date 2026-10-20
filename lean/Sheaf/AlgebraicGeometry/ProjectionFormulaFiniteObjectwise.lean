/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjectionBaseChange
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
import WeilConjectures.AlgebraicGeometry.Sites.DerivedStalk
import Sheaf.AlgebraicGeometry.ProjectionFormulaFiniteGeometricPoint

/-! An objectwise split of the finite proper projection formula.

Source: Stacks Project, Tag 0F0G, Lemma 59.96.6.
(blueprint: lem-etale-proper-projection-formula-finite-objectwise)

The unbounded proper projection formula is checked on arbitrary objects of the two derived
categories. The geometric-stalk proof of Tag 0F0G applies to the finite coefficient ring and
identifies the canonical map with the corresponding fibre projection map; finite cohomological
dimension of proper geometric fibres makes that fibre map invertible. This objectwise result is
the component needed to assemble the natural isomorphism in the parent module.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ]

private lemma isIso_of_geometricPullbacks {Y : Scheme.{u}}
    {K L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (φ : K ⟶ L)
    (h : ∀ y : Y, IsIso (D(((Y.algClosurePoint y))^*[ModuleCat.{u + 1} Λ]).map φ)) :
    IsIso φ := by
  apply (Y.isIso_iff_isIso_sheafFiber_map_homologyFunctor_map φ).2
  intro n y
  let s := Y.algClosurePoint y
  have : IsIso (D((s)^*[ModuleCat.{u + 1} Λ]).map φ) := h y
  have hp : IsIso (((s)^*[ModuleCat.{u + 1} Λ]).map
      ((_root_.DerivedCategory.homologyFunctor _ n).map φ)) :=
    (NatIso.isIso_map_iff (Functor.mapDerivedCategoryHomologyFunctorIso
      ((s)^*[ModuleCat.{u + 1} Λ]) n) φ).mpr (inferInstanceAs (IsIso
        ((_root_.DerivedCategory.homologyFunctor _ n).map
          (D((s)^*[ModuleCat.{u + 1} Λ]).map φ))))
  let e := upperStarCompUliftSheafFiberIso (ModuleCat.{u + 1} Λ) s (𝟙 _)
  have : IsIso (((s)^*[ModuleCat.{u + 1} Λ] ⋙
      ((pointSmallEtale (𝟙 _)).ulift.{u + 1}).sheafFiber).map
        ((_root_.DerivedCategory.homologyFunctor _ n).map φ)) :=
    inferInstanceAs (IsIso (((pointSmallEtale (𝟙 _)).ulift.{u + 1}).sheafFiber.map
      (((s)^*[ModuleCat.{u + 1} Λ]).map
        ((_root_.DerivedCategory.homologyFunctor _ n).map φ))))
  have ht := (NatIso.isIso_map_iff e
    ((_root_.DerivedCategory.homologyFunctor _ n).map φ)).mp this
  change IsIso (((pointSmallEtale ((𝟙 _) ≫ s)).ulift.{u + 1}).sheafFiber.map
    ((_root_.DerivedCategory.homologyFunctor _ n).map φ)) at ht
  rw [Category.id_comp] at ht
  exact ht


private lemma pullback_projection_isIso [Finite Λ]
    {X' X Y' Y : Scheme.{u}} {a : X' ⟶ X} {b : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} [IsProper f]
    (sq : IsPullback a b f g)
    (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (h : IsIso (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} Λ) b).app
      (L((a)^*[ModuleCat.{u + 1} Λ]).obj M)).app
        (L((g)^*[ModuleCat.{u + 1} Λ]).obj L))) :
    IsIso (D((g)^*[ModuleCat.{u + 1} Λ]).map
      (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} Λ) f).app M).app L)) := by
  have := isIso_derivedBaseChangeMap_of_isProper_of_isAddTorsion_ring Λ
    isAddTorsion_of_finite sq
  have H := rightDerivedLowerStarProjectionMap_derivedBaseChangeMap
    (ModuleCat.{u + 1} Λ) sq.toCommSq M L
  have : IsIso (L((g)^*[ModuleCat.{u + 1} Λ]).map
      (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} Λ) f).app M).app L) ≫
        (derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app
          (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj M).obj
            (L((f)^*[ModuleCat.{u + 1} Λ]).obj L)) ≫
        R((b)_*[ModuleCat.{u + 1} Λ]).map
          (((leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} Λ) a).app M).app
            (L((f)^*[ModuleCat.{u + 1} Λ]).obj L))) := by
    rw [H]
    infer_instance
  have hi : IsIso (L((g)^*[ModuleCat.{u + 1} Λ]).map
      (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} Λ) f).app M).app L)) :=
    IsIso.of_isIso_comp_right _
    ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app
      (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj M).obj
        (L((f)^*[ModuleCat.{u + 1} Λ]).obj L)) ≫
      R((b)_*[ModuleCat.{u + 1} Λ]).map
        (((leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} Λ) a).app M).app
          (L((f)^*[ModuleCat.{u + 1} Λ]).obj L)))
  exact (NatIso.isIso_map_iff (leftDerivedUpperStarIsoMapDerivedCategory
    (ModuleCat.{u + 1} Λ) g)
      (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} Λ) f).app M).app L)).mp hi

private lemma geometric_projection_pullback [Finite Λ]
    {Y Z : Scheme.{u}} (g : Z ⟶ Y) [IsProper g]
    (M : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    {k : Type u} [Field k] [IsAlgClosed k] (s : Spec (.of k) ⟶ Y) :
    IsIso (D((s)^*[ModuleCat.{u + 1} Λ]).map
      (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} Λ) g).app M).app L)) := by
  let a : pullback g s ⟶ Z := pullback.fst g s
  let b : pullback g s ⟶ Spec (.of k) := pullback.snd g s
  have sq : IsPullback a b g s := IsPullback.of_hasPullback g s
  have : IsProper b := inferInstanceAs (IsProper (pullback.snd g s))
  exact pullback_projection_isIso Λ (a := a) (b := b) (f := g) (g := s) sq M L
    (isIso_projection_over_geometricPoint Λ (k := k) (X := pullback g s) b
      (L((a)^*[ModuleCat.{u + 1} Λ]).obj M) (L((s)^*[ModuleCat.{u + 1} Λ]).obj L))

/-- The objectwise finite proper projection formula used to assemble the bifunctorial result.
(blueprint: lem-etale-proper-projection-formula-finite-objectwise) -/
theorem isIso_rightDerivedLowerStarProjectionMap_app_app_of_finite [Finite Λ]
    {Y Z : Scheme.{u}} (g : Z ⟶ Y) [IsProper g] [UpperStarPreservesFlat (ModuleCat.{u + 1} Λ)]
    (M : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} Λ) g).app M).app L) := by
  rename_i instFlat
  cases Subsingleton.elim instFlat (upperStarPreservesFlat_moduleCat (Λ := Λ))
  refine isIso_of_geometricPullbacks Λ
    (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} Λ) g).app M).app L) ?_
  intro y
  exact geometric_projection_pullback Λ g M L (Y.algClosurePoint y)

private lemma isIso_of_isIso_app_app {A B : Type*} [Category A] [Category B]
    {F G : A ⥤ B ⥤ B} (α : F ⟶ G)
    (h : ∀ X Y, IsIso ((α.app X).app Y)) : IsIso α := by
  let (X : A) : IsIso (α.app X) := by
    apply (NatTrans.isIso_iff_isIso_app _).2
    intro Y
    exact h X Y
  apply (NatTrans.isIso_iff_isIso_app _).2
  intro X
  exact inferInstance

/-- Assemble the objectwise finite projection isomorphisms into the bifunctorial one. -/
theorem finite_projection_iso [Finite Λ] {Y Z : Scheme.{u}} (g : Z ⟶ Y) [IsProper g] :
    IsIso (rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} Λ) g) := by
  exact isIso_of_isIso_app_app (rightDerivedLowerStarProjectionMap
      (ModuleCat.{u + 1} Λ) g)
    (fun M L => isIso_rightDerivedLowerStarProjectionMap_app_app_of_finite Λ g M L)

end AlgebraicGeometry.Etale

