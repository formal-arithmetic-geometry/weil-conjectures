/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.Paper.CondensedQbarComparisons
import all Sheaf.Paper.ContinuousIntegralPullComposition
import all Sheaf.Paper.ContinuousIntegralExchangeTargetAdjunct

/-! # The exchange equality for condensed finite-to-Qbar coefficient change -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))

section RestrictionAPI
variable {T U : Scheme.{u}} [T.Over (Spec (.of k))] [U.Over (Spec (.of k))]
  [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]
  [IsSeparated (T ↘ Spec (.of k))]
  [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
  [IsSeparated (U ↘ Spec (.of k))] (h : T ⟶ U) [h.IsOver (Spec (.of k))]

private lemma qbar_map_hom {K M : PadicSubfieldConstructible T ℓ E} (v : K ⟶ M) :
    ((constructibleToPadicAlgCl T ℓ E).map v).hom =
      L(Mod.extendScalars
        (coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) T)).map v.hom := rfl

private lemma qbar_obj_obj (K : PadicSubfieldConstructible T ℓ E) :
    ((constructibleToPadicAlgCl T ℓ E).obj K).obj =
      L(Mod.extendScalars
        (coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) T)).obj K.obj := rfl

private lemma upper_map_hom
    {K M : PadicAlgClConstructible U ℓ} (v : K ⟶ M) :
    ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ k h).map v).hom =
      L((h)^*⟦Profinite.padicAlgClRingObj ℓ⟧).map v.hom := rfl

private lemma upper_obj_obj (K : PadicSubfieldConstructible U ℓ E) :
    ((boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ k h).obj K).obj =
      L((h)^*⟦Profinite.continuousMapRingObj E⟧).obj K.obj := rfl
end RestrictionAPI

attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctorIsoMapDerivedCategory
  CategoryTheory.Functor.leftDerivedFunctor CategoryTheory.Functor.mapDerivedCategory
attribute [local irreducible] monoidal_pointUpperStar monoidal_upperStarFromPoint
  pointUpperStarLowerStarAdjunction

set_option backward.isDefEq.respectTransparency true

set_option maxHeartbeats 150000 in
-- The canonical module-object comparisons require repeated exactness instance inference.
private theorem qbarPullIso_comp
    {T U : Scheme.{u}} [T.Over (Spec (.of k))] [U.Over (Spec (.of k))]
    [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]
    [IsSeparated (T ↘ Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))] (h : T ⟶ U) [h.IsOver (Spec (.of k))]
    {V : Scheme.{u}} [V.Over (Spec (.of k))]
    [LocallyOfFiniteType (V ↘ Spec (.of k))] [QuasiCompact (V ↘ Spec (.of k))]
    [IsSeparated (V ↘ Spec (.of k))] (j : U ⟶ V) [j.IsOver (Spec (.of k))]
    (K : PadicSubfieldConstructible V ℓ E) :
    (constructibleToPadicAlgCl T ℓ E).mapIso
        ((boundedConstructibleUpperStarComp (Profinite.continuousMapRingObj E) ℓ k h j).app K) ≪≫
      constructibleToQbarPullIso ℓ k E h
        ((boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ k j).obj K) ≪≫
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ k h).mapIso
        (constructibleToQbarPullIso ℓ k E j K) =
    constructibleToQbarPullIso ℓ k E (h ≫ j) K ≪≫
      (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ k h j).app
        ((constructibleToPadicAlgCl V ℓ E).obj K) := by
  apply Iso.ext
  apply ObjectProperty.hom_ext
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    ObjectProperty.FullSubcategory.comp_hom, constructibleToQbarPullIso]
  simp only [qbar_map_hom, upper_map_hom, ObjectProperty.isoMk,
    ObjectProperty.homMk_hom]
  conv_lhs =>
    lhs
    arg 2
    rw [bounded_comp_hom ℓ k (Profinite.continuousMapRingObj E) h j K]
  conv_rhs =>
    rhs
    rw [bounded_comp_hom ℓ k (Profinite.padicAlgClRingObj ℓ) h j
      ((constructibleToPadicAlgCl V ℓ E).obj K)]
  have he := congr_app
    (derived_pull_comp (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) h j) K.obj
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Category.comp_id] at he
  simp only [qbar_obj_obj ℓ E K, upper_obj_obj ℓ k E j K]
  dsimp only [constructibleToPadicAlgCl, boundedConstructibleUpperStar,
    ObjectProperty.lift_obj_obj, Functor.comp_obj, ObjectProperty.ι_obj,
    derivedExtendScalarsToPadicAlgCl, finiteCoefficientDerivedToAlgCl, Iso.app_hom,
    padicAlgClRingObj, padicSubfieldRingObj]
  -- Normalize the implicit objects of the restricted composition maps as well.
  convert! he using 1

variable {X Y X' Y' : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [X'.Over (Spec (.of k))] [Y'.Over (Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
  [IsSeparated (X ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
  [IsSeparated (Y ↘ Spec (.of k))]
  [LocallyOfFiniteType (X' ↘ Spec (.of k))] [QuasiCompact (X' ↘ Spec (.of k))]
  [IsSeparated (X' ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y' ↘ Spec (.of k))] [QuasiCompact (Y' ↘ Spec (.of k))]
  [IsSeparated (Y' ↘ Spec (.of k))]
  (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
  [f.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))]
  [f'.IsOver (Spec (.of k))] [g'.IsOver (Spec (.of k))]

set_option backward.isDefEq.respectTransparency true in
private lemma qbarPull_eq
    {T U : Scheme.{u}} [T.Over (Spec (.of k))] [U.Over (Spec (.of k))]
    [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]
    [IsSeparated (T ↘ Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))] (h : T ⟶ U) [h.IsOver (Spec (.of k))]
    (j : T ⟶ U) [j.IsOver (Spec (.of k))] (w : h = j)
    (K : PadicSubfieldConstructible U ℓ E) :
    (constructibleToPadicAlgCl T ℓ E).mapIso
        ((eqToIso (by subst j; rfl) :
          boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ k h ≅
            boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ k j).app K) ≪≫
      constructibleToQbarPullIso ℓ k E j K =
    constructibleToQbarPullIso ℓ k E h K ≪≫
      (eqToIso (by subst j; rfl) :
        boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ k h ≅
          boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ k j).app
          ((constructibleToPadicAlgCl U ℓ E).obj K) := by
  subst j
  change (constructibleToPadicAlgCl T ℓ E).mapIso (Iso.refl _) ≪≫ _ =
    _ ≪≫ Iso.refl _
  simp only [Functor.mapIso_refl, Iso.refl_trans, Iso.trans_refl]

section PullSquareCalculation
attribute [local irreducible] constructibleToPadicAlgCl
  constructibleToQbarPullIso
  boundedConstructibleUpperStar boundedConstructibleLowerStar

private lemma qbarPull_square_cube_iso
    (sq : CommSq g' f' f g) (M : PadicSubfieldConstructible Y ℓ E) :
    (constructibleToPadicAlgCl X' ℓ E).mapIso
        ((boundedConstructiblePullbackSquareComparison
          (Profinite.continuousMapRingObj E) ℓ k sq).app M) ≪≫
      constructibleToQbarPullIso ℓ k E g'
        ((boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ k f).obj M) ≪≫
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ k g').mapIso
        (constructibleToQbarPullIso ℓ k E f M) =
    constructibleToQbarPullIso ℓ k E f'
        ((boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ k g).obj M) ≪≫
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ k f').mapIso
        (constructibleToQbarPullIso ℓ k E g M) ≪≫
      (boundedConstructiblePullbackSquareComparison
        (Profinite.padicAlgClRingObj ℓ) ℓ k sq).app
          ((constructibleToPadicAlgCl Y ℓ E).obj M) := by
  have h₁ := qbarPullIso_comp ℓ k E g' f M
  have h₂ := qbarPullIso_comp ℓ k E f' g M
  have he := qbarPull_eq ℓ k E (f' ≫ g) (g' ≫ f) sq.w.symm M
  conv_lhs =>
    lhs
    arg 2
    rw [boundedConstructiblePullbackSquareComparison_app]
  conv_rhs =>
    rhs
    rhs
    rw [boundedConstructiblePullbackSquareComparison_app]
  exact mapped_iso_rectangle (constructibleToPadicAlgCl X' ℓ E)
      ((boundedConstructibleUpperStarComp (Profinite.continuousMapRingObj E) ℓ k f' g).app M)
      ((boundedConstructibleUpperStarComp (Profinite.continuousMapRingObj E) ℓ k g' f).app M)
      ((eqToIso (by simp only [sq.w]) :
        boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ k (f' ≫ g) ≅
        boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ k (g' ≫ f)).app M)
      ((boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ)
        ℓ k f' g).app ((constructibleToPadicAlgCl Y ℓ E).obj M))
      ((boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ)
        ℓ k g' f).app ((constructibleToPadicAlgCl Y ℓ E).obj M))
      ((eqToIso (by simp only [sq.w]) :
        boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ k (f' ≫ g) ≅
        boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ k (g' ≫ f)).app
        ((constructibleToPadicAlgCl Y ℓ E).obj M))
      _ _ _ _ _ _ h₁ h₂ he

private lemma qbarPull_square_cube
    (sq : CommSq g' f' f g) (M : PadicSubfieldConstructible Y ℓ E) :
    (constructibleToPadicAlgCl X' ℓ E).map
        ((boundedConstructiblePullbackSquareComparison
          (Profinite.continuousMapRingObj E) ℓ k sq).hom.app M) ≫
      (constructibleToQbarPullIso ℓ k E g'
        ((boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ k f).obj M)).hom ≫
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ k g').map
        (constructibleToQbarPullIso ℓ k E f M).hom =
    (constructibleToQbarPullIso ℓ k E f'
        ((boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ k g).obj M)).hom ≫
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ k f').map
        (constructibleToQbarPullIso ℓ k E g M).hom ≫
      (boundedConstructiblePullbackSquareComparison
        (Profinite.padicAlgClRingObj ℓ) ℓ k sq).hom.app
          ((constructibleToPadicAlgCl Y ℓ E).obj M) := by
  simpa only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom] using
    congrArg Iso.hom (qbarPull_square_cube_iso ℓ k E f g f' g' sq M)

end PullSquareCalculation

/-- Coefficient pullback comparisons commute with the specified geometric square comparison.
Source: ChangeOfCoefficients.lean, derivedPullIso and derivedComapLowerStarIso;
UpperLowerStar/Defs.lean, upperStarComp; Derived/UpperLowerStar.lean, leftDerivedUpperStarComp;
TwoColimit.lean, final transport paragraph
(blueprint: lem-weil-pbc-qbar-condensed-pullback-cube).

Proof in words. Restriction of scalars followed by geometric direct image and geometric
direct image followed by restriction have the same underlying sheaf functor; the natural
isomorphism comapLowerStarIso is the identity on underlying sheaves. Its compatibility
with direct-image composition follows by forgetting the action, which is faithful, and
using associativity of direct-image composition. The change-of-coefficients square for
the coefficient maps follows from their naturality. Derive these commuting diagrams using
K-injective resolutions: restriction is exact and preserves K-injectives since its left
adjoint is exact, and direct images preserve K-injectives. The universal property of the
right derived functor identifies the resulting comparison with derivedComapLowerStarIso
and preserves its composition equation. Conjugate that equation along the two geometric
adjunctions and the extension/restriction adjunctions. Conjugation respects composition
and associators, giving compatibility of derivedPullIso with geometric composition.
The geometric composition maps are the specified leftDerivedUpperStarComp: derive the
underived adjunction-conjugate composition equation and use uniqueness of derived
adjunctions, with exact pullbacks computed termwise. Apply this composition equation to
(f', g) and (g', f), transport along sq.w, and cancel the common comparison for the equal
composite. Naturality under equality and proof irrelevance handle the commutativity proof.
This gives the pullback cube in the displayed inverse-alpha_f' orientation. Restrict along
the fully faithful bounded constructible inclusions, whose composition constraints are
restrictions of these same maps. This proof uses no base-change exchange morphism, no
push comparison, and no properness or Cartesianity. For identity morphisms the equation
reduces to the unit coherence; for a zero object both sides are its unique morphism. -/
theorem constructibleToQbar_pullback_cube
    (sq : CommSq g' f' f g) (V : PadicSubfieldConstructible Y ℓ E) :
    (constructibleToQbarPullIso ℓ k E f'
      ((boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ k g).obj V)).inv ≫
      (constructibleToPadicAlgCl X' ℓ E).map
        ((boundedConstructiblePullbackSquareComparison
          (Profinite.continuousMapRingObj E) ℓ k sq).hom.app V) ≫
      (constructibleToQbarPullIso ℓ k E g'
        ((boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ k f).obj V)).hom =
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ k f').map
      (constructibleToQbarPullIso ℓ k E g V).hom ≫
      (boundedConstructiblePullbackSquareComparison (Profinite.padicAlgClRingObj ℓ)
        ℓ k sq).hom.app ((constructibleToPadicAlgCl Y ℓ E).obj V) ≫
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ k g').map
        (constructibleToQbarPullIso ℓ k E f V).inv := by
  simpa only [Category.assoc] using inverse_mapped_square
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ k g')
    (constructibleToQbarPullIso ℓ k E f'
      ((boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ k g).obj V))
    (constructibleToQbarPullIso ℓ k E f V) _ _ _
    (qbarPull_square_cube ℓ k E f g f' g' sq V)

end AlgebraicGeometry.ProEtale.CondensedRing
