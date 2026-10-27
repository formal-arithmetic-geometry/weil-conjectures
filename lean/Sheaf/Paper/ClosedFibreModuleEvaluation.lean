/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q22, D9
-/
module

public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback

/-! # Evaluation and canonical restriction of internal pro-etale modules

Source: Stacks Project, Tags 0D6F, 0D6G; the canonical unit-section restriction.
(blueprint: def-sfb-closed-fibre-module-evaluation).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- Evaluation of an internal module at a small pro-etale site object, forgetting its action.
Source: the derived-evaluation convention in the proper closed-fibre comparison
(blueprint: lem-sfb-proper-wcontractible-closed-fibre-rigidity). -/
abbrev closedFibreModuleEvaluation (X : Scheme.{u}) (U : X.ProEt) :
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X) ⥤
      Ab.{u + 1} :=
  Mod.forget (condensedRingObj Λ X) ⋙ sheafToPresheaf _ _ ⋙
    (evaluation _ _).obj (op U)

/-- Restriction of sections along a map from Z to the evaluating object over X.
It is the module adjunction unit, evaluated at U, followed by the presheaf restriction
along the map from the terminal Z-object to the base change of U.
Source: the canonical restriction described in the node, final paragraph
(blueprint: lem-sfb-proper-wcontractible-closed-fibre-rigidity). -/
def closedFibreModuleSectionsRestriction {X Z : Scheme.{u}} (a : Z ⟶ X)
    (U : X.ProEt) (φ : Z ⟶ U.left) (hφ : φ ≫ U.hom = a) :
    closedFibreModuleEvaluation Λ X U ⟶
      upperStar Λ a ⋙ closedFibreModuleEvaluation Λ Z (Scheme.ProEt.mk (𝟙 Z)) :=
  Functor.whiskerRight (upperStarLowerStarAdjunction Λ a).unit
      (closedFibreModuleEvaluation Λ X U) ≫
    Functor.whiskerLeft (upperStar Λ a)
      (Functor.whiskerLeft (Mod.forget (condensedRingObj Λ Z))
        ((sheafSections (Scheme.ProEt.topology Z) Ab.{u + 1}).map
          (MorphismProperty.Over.homMk
            (pullback.lift φ (𝟙 Z) (hφ.trans (Category.id_comp a).symm))
            (pullback.lift_snd _ _ _)).op))

/-- The ordinary unbounded derived restriction map. Exact inverse image acts termwise;
the right-derived pullback is characterized by the evaluation map and derived units.
Source: the node's canonical derived restriction, final paragraph
(blueprint: lem-sfb-proper-wcontractible-closed-fibre-rigidity). -/
def closedFibreModuleDerivedRestriction {X Z : Scheme.{u}} (a : Z ⟶ X)
    (U : X.ProEt) (φ : Z ⟶ U.left) (hφ : φ ≫ U.hom = a) :
    (closedFibreModuleEvaluation Λ X U).rightDerivedFunctor ⟶
      (upperStar Λ a).mapDerivedCategory ⋙
        (closedFibreModuleEvaluation Λ Z (Scheme.ProEt.mk (𝟙 Z))).rightDerivedFunctor :=
  Functor.rightDerivedPullback (upperStar Λ a)
    (closedFibreModuleSectionsRestriction Λ a U φ hφ)

end AlgebraicGeometry.ProEtale.CondensedRing
