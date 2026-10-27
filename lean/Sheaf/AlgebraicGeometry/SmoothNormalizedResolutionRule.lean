/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NP
-/
module

public import Sheaf.AlgebraicGeometry.QENormalizedResolutionRule
public import Sheaf.AlgebraicGeometry.OrdinaryResolutionRule
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Smooth normalized resolution rules

Source: ILO, Exposé VIII, 2.2.5--2.2.9 and 2.3.2--2.3.5
(blueprint: def-trf-smooth-normalized-resolution-rule).

The input, based towers, recursive cartesian comparisons and ordered unit contractions
are existing notions. Only the smooth family of morphisms is specified here.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Normal reduced finite-type rational inputs, without connectedness or separation
restrictions. Source: ILO VIII 2.2.1, 2.3.9--2.3.12
(blueprint: def-trf-smooth-normalized-resolution-rule). -/
def NormalRationalResolutionInput : Type (u + 1) :=
  {X : RationalResolutionInput.{u} // ∀ x : X.scheme,
    IsDomain (X.scheme.presheaf.stalk x) ∧ IsIntegrallyClosed (X.scheme.presheaf.stalk x)}

/-- A normalized resolution rule on a family of schemes with canonical smooth comparisons.
The reused comparison retains precisely the extended nonunit centers, in order, and
requires every deleted unit-center arrow to be an isomorphism. Identity and composition
hold on contraction indices and actual level maps. Surjective maps delete no stage.
Source: ILO VIII 2.2.5--2.2.9, 2.3.2--2.3.5
(blueprint: def-trf-smooth-normalized-resolution-rule). -/
structure SmoothNormalizedResolutionRule (I : Type v) (base : I → Scheme.{u}) where
  tower : ∀ X : I, QENormalizedResolutionTower (base X)
  comparison : ∀ (X Y : I) (h : base Y ⟶ base X), Smooth h →
    QENormalizedResolutionComparison h (tower X) (tower Y)
  empty : ∀ X : I, IsEmpty (base X) → (tower X).length = 0
  identityIndex : ∀ (X : I) (hr : Smooth (𝟙 (base X))) i,
    (comparison X X (𝟙 _) hr).contraction.index i = i
  identityMap : ∀ (X : I) (hr : Smooth (𝟙 (base X))) i,
    HEq ((comparison X X (𝟙 _) hr).levelMap i) (𝟙 ((tower X).tower.level i))
  compositionIndex : ∀ (X Y Z : I) (h : base Y ⟶ base X) (g : base Z ⟶ base Y)
    (hr : Smooth h) (gr : Smooth g)
    (ghr : Smooth (g ≫ h)) i,
    (comparison X Z (g ≫ h) ghr).contraction.index i =
      (comparison Y Z g gr).contraction.index ((comparison X Y h hr).contraction.index i)
  compositionMap : ∀ (X Y Z : I) (h : base Y ⟶ base X) (g : base Z ⟶ base Y)
    (hr : Smooth h) (gr : Smooth g)
    (ghr : Smooth (g ≫ h)) i,
    HEq ((comparison X Z (g ≫ h) ghr).levelMap i)
      ((comparison Y Z g gr).levelMap ((comparison X Y h hr).contraction.index i) ≫
        (comparison X Y h hr).levelMap i)
  surjective_no_deletion : ∀ (X Y : I) (h : base Y ⟶ base X)
    (hr : Smooth h), Surjective h →
      Function.Injective (comparison X Y h hr).contraction.index


end AlgebraicGeometry
