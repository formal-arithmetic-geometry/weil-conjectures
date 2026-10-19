/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N4
-/
module

public import Sheaf.AlgebraicGeometry.StrictTowerOpenExtension
public import Sheaf.AlgebraicGeometry.OpenImmersionSquare

/-!
# Normalized finite constant-coefficient open base change

Source: Stacks Project, Tags 0F7B, 0F7C, 0F7D, 0F7F, 07A7 and 09AE, and the explicit
strict-tower refinement in the blueprint (blueprint: lem-cbc-proetale-extension-zero-base-change).

The index `n : ℕ` denotes positive level `n+1`. All derived categories below localize
complexes of strict towers, rather than forming towers in separate derived categories.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale.StrictTower

variable (B : Type (u + 1)) [CommRing B]

/-- The square compositor is uniquely determined by its explicit composition formula.
Source: Stacks, Tag 09AE
(blueprint: lem-fix-constant-square-compositor-specification).
Proof: the displayed composite witnesses existence, and the required equality gives uniqueness. -/
theorem moduleSquareG_existsUnique {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) (h : k ≫ p = r ≫ i) :
    ∃! e : modulePullback B i ⋙ modulePullback B r ≅
        modulePullback B p ⋙ modulePullback B k,
      e = (moduleGComp B r i).symm ≪≫ eqToIso (congrArg (modulePullback B) h.symm) ≪≫
        moduleGComp B k p := by
  exact ⟨_, rfl, fun _ he ↦ he⟩

/-- The canonical single-level pullback-square identification.
Source: Stacks, Tag 09AE
(blueprint: lem-cbc-proetale-extension-zero-base-change). -/
noncomputable def moduleSquareG {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) (h : k ≫ p = r ≫ i) :
    modulePullback B i ⋙ modulePullback B r ≅ modulePullback B p ⋙ modulePullback B k :=
  (moduleSquareG_existsUnique B k r p i h).choose

/-- The specified square compositor equals the original explicit composite.
Source: Stacks, Tag 09AE
(blueprint: lem-fix-constant-square-compositor-specification).
Proof: this is the equality clause of the unique specification. -/
theorem moduleSquareG_eq {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) (h : k ≫ p = r ≫ i) :
    moduleSquareG B k r p i h =
      (moduleGComp B r i).symm ≪≫ eqToIso (congrArg (modulePullback B) h.symm) ≪≫
        moduleGComp B k p :=
  (moduleSquareG_existsUnique B k r p i h).choose_spec.1

/-- The inverse open-base-change component, specified by the original open-unit transpose.
Source: Stacks, Tag 09AE
(blueprint: lem-cbc-proetale-extension-zero-base-change). -/
noncomputable def singleBetaInvApp {U' U X' X : Scheme.{u}}
    (a : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : a ≫ j = j' ≫ g) (M : Modules B U) :
    (moduleJ B j').obj ((modulePullback B a).obj M) ⟶
      (modulePullback B g).obj ((moduleJ B j).obj M) :=
  ((moduleJAdj B j').homEquiv _ _).symm
    ((modulePullback B a).map ((moduleJAdj B j).unit.app M) ≫
      (moduleSquareG B a j' j g h).inv.app ((moduleJ B j).obj M))

/-- Naturality follows from the same open-unit transpose.
Source: Stacks, Tag 09AE
(blueprint: lem-cbc-proetale-extension-zero-base-change).
Proof: transpose each naturality square under the open adjunction. Naturality of
the open unit and of the pullback-square comparison makes their transposes equal. -/
theorem singleBetaInvApp_naturality {U' U X' X : Scheme.{u}}
    (a : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : a ≫ j = j' ≫ g)
    (M N : Modules B U) (f : M ⟶ N) :
    (moduleJ B j').map ((modulePullback B a).map f) ≫ singleBetaInvApp B a j' j g h N =
      singleBetaInvApp B a j' j g h M ≫
        (modulePullback B g).map ((moduleJ B j).map f) := by
  sorry

/-- The specified inverse comparison, as a natural transformation.
Source: Stacks, Tag 09AE
(blueprint: lem-cbc-proetale-extension-zero-base-change). -/
noncomputable def singleBetaInv {U' U X' X : Scheme.{u}}
    (a : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : a ≫ j = j' ≫ g) :
    modulePullback B a ⋙ moduleJ B j' ⟶ moduleJ B j ⋙ modulePullback B g where
  app := singleBetaInvApp B a j' j g h
  naturality := singleBetaInvApp_naturality B a j' j g h

/-- The finite-coefficient canonical comparison is invertible for a cartesian square.
Source: Stacks, Tag 09AE
(blueprint: lem-cbc-proetale-extension-zero-base-change).
Proof: open localization identifies the right adjoints by restriction on the same
pulled-back test objects. Their left adjoints have the unique unit-preserving
isomorphism. Its inverse has exactly the displayed open-unit transpose, hence is
singleBetaInv. Exactness passes this isomorphism degreewise and through localization. -/
theorem singleBetaInv_isIso [Finite B] {U' U X' X : Scheme.{u}}
    (a : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : a ≫ j = j' ≫ g)
    (hsq : IsPullback a j' j g) : IsIso (singleBetaInv B a j' j g h) := by
  sorry

/-- The existing finite open-base-change comparison, in constant-ring module coordinates.
Its inverse has the prescribed open-unit transpose; no new map is chosen.
Source: Stacks, Tag 09AE
(blueprint: lem-cbc-proetale-extension-zero-base-change). -/
noncomputable def singleBeta [Finite B] {U' U X' X : Scheme.{u}}
    (a : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : a ≫ j = j' ≫ g)
    (hsq : IsPullback a j' j g) :
    (moduleJ B j).mapDerivedCategory ⋙ (modulePullback B g).mapDerivedCategory ≅
      (modulePullback B a).mapDerivedCategory ⋙ (moduleJ B j').mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (@asIso _ _ _ _ (singleBetaInv B a j' j g h)
        (singleBetaInv_isIso B a j' j g h hsq)).symm ≪≫
    Functor.mapDerivedCategoryCompIso _ _

end AlgebraicGeometry.ProEtale.StrictTower
