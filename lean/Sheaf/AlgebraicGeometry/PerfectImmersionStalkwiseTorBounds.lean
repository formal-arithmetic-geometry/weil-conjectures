/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N3
-/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.DerivedTensorStructure
public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Monoidal.Tor

/-! # Stalkwise Tor bounds for a perfect closed immersion

Source: Stacks Project, Duality for Schemes, Tag 0A9U, hypothesis translation
in lem-sc-smooth-proper-diagonal-tensor-formula step 1.
(blueprint: lem-sc-perfect-immersion-stalkwise-tor-bounds).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry

/-- Perfection of the pushforward of the unit along a closed immersion gives finite
Tor bounds in both tensor variables on the actual stalk restriction of scalars.
Source: Stacks Project, Tag 0A9U, hypothesis translation in step 1 of
lem-sc-smooth-proper-diagonal-tensor-formula.
(blueprint: lem-sc-perfect-immersion-stalkwise-tor-bounds).

Proof. Fix z in Z and put y = i(z). Direct image along a closed immersion is exact
on modules: its stalk is the source stalk at points of Z and zero outside Z.
Consequently the stalk at y of Ri_*O_Z is O_{Z,z}, restricted along i.stalkMap z,
in degree zero. Take a strictly perfect local model furnished by hperfect at y.
Stalks preserve its finite-free direct-summand presentations, exactness, and its
quasi-isomorphism, giving a bounded complex of finite projective O_{Y,y}-modules
representing this restricted module. Choose a natural number larger than the
absolute values of the endpoints of this finite complex. Tensoring its projective
resolution with any test module has zero homology above this bound, proving the
Tor' assertion. For Tor, resolve the test module and use the tensor double complex:
augmenting its test-module direction computes the same bounded projective model
because those terms are flat; augmenting the other direction computes the derived
functor defining Tor. The two computations identify Tor and Tor', so the same
bound works. The argument is pointwise and permits bounds depending on z. -/
theorem perfectImmersion_stalkwiseTorBounds
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ U : Y.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U))]
    (hperfect : Y.IsPerfect ((schemeDerivedDirectImage i).obj
      (𝟙_ (schemeDerivedCategory Z)))) :
    (∀ x : Z, ∃ n : ℕ,
      ∀ (M : ModuleCat.{u} (Y.presheaf.stalk (i x))) (j : ℕ), n < j →
        IsZero (((Tor' (ModuleCat.{u} (Y.presheaf.stalk (i x))) j).obj
          ((ModuleCat.restrictScalars (i.stalkMap x).hom).obj
            (ModuleCat.of (Z.presheaf.stalk x) (Z.presheaf.stalk x)))).obj M)) ∧
    (∀ x : Z, ∃ n : ℕ,
      ∀ (M : ModuleCat.{u} (Y.presheaf.stalk (i x))) (j : ℕ), n < j →
        IsZero (((Tor (ModuleCat.{u} (Y.presheaf.stalk (i x))) j).obj
          ((ModuleCat.restrictScalars (i.stalkMap x).hom).obj
            (ModuleCat.of (Z.presheaf.stalk x) (Z.presheaf.stalk x)))).obj M)) := by sorry

end AlgebraicGeometry
