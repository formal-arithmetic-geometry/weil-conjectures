/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M4
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Sheaf.AlgebraicGeometry.OpenModuleStalkFunctor

/-! # Shrinking stalk equality for a finite retract sheaf

Source: Stacks Project, Tags 09RE, 0BC7 and 01CP.
(blueprint: lem-sc-perfect-open-stalk-retract-map-equality).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
noncomputable section

/-- Equality of endomorphisms of a finite free retract at one stalk holds nearby.
Source: Stacks Project, Tag 01CP, finite-type injectivity proof.
(blueprint: lem-sc-perfect-open-stalk-retract-map-equality).

Proof: Restrict the finite-free inclusion and retraction to Z. Restriction
preserves the finite free sheaf and the splitting identity. Sandwich a-b into
that free sheaf. Its matrix has finitely many entries, whose germs vanish because
the given stalk maps agree. For each entry choose an open inside Z on which it
vanishes, by the germ equality criterion. Intersect the finitely many opens.
The restricted sandwich map is zero there; composing with the restricted
inclusion and retraction and using their splitting identity proves that a and b
agree. Stalk formation after restriction uses the open-subscheme comparison in
the definition of openModuleStalkFunctor, and restriction of scalars is faithful.
The empty matrix gives the unique endomorphism of the zero retract. Arbitrary
non-Noetherian structure rings and Z=V=U obey the same proof. -/
theorem exists_open_stalk_retract_map_eq
    (X : Scheme.{u}) (U : X.Opens)
    (M : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
    (hM : ∃ m : ℕ,
      ∃ (ι : M ⟶ SheafOfModules.free
          (R := (moduleRings X.toRingedSpace).over U) (ULift.{u} (Fin m)))
        (π : SheafOfModules.free
          (R := (moduleRings X.toRingedSpace).over U) (ULift.{u} (Fin m)) ⟶ M),
        ι ≫ π = 𝟙 M)
    (x : X) (V Z : X.Opens) (hxZ : x ∈ Z) (hVU : V ≤ U) (hZV : Z ≤ V)
    (a b :
      (SheafOfModules.overMap (moduleRings X.toRingedSpace) (homOfLE hZV)).obj
        ((SheafOfModules.overMap (moduleRings X.toRingedSpace) (homOfLE hVU)).obj M) ⟶
      (SheafOfModules.overMap (moduleRings X.toRingedSpace) (homOfLE hZV)).obj
        ((SheafOfModules.overMap (moduleRings X.toRingedSpace) (homOfLE hVU)).obj M))
    (heq : (openModuleStalkFunctor X Z ⟨x, hxZ⟩).map a =
      (openModuleStalkFunctor X Z ⟨x, hxZ⟩).map b) :
    ∃ (W : X.Opens) (hWZ : W ≤ Z), x ∈ W ∧
      (SheafOfModules.overMap (moduleRings X.toRingedSpace) (homOfLE hWZ)).map a =
      (SheafOfModules.overMap (moduleRings X.toRingedSpace) (homOfLE hWZ)).map b := by sorry

end
end AlgebraicGeometry.Scheme
