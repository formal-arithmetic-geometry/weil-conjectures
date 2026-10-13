/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D4
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Sheaf.AlgebraicGeometry.OpenModuleStalkFunctor

/-! # Local equality of morphisms from finite free retracts

Source: Stacks Project, Tag 01CP, finite-type injectivity argument.
(blueprint: lem-sc-perfect-open-stalk-retract-hom-equality).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
noncomputable section

/-- Maps from a restricted finite free retract to any module sheaf agree nearby
if their maps on the open module stalk agree.

Source: Stacks Project, Tag 01CP, injectivity for a finite-type source;
Tag 09RE, finite-presentation calculation.
(blueprint: lem-sc-perfect-open-stalk-retract-hom-equality).

Proof: Restrict the inclusion and projection exhibiting M as a retract to W.
Precompose a and b with the projection from the restricted finite free sheaf.
Their stalks agree by functoriality. Evaluate on each of its finitely many free
basis sections. The two resulting sections of N have equal germs. The germ
criterion gives a neighbourhood for each equality; intersect these finitely
many neighbourhoods inside W. The two maps from the free sheaf agree there
by their basis values. Precompose with the restricted inclusion and use the
splitting identity to obtain equality of a and b. The equivalence between the
slice site and the open subscheme identifies these germs with the specified
open module stalks; restriction of scalars is faithful. No finiteness of N is
used. For rank zero the retract is zero and both maps are uniquely zero. -/
theorem exists_open_stalk_retract_hom_eq
    (X : Scheme.{u}) (U W : X.Opens) (hWU : W ≤ U)
    (M : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
    (hM : ∃ m : ℕ,
      ∃ (ι : M ⟶ SheafOfModules.free
          (R := (moduleRings X.toRingedSpace).over U) (ULift.{u} (Fin m)))
        (π : SheafOfModules.free
          (R := (moduleRings X.toRingedSpace).over U) (ULift.{u} (Fin m)) ⟶ M),
        ι ≫ π = 𝟙 M)
    (N : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over W))
    (x : X) (hxW : x ∈ W)
    (a b : (SheafOfModules.overMap (moduleRings X.toRingedSpace)
      (homOfLE hWU)).obj M ⟶ N)
    (heq : (openModuleStalkFunctor X W ⟨x, hxW⟩).map a =
      (openModuleStalkFunctor X W ⟨x, hxW⟩).map b) :
    ∃ (V : X.Opens) (hVW : V ≤ W), x ∈ V ∧
      (SheafOfModules.overMap (moduleRings X.toRingedSpace) (homOfLE hVW)).map a =
      (SheafOfModules.overMap (moduleRings X.toRingedSpace) (homOfLE hVW)).map b := by sorry

end
end AlgebraicGeometry.Scheme
