/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R4
-/
module

public import Mathlib.Geometry.RingedSpace.Basic
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Sheaf.Algebra.Homology.ModuleStalkFunctor
import Sheaf.Topology.PresheafModuleStalkFunctor

/-! # Detecting the zero germ of a local morphism by finite generation

Source: Stacks Project, Modules, Lemma 01CP, second paragraph.
-/

@[expose] public section

universe u
open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.RingedSpace

/-- A local morphism from a finite type sheaf whose induced stalk map is zero
has zero germ in internal Hom.

Source: Stacks Project, Modules, Lemma 01CP (`lemma-stalk-internal-hom`), second
paragraph (finite type case).
(blueprint: lem-weil-pbc-internal-hom-germ-zero-finite-type)

Proof: Restrict to a neighborhood of x where F has finitely many generating
sections. Intersect it with U. The images of these generators have zero germs
by the hypothesis. Shrink once for each generator and intersect the finitely
many resulting neighborhoods. All generator images are then zero sections.
The generators still generate the restriction of F, since restriction preserves
free sheaves and epimorphisms. Thus the restricted morphism is zero: compose
with the free generator epimorphism and use its right cancellation property.
Its germ, equal to the original germ, is consequently zero. If there are no
generators the source is zero on this neighborhood and the assertion is immediate. -/
theorem internalHom_germ_eq_zero_of_finiteType
    (X : RingedSpace.{u})
    (F G : SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology X)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf))
    [SheafOfModules.IsFiniteType.{u} F] (x : X)
    (U : Opens X) (hxU : x ∈ U) (φ : (F.homObj G).val.obj (op U))
    (hφ : ∀ (V : Opens X) (i : V ⟶ U) (hxV : x ∈ V) (s : F.val.obj (op V)),
      TopCat.Presheaf.germ G.val.presheaf V x hxV (φ.app (op (Over.mk i)) s) = 0) :
    TopCat.Presheaf.germ (F.homObj G).val.presheaf U x hxU φ = 0 := by
  sorry

end AlgebraicGeometry.RingedSpace
