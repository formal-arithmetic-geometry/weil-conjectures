/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AlgebraicModuliStack
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-! # Inertia of a fibred category

Source: Stacks Project, Tags 034H and 06QJ (blueprint: def-sfb-moduli-inertia).

The inertia projection forgets a vertical automorphism. Flatness and local finite
presentation are tested on the actual scheme base changes and their étale charts.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory

namespace CategoryTheory

/-- An inertia object is an object with an automorphism over the identity of its base.
Source: Stacks Project, inertia of categories fibred in groupoids, Tag 034H
(blueprint: def-sfb-moduli-inertia). -/
structure ModuliInertiaObject {S : AlgebraicGeometry.Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) where
  /-- The underlying object. -/
  obj : F.obj
  /-- The automorphism. -/
  automorphism : obj ≅ obj
  /-- The automorphism lies over the identity. -/
  vertical : F.p.map automorphism.hom = 𝟙 (F.p.obj obj)

/-- Inertia arrows commute with the specified automorphisms.
Source: Stacks Project, Tag 034H (blueprint: def-sfb-moduli-inertia). -/
instance moduliInertiaCategory {S : AlgebraicGeometry.Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) : Category (ModuliInertiaObject F) where
  Hom x y := {f : x.obj ⟶ y.obj // x.automorphism.hom ≫ f = f ≫ y.automorphism.hom}
  id x := ⟨𝟙 x.obj, by simp⟩
  comp f g := ⟨f.val ≫ g.val, by
    rw [← Category.assoc, f.property, Category.assoc, g.property, ← Category.assoc]⟩
  id_comp f := Subtype.ext (Category.id_comp f.val)
  comp_id f := Subtype.ext (Category.comp_id f.val)
  assoc f g h := Subtype.ext (Category.assoc f.val g.val h.val)

/-- The forgetful functor from inertia objects to their underlying objects.
Source: Stacks Project, Tag 034H (blueprint: def-sfb-moduli-inertia). -/
def moduliInertiaForget {S : AlgebraicGeometry.Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) : ModuliInertiaObject F ⥤ F.obj where
  obj x := x.obj
  map f := f.val

/-- Inertia as a category over the same scheme base.
Source: Stacks Project, Tag 034H (blueprint: def-sfb-moduli-inertia). -/
def moduliInertia {S : AlgebraicGeometry.Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) : BasedCategory (Over S) :=
  BasedCategory.ofFunctor (moduliInertiaForget F ⋙ F.p)

/-- The canonical inertia projection, retaining the original underlying object.
Source: Stacks Project, Tag 034H (blueprint: def-sfb-moduli-inertia). -/
def moduliInertiaProjection {S : AlgebraicGeometry.Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) : BasedFunctor (moduliInertia F) F where
  toFunctor := moduliInertiaForget F
  w := rfl

/-- The inertia projection is representable by spaces, flat and locally finitely presented.
Every scheme base change is presented with its actual projection, and both properties
are required after every representable étale scheme chart.
Source: Stacks Project, Tag 06QJ (blueprint: def-sfb-moduli-inertia). -/
def HasFlatLocallyPresentedModuliInertia {S : AlgebraicGeometry.Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) : Prop :=
  ∀ (T : Over S) (t : BasedFunctor (discreteModuli (yoneda.obj T)) F),
    ∃ (Z : AlgebraicGeometry.AlgebraicSpace S) (p : Z.obj.obj ⟶ yoneda.obj T),
      HasSpaceBaseChange (moduliInertiaProjection F) T t Z p ∧
        ∀ (U : Over S) (a : yoneda.obj U ⟶ Z.obj.obj),
          AlgebraicGeometry.AlgebraicSpace.IsEtale a →
            AlgebraicGeometry.Flat ((yoneda.preimage (a ≫ p)).left) ∧
              AlgebraicGeometry.LocallyOfFinitePresentation ((yoneda.preimage (a ≫ p)).left)

end CategoryTheory
