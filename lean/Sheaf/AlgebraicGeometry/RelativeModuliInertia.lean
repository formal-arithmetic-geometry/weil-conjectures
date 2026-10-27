/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q145
-/
module

public import Sheaf.AlgebraicGeometry.ModuliInertia

/-! # Relative inertia of a morphism of fibred groupoids

Source: Stacks Project, Categories, Tag 034H
(blueprint: def-sfb-relative-moduli-inertia).

The full subcategory retains exactly the vertical automorphisms killed by the morphism.
Its arrows are the existing inertia arrows, so they commute with those automorphisms.
-/

@[expose] public section

set_option autoImplicit false

universe u v₁ w₁ v₂ w₂

namespace CategoryTheory

/-- Relative inertia retains the absolute inertia objects whose automorphism maps to identity.
Source: Stacks Project, Categories, Tag 034H
(blueprint: def-sfb-relative-moduli-inertia). -/
def relativeModuliInertia {S : AlgebraicGeometry.Scheme.{u}}
    {F : BasedCategory.{v₁, w₁} (Over S)} {G : BasedCategory.{v₂, w₂} (Over S)}
    (h : BasedFunctor F G) : BasedCategory (Over S) :=
  BasedCategory.ofFunctor
    (ObjectProperty.ι (fun x : ModuliInertiaObject F ↦
      h.toFunctor.map x.automorphism.hom = 𝟙 (h.obj x.obj)) ⋙
        moduliInertiaForget F ⋙ F.p)

/-- Inclusion of relative inertia in absolute inertia, preserving the actual automorphism.
Source: Stacks Project, Categories, Tag 034H
(blueprint: def-sfb-relative-moduli-inertia). -/
def relativeModuliInertiaToAbsolute {S : AlgebraicGeometry.Scheme.{u}}
    {F : BasedCategory.{v₁, w₁} (Over S)} {G : BasedCategory.{v₂, w₂} (Over S)}
    (h : BasedFunctor F G) : BasedFunctor (relativeModuliInertia h) (moduliInertia F) where
  toFunctor := ObjectProperty.ι _
  w := rfl

/-- The relative inertia projection forgets the automorphism.
Source: Stacks Project, Categories, Tag 034H
(blueprint: def-sfb-relative-moduli-inertia). -/
def relativeModuliInertiaProjection {S : AlgebraicGeometry.Scheme.{u}}
    {F : BasedCategory.{v₁, w₁} (Over S)} {G : BasedCategory.{v₂, w₂} (Over S)}
    (h : BasedFunctor F G) : BasedFunctor (relativeModuliInertia h) F :=
  (relativeModuliInertiaToAbsolute h).comp (moduliInertiaProjection F)

/-- The neutral section sends an object to its identity automorphism and an arrow to itself.
Source: Stacks Project, Morphisms of Stacks, higher diagonals preceding Tag 0CL0
(blueprint: def-sfb-relative-moduli-inertia). -/
def relativeModuliInertiaNeutral {S : AlgebraicGeometry.Scheme.{u}}
    {F : BasedCategory.{v₁, w₁} (Over S)} {G : BasedCategory.{v₂, w₂} (Over S)}
    (h : BasedFunctor F G) : BasedFunctor F (relativeModuliInertia h) where
  toFunctor :=
    { obj := fun x ↦ ⟨⟨x, Iso.refl x, by simp⟩, by simp⟩
      map := fun a ↦ ObjectProperty.homMk ⟨a, by simp⟩ }
  w := rfl

/-- The structural morphism to the base scheme, represented by the identity category over it.
The fibre over every scheme has just its identity object and identity arrow.
Source: Stacks Project, Categories, Tag 034H, absolute specialization
(blueprint: def-sfb-relative-moduli-inertia). -/
def moduliBaseStructure {S : AlgebraicGeometry.Scheme.{u}}
    (F : BasedCategory.{v₁, w₁} (Over S)) :
    BasedFunctor F (BasedCategory.ofFunctor (𝟭 (Over S))) where
  toFunctor := F.p
  w := rfl

end CategoryTheory
