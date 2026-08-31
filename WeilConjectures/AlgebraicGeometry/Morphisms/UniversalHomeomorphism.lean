/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Universal homeomorphisms of schemes

A morphism of schemes is a *universal homeomorphism* if every base change of it is a
homeomorphism on underlying topological spaces. By [Stacks 04DF] this holds if and only if
the morphism is integral, universally injective and surjective, and this is the definition
we take: all three are readily available as classes, while quantifying over all base
changes is not.

## Main definitions

- `AlgebraicGeometry.UniversalHomeomorphism`: the class of universal homeomorphisms.

## Main statements

- `AlgebraicGeometry.universalHomeomorphism_eq`: the `MorphismProperty` description of the
  class, through which the stability properties are proved.
- `AlgebraicGeometry.Scheme.Hom.isHomeomorph`: a universal homeomorphism is in particular a
  homeomorphism on underlying spaces;
  `AlgebraicGeometry.UniversalHomeomorphism.homeomorph` is the bundled form.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MorphismProperty

namespace AlgebraicGeometry

variable {X Y Z S : Scheme.{u}}

/-- A morphism of schemes is a universal homeomorphism if it is integral, universally
injective and surjective; equivalently, if every base change of it is a homeomorphism
on underlying spaces. See https://stacks.math.columbia.edu/tag/04DF. -/
@[mk_iff, stacks 04DF]
class UniversalHomeomorphism (f : X ⟶ Y) : Prop
    extends IsIntegralHom f, UniversallyInjective f, Surjective f

theorem universalHomeomorphism_eq :
    @UniversalHomeomorphism = (@IsIntegralHom ⊓ @UniversallyInjective ⊓ @Surjective :
      MorphismProperty Scheme.{u}) := by
  ext X Y f
  rw [universalHomeomorphism_iff]
  exact ⟨fun ⟨h₁, h₂, h₃⟩ ↦ ⟨⟨h₁, h₂⟩, h₃⟩, fun ⟨⟨h₁, h₂⟩, h₃⟩ ↦ ⟨h₁, h₂, h₃⟩⟩

namespace UniversalHomeomorphism

instance : IsMultiplicative @UniversalHomeomorphism.{u} :=
  universalHomeomorphism_eq ▸ inferInstance

instance : IsStableUnderComposition @UniversalHomeomorphism.{u} :=
  universalHomeomorphism_eq ▸ inferInstance

instance : IsStableUnderBaseChange @UniversalHomeomorphism.{u} :=
  universalHomeomorphism_eq ▸ inferInstance

instance : RespectsIso @UniversalHomeomorphism.{u} :=
  universalHomeomorphism_eq ▸ inferInstance

instance comp (f : X ⟶ Y) (g : Y ⟶ Z) [UniversalHomeomorphism f] [UniversalHomeomorphism g] :
    UniversalHomeomorphism (f ≫ g) :=
  MorphismProperty.comp_mem _ _ _ ‹_› ‹_›

instance (f : X ⟶ S) (g : Y ⟶ S) [UniversalHomeomorphism g] :
    UniversalHomeomorphism (pullback.fst f g) :=
  MorphismProperty.pullback_fst f g inferInstance

instance (f : X ⟶ S) (g : Y ⟶ S) [UniversalHomeomorphism f] :
    UniversalHomeomorphism (pullback.snd f g) :=
  MorphismProperty.pullback_snd f g inferInstance

instance (f : X ⟶ Y) [IsIso f] : UniversalHomeomorphism f where

/-- A surjective closed immersion is a universal homeomorphism. This covers the case of a
closed immersion cut out by a nilpotent sheaf of ideals, see [Stacks 03SI]. -/
instance (f : X ⟶ Y) [IsClosedImmersion f] [Surjective f] : UniversalHomeomorphism f where

end UniversalHomeomorphism

/-- A universal homeomorphism is a homeomorphism on underlying topological spaces. -/
theorem Scheme.Hom.isHomeomorph (f : X ⟶ Y) [UniversalHomeomorphism f] :
    IsHomeomorph f.base :=
  isHomeomorph_iff_continuous_isClosedMap_bijective.mpr
    ⟨f.base.hom.continuous, f.isClosedMap, f.injective, f.surjective⟩

/-- The homeomorphism of underlying topological spaces induced by a universal
homeomorphism.

This is not called `Scheme.Hom.homeomorph`, since that name is taken by the homeomorphism
attached to an isomorphism of schemes. -/
noncomputable def UniversalHomeomorphism.homeomorph (f : X ⟶ Y) [UniversalHomeomorphism f] :
    X ≃ₜ Y :=
  IsHomeomorph.homeomorph _ f.isHomeomorph

end AlgebraicGeometry
