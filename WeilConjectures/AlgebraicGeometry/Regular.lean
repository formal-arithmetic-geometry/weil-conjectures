/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Regular schemes

A scheme is *regular* if all of its local rings are regular local rings. Mathlib has the
predicate `IsRegularLocalRing` on commutative rings but no class for schemes, so it is
introduced here; it is a hypothesis of the divisor sequence and of Grothendieck's residue
injection for the Brauer group.

## Main statements

- `AlgebraicGeometry.isRegularLocalRing_stalk_of_etale`: a scheme étale over a regular scheme
  is regular.
- `AlgebraicGeometry.isRegularLocalRing_stalk_pullback`: a product of regular schemes locally
  of finite type over a perfect field is regular.
- `AlgebraicGeometry.IsRegular.of_smooth`: a scheme smooth over a field is regular.
- `AlgebraicGeometry.IsRegular.irreducibleSpace`: a connected locally noetherian regular scheme
  is irreducible.
- `AlgebraicGeometry.GeometricallyIrreducible.of_smooth_of_geometricallyConnected`: a smooth
  morphism with geometrically connected fibres has geometrically irreducible fibres.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- A scheme is *regular* if the local ring at each of its points is a regular local ring. -/
@[mk_iff]
class IsRegular (X : Scheme.{u}) : Prop where
  /-- The local ring of a regular scheme at any point is a regular local ring. -/
  isRegularLocalRing_stalk (x : X) : IsRegularLocalRing (X.presheaf.stalk x)

attribute [instance] IsRegular.isRegularLocalRing_stalk

/-- A scheme étale over a regular scheme is regular: an étale local homomorphism of local rings
is flat with regular (indeed trivial) closed fibre, so it preserves regularity. -/
theorem isRegularLocalRing_stalk_of_etale {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f]
    (hY : ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y)) (x : X) :
    IsRegularLocalRing (X.presheaf.stalk x) :=
  sorry

/-- The product of two regular schemes locally of finite type over a perfect field `k` is
regular: over a perfect field such schemes are smooth, and smoothness is stable under base
change and composition. -/
theorem isRegularLocalRing_stalk_pullback {k : Type u} [Field k] [PerfectField k]
    {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    [LocallyOfFiniteType g] (hX : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x))
    (hY : ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y)) (z : ↥(pullback f g)) :
    IsRegularLocalRing ((pullback f g).presheaf.stalk z) :=
  sorry

/-- A scheme smooth over a field `k` is regular: the local rings of a smooth `k`-scheme are
regular local rings. -/
theorem IsRegular.of_smooth {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [Smooth f] : IsRegular X :=
  sorry

/-- A connected locally noetherian regular scheme is irreducible, since its local rings, being
regular, are integral domains. -/
theorem IsRegular.irreducibleSpace (X : Scheme.{u}) [IsRegular X] [IsLocallyNoetherian X]
    [ConnectedSpace X] : IrreducibleSpace X :=
  irreducibleSpace_of_isDomain_stalk X fun _ ↦ inferInstance

/-- A smooth morphism with geometrically connected fibres has geometrically irreducible fibres:
a base change of it to a field is smooth over that field, hence regular and locally noetherian,
and connected, hence irreducible. -/
theorem GeometricallyIrreducible.of_smooth_of_geometricallyConnected {X S : Scheme.{u}}
    (f : X ⟶ S) [Smooth f] [GeometricallyConnected f] : GeometricallyIrreducible f where
  geometrically_irreducibleSpace _ _ y _ fst snd h := by
    have := GeometricallyConnected.geometrically_connectedSpace y fst snd h
    have : Smooth snd := MorphismProperty.of_isPullback h ‹Smooth f›
    have := LocallyOfFiniteType.isLocallyNoetherian snd
    have := IsRegular.of_smooth snd
    exact IsRegular.irreducibleSpace _

end AlgebraicGeometry
