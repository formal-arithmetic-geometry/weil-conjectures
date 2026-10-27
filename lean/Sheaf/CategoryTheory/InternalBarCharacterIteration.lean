/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R4
-/
module

public import Sheaf.CategoryTheory.InternalBarCharacterData

/-! # Ordered iteration of character deletion

The formulas for the actual recursively constructed composite and augmentation.
Source: agent-written internal bar calculation, steps 3--4
(blueprint: lem-sfb-internal-bar-character-iteration).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open Profinite.CondensedAction Profinite.CondensedAction.InternalBar
open CategoryTheory.CondensedDerivedRestriction (Character)
namespace Profinite.CondensedAction.InternalBarCharacter
variable {A : CategoryTheory.CondensedBar.Ring.{u}}
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- The generator and equivariance properties of the constructed ordered composites.
No inhomogeneous internal functions occur in this statement.
Source: character-lift calculation, steps 2--4
(blueprint: lem-sfb-internal-bar-character-iteration). -/
structure OrderedProperties (D : Resolution A.toMon G)
    (L : Character A G → (complex D ⟶ (complex D)⟦(1 : ℤ)⟧)) : Prop where
  anticommutation : ∀ (a : Character A G) (n : ℕ),
    component D (L a) (n + 1) ≫ (D.boundary n).val +
      (D.boundary (n + 1)).val ≫ component D (L a) n = 0
  equivariant : ∀ (a : List (Character A G)) (n : ℕ),
    Equivariant (D.objects (n + a.length)) (D.objects n)
      (component D (orderedIterate D L a) n)
  below : ∀ (a : List (Character A G)) (n : ℕ), n < a.length →
    (orderedIterate D L a).f (-(n : ℤ)) = 0
  generator : ∀ (a : List (Character A G)) (n : ℕ) (S : Profinite.{u})
      (x : Fin (n + a.length + 1) → C(S, G)),
    onSections A.toMon (component D (orderedIterate D L a) n) S
      (basis A.toMon G (n + a.length + 1) (D.objects (n + a.length))
        (D.freeIso (n + a.length)) S x) =
      (∏ k : Fin a.length, (a.get k).app S
        ((x ⟨k.val, by omega⟩)⁻¹ * x ⟨k.val + 1, by omega⟩)) •
        basis A.toMon G (n + 1) (D.objects n) (D.freeIso n) S
          (fun i ↦ x ⟨a.length + i.val, by omega⟩)
  augmented_equivariant : ∀ a : List (Character A G),
    Equivariant (D.objects a.length)
      ((trivial (R := A.toMon) (P := G)).obj (Mod.regular A.X))
      (augmentedComponent D (barAugmentation D) (orderedIterate D L a))
  augmented_closed : ∀ a : List (Character A G),
    (D.boundary a.length).val ≫
      augmentedComponent D (barAugmentation D) (orderedIterate D L a) = 0
  augmented_nil : augmentedComponent D (barAugmentation D) (orderedIterate D L []) =
    D.augmentation.val
  augmented_generator : ∀ (a : List (Character A G)) (S : Profinite.{u})
      (x : Fin (a.length + 1) → C(S, G)),
    onSections A.toMon
      (augmentedComponent D (barAugmentation D) (orderedIterate D L a)) S
      (basis A.toMon G (a.length + 1) (D.objects a.length) (D.freeIso a.length) S x) =
        ∏ k : Fin a.length, (a.get k).app S ((x k.castSucc)⁻¹ * x k.succ)

/-- Ordered iteration has the expected homogeneous product formula, equivariance,
and augmented cocycle equation.
Source: lem-sfb-internal-bar-character-lifts, proof steps 2--4, agent-written
internal-bar expansion of blueprint direct-images paragraph (3).
(blueprint: lem-sfb-internal-bar-character-iteration).

Proof: Transport the cochain-map equation of L across termIso. Since the
one-shift differential is -d, it becomes the displayed anticommutation identity.
Induct on the list by appending its last character, using orderedIterate_nil and
orderedIterate_snoc. The zero case is the identity on generators and has empty
product 1. Shifted maps have the same component maps, with only their degree
indices changed. Thus a component below the list length vanishes; at the new
endpoint it vanishes because the next deletion lift has target P^1=0. Above that
endpoint, linearity and IsLift multiply the existing coefficient by the next
character evaluated on the next ratio and delete the first remaining vertex.
The product is in the supplied list order. Components are equivariant because
they are composites of equivariant deletion components; the empty composite is
an identity. The augmentation is an equivariant chain map, normalized by
barAugmentation_zero, so its shifted composite has an equivariant sole component.
Its cochain equation in degree -q-1 gives the augmented closedness equation.
For the empty list its component is the original augmentation. Applying the
augmentation to the generator formula replaces the final singleton generator
by 1, yielding the last displayed product formula. All equalities hold after
every profinite base change. No projectivity or internal-Hom exactness is used.
-/
theorem ordered_properties (D : Resolution A.toMon G)
    (L : Character A G → (complex D ⟶ (complex D)⟦(1 : ℤ)⟧))
    (hL : ∀ a, IsLift D a (L a)) : OrderedProperties D L := by sorry

end Profinite.CondensedAction.InternalBarCharacter
