/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Sheaf.CategoryTheory.InternalBarCharacterLifts
public import Sheaf.CategoryTheory.InternalBarCharacterRoofCup

/-! # Equivariant realization of the underlying character lifts

Source: the chain-level assembly in steps 1--2 of the ordered-cup node, expanding
paragraph (3) of the six-functors direct-image argument.
(blueprint: lem-sfb-internal-bar-equivariant-character-lifts).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.CondensedBar CategoryTheory.CondensedBarRoof
open CategoryTheory.CondensedDerivedRestriction
open Profinite.CondensedAction.InternalBar
namespace CategoryTheory.CondensedBar.OrderedCup

variable {A : CondensedBar.Ring.{u}} {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- The augmented degree-minus-q component of an equivariant shifted bar map.
This is an actual composite; no lift or augmentation is selected by this definition.
Source: ordered-cup argument, step 1
(blueprint: lem-sfb-internal-bar-equivariant-character-lifts). -/
def augmentedRoofComponent (R : Resolution A.toMon G) (e : RoofAugmentation R)
    (q : ℕ) (Fq : complex R ⟶ (complex R)⟦(q : ℤ)⟧) :
    R.objects q ⟶ regularTrivial A G :=
  (termIso R q).inv ≫ (Fq ≫ e⟦(q : ℤ)⟧').f (-(q : ℤ)) ≫
    (CochainComplex.shiftFunctorObjXIso (single 0 (regularTrivial A G))
      (q : ℤ) (-(q : ℤ)) 0 (by omega)).hom ≫
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (regularTrivial A G)).hom

/-- The specified underlying deletion lifts lift to equivariant cochain maps. Their
ordered shifted composites have exactly the specified augmented components.
This assertion contains neither a cup product nor a derived bar comparison.
Source: ordered-cup argument, steps 1--2; the character-lift lemma, steps 1--4
(blueprint: lem-sfb-internal-bar-equivariant-character-lifts).

Proof:
1. The complex obtained by forgetting the action on the homogeneous bar is canonically
identified degree by degree with InternalBarCharacter.complex. In degree -n use the
extendXIso identifications; in positive degrees both terms are zero. These comparisons
commute with differentials because both differentials are the recorded boundary maps.
2. Lift the augmentation of the given Lifts to the action category. Its only nonzero
component is the recorded equivariant augmentation R.augmentation. The boundary equation
is R.boundary_augmentation. Exactness at every R.objects n, exactness at degree zero and
the epimorphic augmentation show this map is a quasi-isomorphism. Its zero component is
augmentationEquation, by the single-object and extension identifications.
3. For each character lift use lift_spec.1 to regard every component in degree -(n+1)
as an equivariant morphism. In all remaining degrees use zero maps. The faithful
forgetful functor reflects the chain-map equations, which are those of the supplied
underlying lift. In degree -1, lift_spec.2 and augmentation_generator show that the
augmented generator is a(g0^-1 g1), proving IsCharacterLift.
4. Induct on a list, appending its last entry. Forgetting its orderedCharacterLift
is the supplied iterate: the empty case is iterate_nil and the successor is
iterate_snoc, since the canonical shift-addition maps and ordinary shifts commute with
forgetting. Compose with the shifted augmentation. The augmented_component equation
of Lifts then identifies its sole component with (l.augmented a).val. All identifications
are sign-free reindexings; no tensor factors are permuted. This includes the empty list,
where augmented_nil gives R.augmentation. No underived term is asserted projective.
-/
theorem exists_equivariant_character_lifts (R : Resolution A.toMon G)
    {F : InternalFunctions A} (B : BarDiagram (G := G) F)
    (l : Profinite.CondensedAction.InternalBarCharacter.Lifts R B) :
    ∃ e : RoofAugmentation R, ∃ he : QuasiIso e,
      augmentationEquation R e ∧
      ∃ L : Character A G → (complex R ⟶ (complex R)⟦(1 : ℤ)⟧),
        (∀ a : Character A G, IsCharacterLift R a (L a)) ∧
        ∀ a : List (Character A G),
          (augmentedRoofComponent R e a.length
            (orderedCharacterLift R a.length (fun i ↦ L (a.get i)))).val =
              (l.augmented a).val := by sorry

end CategoryTheory.CondensedBar.OrderedCup
