/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q03
-/
module

public import Sheaf.Topology.ProfiniteCondensedRing
public import Mathlib.CategoryTheory.Monoidal.Mod
public import Sheaf.CategoryTheory.CondensedActionModule
public import Sheaf.CategoryTheory.CondensedInternalBarResolution
public import Sheaf.CategoryTheory.CondensedEquivariantBarData
public import Sheaf.CategoryTheory.CondensedUnipotentClass
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift
public import Mathlib.Algebra.Homology.Single
public import Sheaf.CategoryTheory.InternalBarCharacterData
import Sheaf.CategoryTheory.InternalBarCharacterDeletion
import Sheaf.CategoryTheory.InternalBarCharacterIteration
import Sheaf.CategoryTheory.InternalBarCharacterCocycles

/-! # Character lifts on the internal homogeneous bar

Source: blueprint, direct-image stability, paragraph (3), agent-written internal
homogeneous-bar normalization, proof steps 1--6
(blueprint: lem-sfb-internal-bar-character-lifts).

The underlying integer-indexed complex is constructed from the recorded resolution.
Equivariance is retained on its components in the recorded internal action category.
The specifications below are not choices of data from a postponed existence theorem.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open Profinite.CondensedAction Profinite.CondensedAction.InternalBar
open CategoryTheory.CondensedDerivedRestriction (Character)

namespace Profinite.CondensedAction.InternalBarCharacter

variable (A : CategoryTheory.CondensedBar.Ring.{u})
variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

variable {A G}

/-- The normalized chain lifts, ordered composites, augmented cocycles and coordinate comparison.
All maps are in the original internal module category; component equivariance is explicit.
Source: all clauses of paragraph (3)'s internal character calculation
(blueprint: lem-sfb-internal-bar-character-lifts). -/
structure Lifts (D : Resolution A.toMon G)
    {H : CategoryTheory.CondensedBar.InternalFunctions A}
    (B : CategoryTheory.CondensedBar.BarDiagram (G := G) H) where
  lift : Character A G → (complex D ⟶ (complex D)⟦(1 : ℤ)⟧)
  lift_spec : ∀ a, IsLift D a (lift a)
  lift_unique : ∀ (a : Character A G) (L : complex D ⟶ (complex D)⟦(1 : ℤ)⟧),
    IsLift D a L → L = lift a
  lift_zero : ∀ a, (lift a).f 0 = 0
  anticommutation : ∀ (a : Character A G) (n : ℕ),
    component D (lift a) (n + 1) ≫ (D.boundary n).val +
      (D.boundary (n + 1)).val ≫ component D (lift a) n = 0
  iterate : ∀ a : List (Character A G), complex D ⟶ (complex D)⟦(a.length : ℤ)⟧
  iterate_nil : iterate [] = (shiftFunctorZero (CochainComplex (Modules A.toMon) ℤ) ℤ).inv.app
    (complex D)
  iterate_snoc : ∀ (a : List (Character A G)) (b : Character A G),
    iterate (a ++ [b]) = iterate a ≫ (lift b)⟦(a.length : ℤ)⟧' ≫
      (shiftFunctorAdd' (CochainComplex (Modules A.toMon) ℤ) 1 (a.length : ℤ)
        ((a ++ [b]).length : ℤ) (by simp; omega)).inv.app (complex D)
  iterate_equivariant : ∀ (a : List (Character A G)) (n : ℕ),
    Equivariant (D.objects (n + a.length)) (D.objects n) (component D (iterate a) n)
  iterate_below : ∀ (a : List (Character A G)) (n : ℕ), n < a.length →
    (iterate a).f (-(n : ℤ)) = 0
  iterate_generator : ∀ (a : List (Character A G)) (n : ℕ) (S : Profinite.{u})
      (x : Fin (n + a.length + 1) → C(S, G)),
    onSections A.toMon (component D (iterate a) n) S
      (basis A.toMon G (n + a.length + 1) (D.objects (n + a.length))
        (D.freeIso (n + a.length)) S x) =
      (∏ k : Fin a.length, (a.get k).app S
        ((x ⟨k.val, by omega⟩)⁻¹ * x ⟨k.val + 1, by omega⟩)) •
        basis A.toMon G (n + 1) (D.objects n) (D.freeIso n) S
          (fun i ↦ x ⟨a.length + i.val, by omega⟩)
  augmentation : complex D ⟶
    (HomologicalComplex.single (Modules A.toMon) (.up ℤ) 0).obj (Mod.regular A.X)
  augmentation_zero : (termIso D 0).inv ≫ augmentation.f 0 ≫
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (Mod.regular A.X)).hom = D.augmentation.val
  augmented : ∀ a : List (Character A G),
    D.objects a.length ⟶ (trivial (R := A.toMon) (P := G)).obj (Mod.regular A.X)
  augmented_component : ∀ a, (augmented a).val =
    augmentedComponent D augmentation (iterate a)
  augmented_sole : ∀ (a : List (Character A G)) (i : ℤ), i ≠ -(a.length : ℤ) →
    (iterate a ≫ augmentation⟦(a.length : ℤ)⟧').f i = 0
  augmented_closed : ∀ a, D.boundary a.length ≫ augmented a = 0
  augmented_nil : augmented [] = D.augmentation
  cocycle : ∀ a : List (Character A G),
    (HomologicalComplex.single (Modules A.toMon) (.up ℤ) (a.length : ℤ)).obj
      (Mod.regular A.X) ⟶ CategoryTheory.CondensedBar.extend
        ((CategoryTheory.CondensedBar.cochains B).obj
          ((trivial (R := A.toMon) (P := G)).obj (Mod.regular A.X)))
  cocycle_formula : ∀ (a : List (Character A G)) (S : Profinite.{u})
      (r : CategoryTheory.CondensedBar.sectionRing A S) (T : Profinite.{u}) (f : T ⟶ S)
      (g : Fin a.length → C(T, G)),
    (H.evaluate (CategoryTheory.CondensedBar.power G a.length) S (Mod.regular A.X)
      (onSections A.toMon (cocycleComponent B (cocycle a)) S r)).val T f
        (CategoryTheory.CondensedBar.tupleMap g) =
      (InternalAbelianSheafModule.sectionRingSheaf
        (coherentTopology Profinite.{u}) A.X).obj.map f.op r *
          ∏ k : Fin a.length, (a.get k).app T (g k)
  coordinates : ∀ (a : List (Character A G)) (S : Profinite.{u})
      (x : Fin (a.length + 1) → C(S, G)),
    onSections A.toMon (augmented a).val S
      (basis A.toMon G (a.length + 1) (D.objects a.length) (D.freeIso a.length) S x) =
    (H.evaluate (CategoryTheory.CondensedBar.power G a.length) S (Mod.regular A.X)
      (onSections A.toMon (cocycleComponent B (cocycle a)) S (regularOne A.toMon S))).val
        S (𝟙 S) (CategoryTheory.CondensedBar.tupleMap
          (fun k ↦ (x k.castSucc)⁻¹ * x k.succ))

/-- Additive condensed characters have unique equivariant deletion lifts, whose ordered
iterates give precisely the ordered inhomogeneous product cocycles.
Source: blueprint direct-image stability, paragraph (3), internal bar calculation
(blueprint: lem-sfb-internal-bar-character-lifts).

Proof:
1. The free-module adjunction and generator detection of
lem-sfb-condensed-free-linearization-tensor extend the natural assignment
[g_0,...,g_n] to a(g_0^(-1)g_1)[g_1,...,g_n] uniquely and A-linearly.
The generator equivariance test of lem-sfb-condensed-group-algebra-exact-forgetful
applies since simultaneous left translation preserves g_0^(-1)g_1.
2. On generators, the two deletions at every position i >= 2 cancel with opposite
signs. The remaining coefficient is a_01 + a_12 - a_02 = 0 by additivity.
The degree-one and degree-zero endpoints are zero. This is d L + L d = 0,
hence a cochain map to P[1], whose shifted differential is -d.
3. Induct on the ordered list, appending one character. The shifted next lift
multiplies the current scalar by its character at the next successive ratio,
and deletes the first remaining vertex. Below the list length the map is zero;
the empty list is the identity and the empty product is 1.
4. The augmentation of lem-sfb-condensed-internal-bar-resolution is a chain map.
Compose its shift with the iterate: only degree -q survives, giving f_q and
f_q boundary_(q+1) = 0, with f_0 the original augmentation.
5. The slice evaluation of def-sfb-condensed-equivariant-bar-data turns the product
of character values into a natural section of internal functions and an A-linear
map A to U^q. To check it is closed, substitute h_0=1 and h_i=b_1...b_i.
Homogeneous deletion becomes the first dropping face, interior adjacent-product
faces and the last dropping face; the first coefficient action is trivial.
Thus its differential is f_q boundary_(q+1)=0. At q=0 it is 1-1=0.
6. Substituting b_i=g_(i-1)^(-1)g_i gives the displayed coordinate equality.
All operations and generators commute with every profinite restriction, so every
identity is natural on all slices. No projectivity or internal-Hom acyclicity is used.
-/
theorem exists_lifts (D : Resolution A.toMon G)
    {H : CategoryTheory.CondensedBar.InternalFunctions A}
    (B : CategoryTheory.CondensedBar.BarDiagram (G := G) H) : Nonempty (Lifts D B) := by
  classical
  choose L hL h_unique using (exists_unique_deletion (A := A) (G := G) D)
  have h := ordered_properties D L hL
  choose c hc using (exists_product_cocycle B)
  let f (a : List (Character A G)) :
      D.objects a.length ⟶ (trivial (R := A.toMon) (P := G)).obj (Mod.regular A.X) :=
    ⟨augmentedComponent D (barAugmentation D) (orderedIterate D L a),
      h.augmented_equivariant a⟩
  refine ⟨{
    lift := L
    lift_spec := hL
    lift_unique := fun a L' hL' ↦ h_unique a L' hL'
    lift_zero := fun a ↦ degreeOne_zero D (L a)
    anticommutation := h.anticommutation
    iterate := orderedIterate D L
    iterate_nil := orderedIterate_nil D L
    iterate_snoc := orderedIterate_snoc D L
    iterate_equivariant := h.equivariant
    iterate_below := h.below
    iterate_generator := h.generator
    augmentation := barAugmentation D
    augmentation_zero := barAugmentation_zero D
    augmented := f
    augmented_component := fun _ ↦ rfl
    augmented_sole := fun a i hi ↦ augmented_sole D a.length (orderedIterate D L a) i hi
    augmented_closed := ?_
    augmented_nil := ?_
    cocycle := c
    cocycle_formula := hc
    coordinates := ?_ }⟩
  · intro a
    apply Subtype.ext
    exact h.augmented_closed a
  · apply Subtype.ext
    exact h.augmented_nil
  · intro a S x
    change onSections A.toMon
      (augmentedComponent D (barAugmentation D) (orderedIterate D L a)) S
      (basis A.toMon G (a.length + 1) (D.objects a.length) (D.freeIso a.length) S x) = _
    rw [h.augmented_generator]
    rw [hc a S (regularOne A.toMon S) S (𝟙 S)
      (fun k ↦ (x k.castSucc)⁻¹ * x k.succ)]
    simp only [regularOne, map_one, one_mul]

end Profinite.CondensedAction.InternalBarCharacter
