/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Submission.WeilConjectures.AlgebraicGeometry.CechCapPresheafLocalIso

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Positive-degree signed insertion before sheafification

Source: Stacks Project, Tags 02FU and 01FM.
(blueprint: lem-pc-s3-alternating-cech-presheaf-positive-insertion).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry

namespace CechInsertion
noncomputable section

open Limits Opposite in
private noncomputable def capIntoCap {X : Scheme.{u}} (G : X.Modules)
    (W Z Y : X.Opens) (h : W ⊓ Z ≤ Y) :
    cechCapModule G Y ⟶ (cechCapPresheafFunctor W).obj (cechCapModule G Z) where
  app V := ModuleCat.ofHom
    (X := (cechCapModule G Y).obj V)
    (Y := ((cechCapPresheafFunctor W).obj (cechCapModule G Z)).obj V)
    { toFun := fun s ↦ G.val.map (homOfLE (show (V.unop ⊓ W) ⊓ Z ≤ V.unop ⊓ Y by
        rw [inf_assoc]; exact inf_le_inf_left _ h)).op s
      map_add' := by intros; simp
      map_smul' := by
        intro a s
        change G.val.map
            (homOfLE (show (V.unop ⊓ W) ⊓ Z ≤ V.unop ⊓ Y by
              rw [inf_assoc]; exact inf_le_inf_left _ h)).op
            ((X.ringCatSheaf.obj.map
              (homOfLE (inf_le_left : V.unop ⊓ Y ≤ V.unop)).op a) •
                (show G.val.obj (op (V.unop ⊓ Y)) from s)) =
          (X.ringCatSheaf.obj.map
            (homOfLE (inf_le_left : (V.unop ⊓ W) ⊓ Z ≤ V.unop ⊓ W)).op
              (X.ringCatSheaf.obj.map
                (homOfLE (inf_le_left : V.unop ⊓ W ≤ V.unop)).op a)) •
            G.val.map
              (homOfLE (show (V.unop ⊓ W) ⊓ Z ≤ V.unop ⊓ Y by
                rw [inf_assoc]; exact inf_le_inf_left _ h)).op s
        rw [PresheafOfModules.map_smul]
        congr 1
        rw [← RingCat.comp_apply, ← RingCat.comp_apply, ← Functor.map_comp,
          ← Functor.map_comp]
        rfl }
  naturality := by
    intro V T f
    ext s
    change G.val.map
        (homOfLE (show (T.unop ⊓ W) ⊓ Z ≤ T.unop ⊓ Y by
          rw [inf_assoc]; exact inf_le_inf_left _ h)).op
        (G.val.map (homOfLE (inf_le_inf_right Y (leOfHom f.unop))).op s) =
      G.val.map
        (homOfLE (inf_le_inf_right Z (inf_le_inf_right W (leOfHom f.unop)))).op
          (G.val.map (homOfLE (show (V.unop ⊓ W) ⊓ Z ≤ V.unop ⊓ Y by
            rw [inf_assoc]; exact inf_le_inf_left _ h)).op s)
    rw [← PresheafOfModules.map_comp_apply, ← PresheafOfModules.map_comp_apply]
    rfl

/- Insert an absent index into the finite ordered range of a tuple.
Source: Stacks 01FM, ordered indices; 02FU, insertion. -/
open Limits Opposite in
private def insertTuple {r n : ℕ} (a : Fin n ↪o Fin r) (i : Fin r)
    (hi : i ∉ Set.range a) : Fin (n + 1) ↪o Fin r :=
  (insert i (Finset.univ.map a.toEmbedding)).orderEmbOfFin (by
    rw [Finset.card_insert_of_notMem, Finset.card_map, Finset.card_fin]
    simpa only [Finset.mem_map, Finset.mem_univ, true_and,
      RelEmbedding.coe_toEmbedding, Set.mem_range]
      using hi)

/- The sign exponent is the number of tuple entries strictly before the inserted index.
Source: Stacks 01FM, ordered signs; 02FU, insertion. -/
open Limits Opposite in
private def position {r n : ℕ} (a : Fin n ↪o Fin r) (i : Fin r) : ℕ :=
  (Finset.univ.filter fun j ↦ a j < i).card

open Limits Opposite in
private theorem intersection_insert_le {X : Scheme.{u}} {r n : ℕ}
    (U : Fin r → X.Opens) (a : Fin (n + 1) ↪o Fin r) (i : Fin r)
    (hi : i ∉ Set.range a) :
    U i ⊓ alternatingCechIntersection U a ≤
      alternatingCechIntersection U (insertTuple a i hi) := by
  apply le_iInf
  intro j
  have hj := Finset.orderEmbOfFin_mem
    (insert i (Finset.univ.map a.toEmbedding))
    (show (insert i (Finset.univ.map a.toEmbedding)).card = (n + 1) + 1 from by
      rw [Finset.card_insert_of_notMem, Finset.card_map, Finset.card_fin]
      simpa only [Finset.mem_map, Finset.mem_univ, true_and,
        RelEmbedding.coe_toEmbedding, Set.mem_range] using hi) j
  change insertTuple a i hi j ∈ insert i (Finset.univ.map a.toEmbedding) at hj
  rcases Finset.mem_insert.mp hj with h | h
  · rw [h]
    exact inf_le_left
  · rcases Finset.mem_map.mp h with ⟨k, _, hk⟩
    rw [← hk]
    exact inf_le_right.trans (iInf_le (fun k ↦ U (a k)) k)

/- One signed insertion coordinate, zero if the inserted index is already present.
Source: Stacks 02FU, increasing-tuple adaptation of 01FM. -/
open Limits Opposite in
private def coordinate {X : Scheme.{u}} {r : ℕ} (U : Fin r → X.Opens)
    (G : X.Modules) (i : Fin r) (q : ℕ) (a : Fin (q + 1) ↪o Fin r) :
    alternatingCechSheafPresheafTerms U G (q + 1) ⟶
      (cechCapPresheafFunctor (U i)).obj
        (cechCapModule G (alternatingCechIntersection U a)) :=
  if hi : i ∈ Set.range a then 0 else
    (-1 : ℤ) ^ position a i •
      (Pi.π _ (insertTuple a i hi) ≫
        capIntoCap G (U i) (alternatingCechIntersection U a)
          (alternatingCechIntersection U (insertTuple a i hi))
          (intersection_insert_le U a i hi))

/- Assemble signed insertion coordinates by the finite product comparison.
Source: Stacks 02FU, increasing-tuple adaptation of 01FM. -/
open Limits Opposite in
private def map {X : Scheme.{u}} {r : ℕ} (U : Fin r → X.Opens)
    (G : X.Modules) (i : Fin r) (q : ℕ) :
    alternatingCechSheafPresheafTerms U G (q + 1) ⟶
      (cechCapPresheafFunctor (U i)).obj (alternatingCechSheafPresheafTerms U G q) :=
  let K := cechCapPresheafFunctor (U i)
  let Q := fun a : Fin (q + 1) ↪o Fin r ↦
    cechCapModule G (alternatingCechIntersection U a)
  let : K.IsRightAdjoint :=
    inferInstanceAs (PresheafOfModules.pushforward (cechCapRingMap (U i))).IsRightAdjoint
  Pi.lift (coordinate U G i q) ≫ inv (piComparison K Q)

open Limits Opposite in
private theorem map_π {X : Scheme.{u}} {r : ℕ} (U : Fin r → X.Opens)
    (G : X.Modules) (i : Fin r) (q : ℕ) (a : Fin (q + 1) ↪o Fin r) :
    map U G i q ≫ (cechCapPresheafFunctor (U i)).map (Pi.π _ a) =
      coordinate U G i q a := by
  let K := cechCapPresheafFunctor (U i)
  let : K.IsRightAdjoint :=
    inferInstanceAs (PresheafOfModules.pushforward (cechCapRingMap (U i))).IsRightAdjoint
  dsimp only [map]
  rw [Category.assoc, inv_piComparison_comp_map_π, Pi.lift_comp_π]

/- The coordinate of insertion followed by the differential: its signed face sum.
Source: Stacks 02FU, ordered deletion calculation as in 01FM. -/
end
end CechInsertion

/- For a tuple already containing the inserted index, exactly its deletion survives.
Source: Stacks 02FU, insertion computation; increasing tuples as in 01FM.

Proof: Write i=a b. Every face other than b still contains i, so its insertion
coordinate is zero. The b face omits i; inserting it recovers a, in position b.
The two signs multiply to one. Restriction through the deleted face followed by
intersection with U i is just the cap unit on the a-coordinate. The other
insertion term is zero because a itself contains i. -/
/- Paired noncentral faces cancel on a tuple omitting the inserted index.
Source: Stacks 02FU, the displayed dh+hd computation; increasing tuples as in 01FM.

Proof: Enlarge a by inserting i in its unique position b. In d followed by
insertion at a, the face deleting b is the restriction of the a-coordinate,
since its two signs multiply to one. Each other face, indexed by b.succAbove j,
is the sorted insertion into the j-face of a. Its pivot position is j.predAbove b.
The two deletion orders agree by the succAbove identity. If j<b, the two sign
exponents are j+b-1 and j+b; otherwise they are j+b and j+b+1, so the terms are
negatives. The restrictions compose to the same map to G on V intersect U i
intersect the intersection of a. Summing the paired negatives leaves precisely
the cap unit of the a-coordinate. Empty intersections do not alter the argument;
if the tuple type is empty there is no coordinate to check. No covering condition
or sheafification is used. -/
end AlgebraicGeometry
