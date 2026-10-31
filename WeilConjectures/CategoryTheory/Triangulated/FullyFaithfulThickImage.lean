/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Idempotents.Basic
public import Mathlib.CategoryTheory.Triangulated.Generators

/-!
# Thick essential images of fully faithful exact functors

Source: the Weil conjectures blueprint, `sec-six-functors-basics/sk-lem-sf-flat-model`,
proof, first paragraph and complement; the categorical essential-image argument extracted
in the DAG, using the idempotent-splitting criterion of Stacks Tag 09SH
(blueprint: lem-sfb-fully-faithful-thick-image).

The zero objects are adjoined to each generating class before taking `triangEnvelope`,
so the statement also includes the empty generating class.
-/

@[expose] public section

universe u v u' v'

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

/-- The essential image of a fully faithful exact functor with idempotent complete source
is thick and is generated thickly by the images of any thick generating class of the source.

Source: the Weil conjectures blueprint, `sec-six-functors-basics/sk-lem-sf-flat-model`,
proof, first paragraph and complement; categorical essential-image argument extracted in
this DAG node, with the splitting criterion of Stacks Tag 09SH
(blueprint: lem-sfb-fully-faithful-thick-image).

`IsTriangulated` expresses containment of zero and stability under integer shifts and
extensions. Together with stability under retracts, which also implies closure under
isomorphisms, this expresses thickness. The latter Mathlib class is type-valued, so its
existence is asserted with `Nonempty`. The essential image and the image of `G` use
Mathlib's isomorphism-invariant object properties. No smallness of `G` or splitting of
idempotents in the target is required.

Proof plan:
1. The essential image is closed under isomorphisms by composing its witnessing
isomorphisms. Exactness implies additivity, hence sends a zero object to a zero object.
The coherent integer-shift comparisons identify shifts of image objects with images
of shifted objects (`def-weil-triangulated-category`).
2. Given a distinguished triangle with first two vertices isomorphic to `F(X)` and
`F(Y)`, lift its first arrow by fullness. TR1 completes that lift to a distinguished
triangle in the source. Apply `F`, then TR3 with the endpoint isomorphisms. The third
component is an isomorphism by `lem-sf-triangle-morphism-iso` (Stacks Tag 014A).
Thus the essential image is cone-closed. Rotate twice and use shift stability to obtain
extension closure (`def-weil-triangulated-category`).
3. For a retract `i : Y ⟶ F(X)`, `r : F(X) ⟶ Y`, lift the idempotent `r ≫ i`
by fullness. Faithfulness makes its lift idempotent. Split it as `b ≫ a` in the source,
with `a ≫ b = 𝟙`. Then `i ≫ F(b)` and `F(a) ≫ r` are mutually inverse: their
composites reduce using the splitting equations and `i ≫ r = 𝟙`. This places `Y` in
the essential image and proves thickness. Only the source splitting assumption is used
(Stacks Tag 09SH).
4. For any thick target object property containing every `F(g)` with `G g`, its inverse
image under `F` is thick: use exactness for zero, shifts and distinguished triangles,
and functoriality for isomorphisms and retract equations. It contains `G`, so the
source generation hypothesis makes it all of the source. Isomorphism closure then
puts the entire essential image inside the chosen target property
(`def-weil-triangulated-category`).
5. Every `F(g)` is in the essential image. Its thickness and the preceding minimality
therefore identify it with the thick closure of these objects. Adjoining zero objects
to the seeds makes Mathlib's `triangEnvelope` precisely this smallest thick subcategory,
even for an empty class. No coproduct indexed by `G` is formed. -/
theorem essImage_thick_eq_triangEnvelope
    {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]
    [CategoryTheory.IsTriangulated C]
    {D : Type u'} [Category.{v'} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ (n : ℤ), (shiftFunctor D n).Additive] [Pretriangulated D]
    [CategoryTheory.IsTriangulated D]
    [IsIdempotentComplete C]
    (F : C ⥤ D) [F.Full] [F.Faithful] [F.CommShift ℤ] [F.IsTriangulated]
    (G : ObjectProperty C) (hG : (G ⊔ IsZero).triangEnvelope = ⊤) :
    F.essImage.IsTriangulated ∧ Nonempty F.essImage.IsStableUnderRetracts ∧
      F.essImage = (G.map F ⊔ IsZero).triangEnvelope := by
  have hret : F.essImage.IsStableUnderRetracts := by
    constructor
    rintro X Y r ⟨Z, ⟨e⟩⟩
    let s : Retract X (F.obj Z) := r.trans (Retract.ofIso e.symm)
    let p : Z ⟶ Z := F.preimage (s.r ≫ s.i)
    have hp : F.map p = s.r ≫ s.i := F.map_preimage _
    have hpp : p ≫ p = p := by
      apply F.map_injective
      simp only [F.map_comp, hp, Category.assoc, s.retract_assoc]
    obtain ⟨W, a, b, hab, hba⟩ := IsIdempotentComplete.idempotents_split Z p hpp
    have hmap : F.map b ≫ F.map a = s.r ≫ s.i := by
      rw [← F.map_comp, hba, hp]
    have hsplit : F.map a ≫ F.map b = 𝟙 (F.obj W) := by
      rw [← F.map_comp, hab, F.map_id]
    refine ⟨W, ⟨{
      hom := F.map a ≫ s.r
      inv := s.i ≫ F.map b
      hom_inv_id := ?_
      inv_hom_id := ?_ }⟩⟩
    · calc
        (F.map a ≫ s.r) ≫ s.i ≫ F.map b =
            F.map a ≫ (F.map b ≫ F.map a) ≫ F.map b := by
          simp only [Category.assoc, hmap]
        _ = 𝟙 (F.obj W) := by simp [← Category.assoc, hsplit]
    · calc
        (s.i ≫ F.map b) ≫ F.map a ≫ s.r = s.i ≫ (s.r ≫ s.i) ≫ s.r := by
          rw [Category.assoc, ← Category.assoc (F.map b), hmap]
        _ = 𝟙 X := by simp
  refine ⟨inferInstance, ⟨hret⟩, ?_⟩
  let H := (G.map F ⊔ IsZero).triangEnvelope
  have : (G.map F ⊔ IsZero).Nonempty := by
    open scoped ZeroObject in
      exact ⟨0, Or.inr (isZero_zero D)⟩
  have : (H.inverseImage F).IsStableUnderRetracts :=
    ⟨fun r h ↦ H.prop_of_retract (r.map F) h⟩
  have hH : (G ⊔ IsZero).triangEnvelope ≤ H.inverseImage F := by
    apply (ObjectProperty.triangEnvelope_le_iff (G ⊔ IsZero)
      (Q := H.inverseImage F)).mpr
    refine sup_le ?_ (fun X hX ↦ (H.inverseImage F).prop_of_isZero hX)
    intro X hX
    exact (G.map F ⊔ IsZero).le_triangEnvelope _ (Or.inl (G.prop_map_obj F hX))
  apply le_antisymm
  · rintro X ⟨Y, ⟨e⟩⟩
    exact H.prop_of_iso e (hH Y (by rw [hG]; trivial))
  · apply (ObjectProperty.triangEnvelope_le_iff (G.map F ⊔ IsZero)
      (Q := F.essImage)).mpr
    refine sup_le ?_ (fun X hX ↦ F.essImage.prop_of_isZero hX)
    rintro X ⟨Y, _, ⟨e⟩⟩
    exact ⟨Y, ⟨e⟩⟩

end CategoryTheory.Functor
