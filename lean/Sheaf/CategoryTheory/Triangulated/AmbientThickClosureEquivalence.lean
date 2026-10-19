/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q78
-/
module

public import Mathlib.CategoryTheory.Triangulated.Generators

/-!
# Transport of ambient thick closures

Source: the Weil conjectures blueprint, `sec-six-functors/sk-lem-sf-ctf-generation`,
proof, first paragraph, transport to the small pro-etale convention
(blueprint: lem-trf-ambient-thick-closure-equivalence).
Thick subcategories and their generated closures use the Mathlib interface recorded by
`pur9-def-thick`; adjoining `IsZero` to the seed includes the empty generating class.
-/

@[expose] public section

universe u v u' v'

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ObjectProperty

private theorem inverseImage_retracts
    {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    (P : ObjectProperty D) [P.IsStableUnderRetracts] (F : C ⥤ D) :
    (P.inverseImage F).IsStableUnderRetracts :=
  ⟨fun r h ↦ P.prop_of_retract (r.map F) h⟩

private theorem map_inclusion_retracts
    {C : Type u} [Category.{v} C]
    (A : ObjectProperty C) [A.IsStableUnderRetracts]
    (P : ObjectProperty A.FullSubcategory) [P.IsStableUnderRetracts] :
    (P.map A.ι).IsStableUnderRetracts := by
  constructor
  rintro X Y r ⟨Z, hZ, ⟨e⟩⟩
  let X' : A.FullSubcategory :=
    ⟨X, A.prop_of_retract r (A.prop_of_iso e Z.property)⟩
  let r' : Retract X' Z :=
    { i := A.homMk (r.i ≫ e.inv)
      r := A.homMk (e.hom ≫ r.r)
      retract := by ext; simp }
  exact ⟨X', P.prop_of_retract r' hZ, ⟨Iso.refl _⟩⟩

private theorem ambient_envelope_iff
    {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
    (A : ObjectProperty C) [A.IsTriangulated] [A.IsStableUnderRetracts]
    (S : ObjectProperty A.FullSubcategory) (K : A.FullSubcategory) :
    (S.map A.ι ⊔ IsZero).triangEnvelope K.obj ↔ (S ⊔ IsZero).triangEnvelope K := by
  let P := (S ⊔ IsZero).triangEnvelope
  let H := (S.map A.ι ⊔ IsZero).triangEnvelope
  have : (P.map A.ι).IsStableUnderRetracts := map_inclusion_retracts A P
  have : (H.inverseImage A.ι).IsStableUnderRetracts := inverseImage_retracts H A.ι
  have hHP : H ≤ P.map A.ι := by
    apply (triangEnvelope_le_iff (S.map A.ι ⊔ IsZero) (Q := P.map A.ι)).mpr
    refine sup_le ?_ (fun X hX ↦ (P.map A.ι).prop_of_isZero hX)
    rintro X ⟨Y, hY, ⟨e⟩⟩
    exact ⟨Y, (S ⊔ IsZero).le_triangEnvelope _ (Or.inl hY), ⟨e⟩⟩
  have hPH : P ≤ H.inverseImage A.ι := by
    apply (triangEnvelope_le_iff (S ⊔ IsZero) (Q := H.inverseImage A.ι)).mpr
    refine sup_le ?_ (fun X hX ↦ (H.inverseImage A.ι).prop_of_isZero hX)
    intro X hX
    exact (S.map A.ι ⊔ IsZero).le_triangEnvelope _
      (Or.inl (S.prop_map_obj A.ι hX))
  constructor
  · intro hK
    obtain ⟨L, hL, ⟨e⟩⟩ := hHP _ hK
    exact P.prop_of_iso (A.isoMk e) hL
  · exact hPH K

/-- Exact equivalences between full thick subcategories transport ambient thick closures.
Source: the Weil conjectures blueprint, `sec-six-functors/sk-lem-sf-ctf-generation`,
proof, first paragraph (blueprint: lem-trf-ambient-thick-closure-equivalence).

The final natural isomorphism specifies that the resulting equivalence is the restriction
of `E`, after including the two ambient closures in their ambient categories. The seed is
augmented by zero objects so that the statement also covers `S = ⊥`.

Proof plan:
1. Since `A` and `B` are thick and contain their respective generating classes, minimality
of the ambient thick closures puts these closures inside `A` and `B` (`pur9-def-thick`).
2. Relative closure in `A` equals ambient closure in `C`, and likewise for `B` in `D`:
induced distinguished triangles and shifts give the same operations. Ambient retracts
and isomorphisms first remain in `A` by thickness, and then belong to the relative closure
by fullness. Zero objects also agree up to isomorphism. Apply minimality both ways
(`pur9-def-thick`, `def-weil-triangulated-category`).
3. The inverse image of the relative closure in `B` under `E.functor` is thick: exactness
preserves zero, integer shifts and distinguished triangles; functoriality preserves
isomorphisms and retract equations. It contains `S`, proving the forward implication.
Apply the same reasoning to `E.inverse`; its inverse image contains `E(S)` by the unit
isomorphism. This proves the reverse implication, again using the unit isomorphism
(`pur9-def-thick`, `def-weil-triangulated-category`).
4. Use step 2 to obtain the ambient membership equivalence. Restrict the forward and
inverse functors, and restrict the unit and counit by fullness, to obtain the asserted
equivalence and its compatibility isomorphism (`pur9-def-thick`). The argument does not
choose a generator or split any idempotent, so empty classes and ambient categories
without idempotent completeness are included. -/
theorem ambient_thickClosure_equivalence
    {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
    {D : Type u'} [Category.{v'} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ (n : ℤ), (shiftFunctor D n).Additive] [Pretriangulated D] [IsTriangulated D]
    (A : ObjectProperty C) [A.IsTriangulated] [A.IsStableUnderRetracts]
    (B : ObjectProperty D) [B.IsTriangulated] [B.IsStableUnderRetracts]
    (E : A.FullSubcategory ≌ B.FullSubcategory)
    [E.functor.CommShift ℤ] [E.functor.IsTriangulated]
    [E.inverse.CommShift ℤ] [E.inverse.IsTriangulated]
    (S : ObjectProperty A.FullSubcategory) :
    ∃ hC : (S.map A.ι ⊔ IsZero).triangEnvelope ≤ A,
      (S.map (E.functor ⋙ B.ι) ⊔ IsZero).triangEnvelope ≤ B ∧
      (∀ K : A.FullSubcategory,
        (S.map A.ι ⊔ IsZero).triangEnvelope K.obj ↔
          (S.map (E.functor ⋙ B.ι) ⊔ IsZero).triangEnvelope (E.functor.obj K).obj) ∧
      ∃ e : (S.map A.ι ⊔ IsZero).triangEnvelope.FullSubcategory ≌
          (S.map (E.functor ⋙ B.ι) ⊔ IsZero).triangEnvelope.FullSubcategory,
        Nonempty (e.functor ⋙ (S.map (E.functor ⋙ B.ι) ⊔ IsZero).triangEnvelope.ι ≅
          ObjectProperty.ιOfLE hC ⋙ E.functor ⋙ B.ι) := by
  let HC := (S.map A.ι ⊔ IsZero).triangEnvelope
  let HD := (S.map (E.functor ⋙ B.ι) ⊔ IsZero).triangEnvelope
  let PA := (S ⊔ IsZero).triangEnvelope
  let PB := (S.map E.functor ⊔ IsZero).triangEnvelope
  have hC : HC ≤ A := by
    apply (triangEnvelope_le_iff (S.map A.ι ⊔ IsZero) (Q := A)).mpr
    refine sup_le ?_ (fun X hX ↦ A.prop_of_isZero hX)
    rintro X ⟨Y, _, ⟨e⟩⟩
    exact A.prop_of_iso e Y.property
  have hD : HD ≤ B := by
    apply (triangEnvelope_le_iff (S.map (E.functor ⋙ B.ι) ⊔ IsZero) (Q := B)).mpr
    refine sup_le ?_ (fun X hX ↦ B.prop_of_isZero hX)
    rintro X ⟨Y, _, ⟨e⟩⟩
    exact B.prop_of_iso e (E.functor.obj Y).property
  have hmap : (S.map E.functor).map B.ι = S.map (E.functor ⋙ B.ι) := by
    ext X
    constructor
    · rintro ⟨Y, ⟨Z, hZ, ⟨e⟩⟩, ⟨f⟩⟩
      exact ⟨Z, hZ, ⟨B.ι.mapIso e ≪≫ f⟩⟩
    · rintro ⟨Z, hZ, ⟨e⟩⟩
      exact ⟨E.functor.obj Z, S.prop_map_obj E.functor hZ, ⟨e⟩⟩
  have hA (K : A.FullSubcategory) : HC K.obj ↔ PA K :=
    ambient_envelope_iff A S K
  have hB (L : B.FullSubcategory) : HD L.obj ↔ PB L := by
    change (S.map (E.functor ⋙ B.ι) ⊔ IsZero).triangEnvelope L.obj ↔
      (S.map E.functor ⊔ IsZero).triangEnvelope L
    simpa only [hmap] using ambient_envelope_iff B (S.map E.functor) L
  have : (PB.inverseImage E.functor).IsStableUnderRetracts :=
    inverseImage_retracts PB E.functor
  have : (PA.inverseImage E.inverse).IsStableUnderRetracts :=
    inverseImage_retracts PA E.inverse
  have hf : PA ≤ PB.inverseImage E.functor := by
    apply (triangEnvelope_le_iff (S ⊔ IsZero) (Q := PB.inverseImage E.functor)).mpr
    refine sup_le ?_ (fun X hX ↦ (PB.inverseImage E.functor).prop_of_isZero hX)
    intro X hX
    exact (S.map E.functor ⊔ IsZero).le_triangEnvelope _
      (Or.inl (S.prop_map_obj E.functor hX))
  have hg : PB ≤ PA.inverseImage E.inverse := by
    apply (triangEnvelope_le_iff (S.map E.functor ⊔ IsZero) (Q := PA.inverseImage E.inverse)).mpr
    refine sup_le ?_ (fun X hX ↦ (PA.inverseImage E.inverse).prop_of_isZero hX)
    rintro X ⟨Y, hY, ⟨e⟩⟩
    exact PA.prop_of_iso (E.unitIso.app Y ≪≫ E.inverse.mapIso e)
      ((S ⊔ IsZero).le_triangEnvelope _ (Or.inl hY))
  have hmem (K : A.FullSubcategory) : HC K.obj ↔ HD (E.functor.obj K).obj := by
    rw [hA, hB]
    exact ⟨hf K, fun h ↦ PA.prop_of_iso (E.unitIso.app K).symm (hg _ h)⟩
  refine ⟨hC, hD, hmem, ?_⟩
  let F : HC.FullSubcategory ⥤ HD.FullSubcategory :=
    HD.lift (ιOfLE hC ⋙ E.functor ⋙ B.ι)
      (fun X ↦ (hmem ((ιOfLE hC).obj X)).mp X.property)
  have : F.EssSurj := by
    constructor
    intro Y
    let L : B.FullSubcategory := ⟨Y.obj, hD _ Y.property⟩
    have hL : HC (E.inverse.obj L).obj :=
      (hmem (E.inverse.obj L)).mpr
        (HD.prop_of_iso (B.ι.mapIso (E.counitIso.app L)).symm Y.property)
    exact ⟨⟨(E.inverse.obj L).obj, hL⟩,
      ⟨HD.isoMk (B.ι.mapIso (E.counitIso.app L))⟩⟩
  have : F.IsEquivalence := { }
  exact ⟨F.asEquivalence, ⟨Iso.refl _⟩⟩

end CategoryTheory.ObjectProperty
