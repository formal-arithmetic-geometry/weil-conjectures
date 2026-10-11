/-
Copyright (c) 2026 The Weil Conjectures Project Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero

/-!
# Properties of the terms of an extended complex

If all terms of `K` satisfy a property `P` which contains zero objects and is closed under
isomorphisms, then so do all terms of `K.extend e`.

A functor `F` preserving zero morphisms commutes with extending complexes:
`HomologicalComplex.mapHomologicalComplexObjExtendIso` is the isomorphism
`F(K.extend e) ≅ (F K).extend e`.
-/

@[expose] public section

namespace HomologicalComplex

open CategoryTheory Limits

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category* C] [HasZeroMorphisms C] [HasZeroObject C]

/-- If `P` contains zero objects and is closed under isomorphisms and all terms of `K` satisfy
`P`, then all terms of `K.extend e` satisfy `P`. -/
lemma prop_extend_X (P : ObjectProperty C) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
    {K : HomologicalComplex C c} (e : c.Embedding c') (hK : ∀ i, P (K.X i)) (i' : ι') :
    P ((K.extend e).X i') := by
  by_cases h : ∃ i, e.f i = i'
  · obtain ⟨i, hi⟩ := h
    exact P.prop_of_iso (K.extendXIso e hi).symm (hK i)
  · exact P.prop_of_isZero (K.isZero_extend_X e i' (by simpa using h))

namespace extend

variable {D : Type*} [Category* D] [HasZeroMorphisms D] [HasZeroObject D] (F : C ⥤ D)
  [F.PreservesZeroMorphisms] (K : HomologicalComplex C c)

/-- Auxiliary definition for `HomologicalComplex.mapHomologicalComplexObjExtendIso`. -/
noncomputable def mapXIso : ∀ (i : Option ι),
    F.obj (X K i) ≅ X ((F.mapHomologicalComplex c).obj K) i
  | some _ => Iso.refl _
  | none => IsZero.iso (F.map_isZero (isZero_X K rfl)) (isZero_X _ rfl)

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma mapXIso_hom_d (i j : Option ι) :
    (mapXIso F K i).hom ≫ d ((F.mapHomologicalComplex c).obj K) i j =
      F.map (d K i j) ≫ (mapXIso F K j).hom :=
  match i, j with
  | none, _ => by simp only [d_none_eq_zero, comp_zero, Functor.map_zero, zero_comp]
  | some i, some j => by
      dsimp [mapXIso, d]
      simp only [Category.id_comp, Category.comp_id]
      rfl
  | some _, none => by simp only [d_none_eq_zero', comp_zero, Functor.map_zero, zero_comp]

end extend

/-- A functor preserving zero morphisms commutes with extending complexes along an embedding
of complex shapes: `F(K.extend e) ≅ (F K).extend e`. -/
noncomputable def mapHomologicalComplexObjExtendIso {D : Type*} [Category* D]
    [HasZeroMorphisms D] [HasZeroObject D] (F : C ⥤ D) [F.PreservesZeroMorphisms]
    (K : HomologicalComplex C c) (e : c.Embedding c') :
    (F.mapHomologicalComplex c').obj (K.extend e) ≅
      ((F.mapHomologicalComplex c).obj K).extend e :=
  Hom.isoOfComponents (fun i' ↦ extend.mapXIso F K (e.r i'))
    (fun i' j' _ ↦ extend.mapXIso_hom_d F K (e.r i') (e.r j'))

end HomologicalComplex
