/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-! # Additive functors and homology of extension by zero -/

@[expose] public noncomputable section

universe u v u' v'

open CategoryTheory CategoryTheory.Limits

private def mapExtendTermIso
    {D : Type u} [Category.{v} D] [Abelian D]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    (E : D ⥤ B) [E.Additive] (K : CochainComplex D ℕ) (i : Option ℕ) :
    E.obj (HomologicalComplex.extend.X K i) ≅
      HomologicalComplex.extend.X ((E.mapHomologicalComplex (.up ℕ)).obj K) i :=
  match i with
  | some _ => Iso.refl _
  | none => IsZero.iso (E.map_isZero (isZero_zero D)) (isZero_zero B)

private lemma mapExtendTermIso_comm
    {D : Type u} [Category.{v} D] [Abelian D]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    (E : D ⥤ B) [E.Additive] (K : CochainComplex D ℕ) (i j : Option ℕ) :
    E.map (HomologicalComplex.extend.d K i j) ≫ (mapExtendTermIso E K j).hom =
      (mapExtendTermIso E K i).hom ≫
        HomologicalComplex.extend.d ((E.mapHomologicalComplex (.up ℕ)).obj K) i j := by
  cases i <;> cases j <;>
    simp [mapExtendTermIso, HomologicalComplex.extend.d]

private def mapExtendComplexIso
    {D : Type u} [Category.{v} D] [Abelian D]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    (E : D ⥤ B) [E.Additive] (K : CochainComplex D ℕ) :
    (E.mapHomologicalComplex (.up ℤ)).obj (K.extend ComplexShape.embeddingUpNat) ≅
      ((E.mapHomologicalComplex (.up ℕ)).obj K).extend ComplexShape.embeddingUpNat :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i ↦ mapExtendTermIso E K (ComplexShape.embeddingUpNat.r i))
    (fun i j _ ↦ (mapExtendTermIso_comm E K
      (ComplexShape.embeddingUpNat.r i) (ComplexShape.embeddingUpNat.r j)).symm)

/-- Applying an additive functor to extension by zero does not change homology
in a nonnegative degree.
Source: Mathlib `HomologicalComplex.extend` in Embedding/Extend.lean and
`HomologicalComplex.extendHomologyIso` in Embedding/ExtendHomology.lean.
(blueprint: lem-weil-pbc-map-extend-homology)

Proof: An additive functor sends zero objects to zero objects. In a nonnegative
integer degree, the extension's term is canonically the original term, and in a
negative degree it is zero. These identifications, after applying E, give a
complex isomorphism between E(K extended by zero) and E(K) extended by zero.
For two nonnegative indices compatibility follows from `extend_d_eq` and
functoriality; if either index is negative both differentials are zero. Map this
complex isomorphism by degree-q homology and compose with `extendHomologyIso`.
At q=0 the incoming term of the integer complex is zero, while the natural-indexed
complex has zero incoming differential by its shape; this is exactly the boundary
case covered by `extendHomologyIso`. No exactness of E is used. -/
theorem mapExtendHomology_nonempty_iso
    {D : Type u} [Category.{v} D] [Abelian D]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    (E : D ⥤ B) [E.Additive] (K : CochainComplex D ℕ) (q : ℕ) :
    Nonempty
      (((E.mapHomologicalComplex (.up ℤ)).obj
          (K.extend ComplexShape.embeddingUpNat)).homology (q : ℤ) ≅
        ((E.mapHomologicalComplex (.up ℕ)).obj K).homology q) := by
  exact ⟨(HomologicalComplex.homologyFunctor B (.up ℤ) (q : ℤ)).mapIso
    (mapExtendComplexIso E K) ≪≫
      ((E.mapHomologicalComplex (.up ℕ)).obj K).extendHomologyIso
        ComplexShape.embeddingUpNat (j := q) rfl⟩
