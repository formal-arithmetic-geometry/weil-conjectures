/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import WeilConjectures.FromJoel.Algebra.Homology.Embedding.ExtendMap

/-! # Additive functors and homology of extension by zero

Source: `HomologicalComplex.mapExtendIso` in
WeilConjectures/FromJoel/Algebra/Homology/Embedding/ExtendMap.lean and
`HomologicalComplex.extendHomologyIso` in Mathlib/Algebra/Homology/Embedding/ExtendHomology.lean.
(blueprint: lem-weil-pbc-map-extend-homology)
-/

@[expose] public noncomputable section

universe u v u' v'

open CategoryTheory CategoryTheory.Limits

/-- The canonical homology comparison for an additive functor and extension by zero.
Source: `HomologicalComplex.mapExtendIso` and `HomologicalComplex.extendHomologyIso`.
(blueprint: lem-weil-pbc-map-extend-homology)

Construction: map the upstream extension comparison by degree-q homology, then
compose with the homology comparison for extension along `embeddingUpNat`.
This constructs the isomorphism directly, including q = 0, without choosing a
witness from an existence theorem or assuming the functor is exact. -/
def mapExtendHomologyIso
    {D : Type u} [Category.{v} D] [Abelian D]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    (E : D ⥤ B) [E.Additive] (K : CochainComplex D ℕ) (q : ℕ) :
    ((E.mapHomologicalComplex (.up ℤ)).obj
        (K.extend ComplexShape.embeddingUpNat)).homology (q : ℤ) ≅
      ((E.mapHomologicalComplex (.up ℕ)).obj K).homology q :=
  (HomologicalComplex.homologyFunctor B (.up ℤ) (q : ℤ)).mapIso
      (K.mapExtendIso ComplexShape.embeddingUpNat E) ≪≫
    ((E.mapHomologicalComplex (.up ℕ)).obj K).extendHomologyIso
      ComplexShape.embeddingUpNat (j := q) rfl

/-- Applying an additive functor to extension by zero does not change homology
in a nonnegative degree.
Source: `HomologicalComplex.mapExtendIso` in
WeilConjectures/FromJoel/Algebra/Homology/Embedding/ExtendMap.lean and Mathlib
`HomologicalComplex.extendHomologyIso` in Embedding/ExtendHomology.lean.
(blueprint: lem-weil-pbc-map-extend-homology)

Proof: Use the existing `HomologicalComplex.mapExtendIso` to identify E applied
to the integer extension with the integer extension of E applied to K. Additivity
supplies its required preservation of zero morphisms. Map this complex isomorphism
by degree-q homology and compose with `extendHomologyIso`.
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
  exact Nonempty.intro (mapExtendHomologyIso E K q)
