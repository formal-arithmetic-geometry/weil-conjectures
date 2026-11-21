/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import WeilConjectures.FromJoel.Algebra.Homology.Embedding.ExtendMap

/-! # Additive functors and homology of extension by zero -/

@[expose] public noncomputable section

universe u v u' v'

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- Applying an additive functor to extension by zero does not change homology
in a nonnegative degree. -/
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

end CochainComplex
