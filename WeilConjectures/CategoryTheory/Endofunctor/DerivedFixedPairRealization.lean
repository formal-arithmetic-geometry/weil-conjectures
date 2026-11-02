/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Endofunctor.CyclicDerivedHomData
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebra
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
public import Mathlib.CategoryTheory.Triangulated.TStructure.Heart
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import WeilConjectures.CategoryTheory.SmoothBaseChange.CohomologyInWeakSerreSubcategory
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-! # Derived realization of fixed pairs

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-def-sf-weil-complexes/_section.md, Complement, derived-to-strict comparison,
equivalence on hearts, and Jordan extension warning.
(blueprint: lem-pur-derived-fixed-pair-realization)

## Main definitions and statements

The source and target properties specify bounded cohomology in the given weak Serre class.
`derivedFixedPairRealization` states the canonical realization, its compatibility with
representatives and shifts, its equivalence on hearts, and its failure of faithfulness
in the presence of an underlying split but equivariantly nonsplit extension.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w wB

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Endofunctor.IsoAlgebra

variable {A : Type u} [Category.{v} A] [Abelian A]
  (P : A ⥤ A) [P.Additive] [P.IsEquivalence]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{wB} (IsoAlgebra P)]

/-- Bounded native derived fixed pairs whose underlying cohomology belongs to S.
Source: blueprint latest, sk-def-sf-weil-complexes, Complement, native derived source.
(blueprint: lem-pur-derived-fixed-pair-realization) -/
def fixedPairRealizationSource (S : ObjectProperty A) :
    ObjectProperty (DerivedCategory (IsoAlgebra P)) :=
  DerivedCategory.homologyProperty (S.inverseImage (forget P)) ⊓
    DerivedCategory.TStructure.t.bounded

end CategoryTheory.Endofunctor.IsoAlgebra
