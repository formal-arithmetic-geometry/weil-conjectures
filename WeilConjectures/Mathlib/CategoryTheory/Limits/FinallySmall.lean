/-
Copyright (c) 2026 Orchestra Agent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Orchestra Agent
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.CategoryTheory.Filtered.FinallySmall
public import Mathlib.CategoryTheory.Functor.Flat

/-!

# Colimits over the comma categories of a pointwise left Kan extension

The pointwise left Kan extension of a presheaf along `F.op`, for `F : C ⥤ D`, is computed by
colimits over the comma categories `CostructuredArrow F.op K`. These are almost never
essentially small — see `AlgebraicGeometry.Scheme.Etale` for the motivating example — so the
usual `EssentiallySmall` hypothesis is unavailable, and the colimits have to be produced from
Mathlib's weaker `CategoryTheory.FinallySmall` instead.

This file records the resulting transfer: `w`-initial smallness of the *structured* arrow
categories `StructuredArrow V F` — where the geometry lives — gives `w`-final smallness of the
*costructured* arrow categories over `F.op`, hence the colimits, and, when `F` is representably
flat, their exactness in an `AB5` target.

## Main results

- `CategoryTheory.finallySmall_costructuredArrow_op`: transfer of smallness across
  `CategoryTheory.structuredArrowOpEquivalence`.
- `CategoryTheory.Limits.hasColimitsOfShape_costructuredArrow_op_of_initiallySmall`.
- `CategoryTheory.Limits.hasExactColimitsOfShape_costructuredArrow_op_of_initiallySmall`.

-/

@[expose] public section

universe w v₁ v₂ v u₁ u₂ u

namespace CategoryTheory

open Limits Opposite

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- If the structured arrow categories of `F : C ⥤ D` are `w`-initially small, then the comma
categories indexing the pointwise left Kan extensions along `F.op` are `w`-finally small.

This is `CategoryTheory.structuredArrowOpEquivalence` together with the fact that
`InitiallySmall.{w} J` gives `FinallySmall.{w} Jᵒᵖ`. -/
theorem finallySmall_costructuredArrow_op (F : C ⥤ D) (K : Dᵒᵖ)
    [InitiallySmall.{w} (StructuredArrow K.unop F)] :
    FinallySmall.{w} (CostructuredArrow F.op K) :=
  finallySmall_of_final_of_finallySmall (structuredArrowOpEquivalence F K.unop).functor

namespace Limits

/-- The colimits computing the pointwise left Kan extension along `F.op` exist as soon as the
structured arrow categories of `F` are `w`-initially small and the target has `w`-small
colimits. This replaces the usual `EssentiallySmall` hypothesis, which is unavailable for the
small étale site. -/
theorem hasColimitsOfShape_costructuredArrow_op_of_initiallySmall (F : C ⥤ D) (K : Dᵒᵖ)
    [InitiallySmall.{w} (StructuredArrow K.unop F)]
    (A : Type u) [Category.{v} A] [HasColimitsOfSize.{w, w} A] :
    HasColimitsOfShape (CostructuredArrow F.op K) A :=
  haveI := finallySmall_costructuredArrow_op F K
  hasColimitsOfShape_of_finallySmall _ _

/-- Those same colimits are exact in an `AB5` target, provided `F` is representably flat: the
comma categories are then filtered, so a *filtered* small final model exists and `AB5` applies
to it. -/
theorem hasExactColimitsOfShape_costructuredArrow_op_of_initiallySmall (F : C ⥤ D)
    [RepresentablyFlat F] (K : Dᵒᵖ) [InitiallySmall.{w} (StructuredArrow K.unop F)]
    [LocallySmall.{w} (CostructuredArrow F.op K)]
    (A : Type u) [Category.{v} A] [HasFiniteLimits A] [HasColimitsOfSize.{w, w} A]
    [HasFilteredColimitsOfSize.{w, w} A] [AB5OfSize.{w, w} A] :
    haveI : HasColimitsOfShape (CostructuredArrow F.op K) A :=
      hasColimitsOfShape_costructuredArrow_op_of_initiallySmall F K A
    HasExactColimitsOfShape (CostructuredArrow F.op K) A :=
  haveI : RepresentablyCoflat F.op := (representablyCoflat_op_iff F).2 inferInstance
  haveI : IsFiltered (CostructuredArrow F.op K) := RepresentablyCoflat.filtered (F := F.op) K
  haveI : FinallySmall.{w} (CostructuredArrow F.op K) := finallySmall_costructuredArrow_op F K
  haveI : HasColimitsOfShape (CostructuredArrow F.op K) A :=
    hasColimitsOfShape_costructuredArrow_op_of_initiallySmall F K A
  hasExactColimitsOfShape_of_final _
    (FinallySmall.fromFilteredFinalModel.{w} (CostructuredArrow F.op K))

end Limits

end CategoryTheory
