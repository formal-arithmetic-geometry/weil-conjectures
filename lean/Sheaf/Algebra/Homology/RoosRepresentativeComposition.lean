/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B4
-/
module

public import Sheaf.Algebra.Homology.FiniteFreeCompletionExchange
public import Sheaf.Algebra.Homology.ArithmeticRoosMap

/-! # Strict composition data for representative Roos comparisons -/

@[expose] public section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe xA xB xD yA yB yD
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.StrictTowerArithmetic
namespace CategoryTheory.PrincipalQuotientCompletion
attribute [local irreducible] roosF strictRoosMapOfSquare
/-- Strict coordinate coherence before inverting arithmetic restriction.
`restricted` is the second scalar comparison on the first arithmetic subsequence;
its finite-stage maps are precisely the selected finite-stage maps of `rb`.
The last two fields give the arithmetic square and weighted-block composition.
Source: Stacks 0941 and 0H9K, DAG proof steps 3--8
(blueprint: def-pur-roos-representative-composition). -/
structure RepresentativeComposition
    {A : Type xA} [Category.{yA} A] [Abelian A] [HasCountableProducts A]
    {B : Type xB} [Category.{yB} B] [Abelian B] [HasCountableProducts B]
    {D : Type xD} [Category.{yD} D] [Abelian D] [HasCountableProducts D]
    {E : A ⥤ B} [E.Additive] {F : B ⥤ D} [F.Additive] {G : A ⥤ D} [G.Additive]
    (α : E ⋙ F ≅ G)
    (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (Y : CochainComplex (ℕᵒᵖ ⥤ B) ℤ)
    (Z W : CochainComplex (ℕᵒᵖ ⥤ D) ℤ) (m : Z ⟶ W)
    (e f : ℕ) (he : 1 ≤ e)
    (ra : RepresentativeRoosComparison E X Y e)
    (rb : RepresentativeRoosComparison F Y Z f)
    (rba : RepresentativeRoosComparison G X W (e * f)) where
  /-- The second tensor/product comparison on the restricted source tower. -/
  restricted : RepresentativeRoosComparison F ((complexRestriction B e).obj Y) Z (e * f)
  /-- Reindexing selects the original quotient maps without a new unit multiplier. -/
  selected_quotients : ∀ n : ℕ,
    HEq (restricted.β.hom.app (op n)) (rb.β.hom.app ((index e).obj (op n)))
  /-- Equality of the actual chain maps, hence of both signed Roos product coordinates. -/
  coordinates :
    (F.mapHomologicalComplex (.up ℤ)).map ra.δ.hom ≫ restricted.δ.hom ≫
      roosF.map ((complexRestriction D (e * f)).map m) =
    (Functor.mapHomologicalComplexCompIso α (.up ℤ)).hom.app (roosF.obj X) ≫ rba.δ.hom
  /-- Arithmetic restriction of the second comparison's target. -/
  arithmetic : roosF.obj ((complexRestriction D f).obj Z) ⟶
    roosF.obj ((complexRestriction D (e * f)).obj Z)
  /-- Both coordinates use selection and the weighted finite-block sum. -/
  arithmetic_coordinates : HEq arithmetic
    (arithmeticRoosMap ((complexRestriction D f).obj Z) e he)
  /-- Additive scalar extension commutes with the specified arithmetic map. -/
  arithmetic_square :
    (F.mapHomologicalComplex (.up ℤ)).map ra.a ≫ restricted.δ.hom = rb.δ.hom ≫ arithmetic
  /-- Weighted blocks compose in exactly the order used by the coefficient tower. -/
  arithmetic_composition : rb.a ≫ arithmetic = restricted.a

end CategoryTheory.PrincipalQuotientCompletion
