/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import WeilConjectures.FromJoel.Algebra.Homology.BicomplexColumns
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap

/-! # Additive transport for uniformly bounded bicomplex totals

Source: WeilConjectures/FromJoel/Algebra/Homology/TotalComplexMap.lean,
BicomplexColumns.lean and CochainComplexMinus.lean
(blueprint: lem-sfb-left-resolution-additive-total-transport).
-/

@[expose] public section

universe uC vC uD vD

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex₂

/--
The canonical total-complex comparison attached to explicit total and preservation
structures.
Source: WeilConjectures/FromJoel/Algebra/Homology/TotalComplexMap.lean,
lines 117--145 (blueprint: lem-sfb-left-resolution-additive-total-transport).
-/
noncomputable def additiveTotalComparison
    {C : Type uC} [Category.{vC} C] [Preadditive C]
    {D : Type uD} [Category.{vD} D] [Preadditive D]
    (F : C ⥤ D) [F.Additive]
    (B : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    (hB : B.HasTotal (ComplexShape.up ℤ))
    (hP : F.PreservesTotalComplex B (ComplexShape.up ℤ)) :
    ((F.mapHomologicalComplex₂ (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj B).total
        (ComplexShape.up ℤ) ≅
      (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (B.total (ComplexShape.up ℤ)) := by
  letI := hB
  letI := hP
  exact HomologicalComplex₂.mapTotalIso F B (ComplexShape.up ℤ)

/--
Additive functors transport the total of an integer bicomplex bounded above in the
first index and in every column, in a preadditive category with a zero object and
finite coproducts. The comparison is natural for maps with independent bounds.
Source: WeilConjectures/FromJoel/Algebra/Homology/TotalComplexMap.lean,
BicomplexColumns.lean (line 746, the ambient `[HasFiniteCoproducts D]`; lines 874--912)
and CochainComplexMinus.lean
(blueprint: lem-sfb-left-resolution-additive-total-transport).

Proof.
1. For each diagonal, the support bounds leave only finitely many nonzero summands
(those with `n ≤ p ≤ b`; none when `n > b`), so the diagonal coproduct exists because
the category has finite coproducts, extended by zero maps on the zero summands; its
image under the additive functor is again a coproduct, since additive functors
preserve finite coproducts and send zero objects to zero objects.
This is the finite-coproduct argument of lem-sfb-left-resolution-additive-finite-coproducts.
2. The canonical comparison is additiveTotalComparison, which is the mapTotalIso of
lem-sfb-left-resolution-map-total-iso, and additivity makes it a chain isomorphism.
3. The hom and inverse naturality equations of mapTotalIso prove naturality for a
second bicomplex with any other first-index bound.
-/
theorem additive_total_transport
    {C : Type uC} [Category.{vC} C] [Preadditive C] [HasZeroObject C] [HasFiniteCoproducts C]
    {D : Type uD} [Category.{vD} D] [Preadditive D]
    (F : C ⥤ D) [F.Additive]
    (B : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    (b : ℤ)
    [CochainComplex.IsStrictlyLE B b]
    [∀ p : ℤ, CochainComplex.IsStrictlyLE (B.X p) 0] :
    ∃ (hB : B.HasTotal (ComplexShape.up ℤ))
      (hP : F.PreservesTotalComplex B (ComplexShape.up ℤ)),
      IsIso (additiveTotalComparison F B hB hP).hom ∧
      ∀ (B' : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
        (b' : ℤ) [CochainComplex.IsStrictlyLE B' b']
        [∀ p : ℤ, CochainComplex.IsStrictlyLE (B'.X p) 0]
        (φ : B ⟶ B'),
        ∃ (hB' : B'.HasTotal (ComplexShape.up ℤ))
          (hP' : F.PreservesTotalComplex B' (ComplexShape.up ℤ)),
          total.map ((F.mapHomologicalComplex₂ (ComplexShape.up ℤ)
            (ComplexShape.up ℤ)).map φ) (ComplexShape.up ℤ) ≫
              (additiveTotalComparison F B' hB' hP').hom =
            (additiveTotalComparison F B hB hP).hom ≫
              (F.mapHomologicalComplex (ComplexShape.up ℤ)).map
                (total.map φ (ComplexShape.up ℤ)) := by
  have hB : B.HasTotal (ComplexShape.up ℤ) := hasTotal_of_isStrictlyLE B b 0
  have hP : F.PreservesTotalComplex B (ComplexShape.up ℤ) :=
    preservesTotal_of_isStrictlyLE B b 0 F
  refine ⟨hB, hP, inferInstance, ?_⟩
  intro B' b' _ _ φ
  have hB' : B'.HasTotal (ComplexShape.up ℤ) := hasTotal_of_isStrictlyLE B' b' 0
  have hP' : F.PreservesTotalComplex B' (ComplexShape.up ℤ) :=
    preservesTotal_of_isStrictlyLE B' b' 0 F
  refine ⟨hB', hP', ?_⟩
  exact mapTotalIso_hom_naturality F φ (ComplexShape.up ℤ)

end HomologicalComplex₂
