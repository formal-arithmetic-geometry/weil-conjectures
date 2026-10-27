# RepresentativeComposition

## Reason

The strict cochain theorem below completion coherence returns the existing coordinate data structure. Its original location would create an import cycle. Extract the structure verbatim into a shared API module.

## Old

In `Sheaf.Algebra.Homology.FiniteFreeCompletionExchangeCoherence`:

```lean
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
```

## New

The same declaration, verbatim, in `Sheaf.Algebra.Homology.RoosRepresentativeComposition`, publicly imported by the original module.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Algebra.Homology.FiniteFreeCompletionExchangeCoherence | B4 | public import retains every field and its original name |
| Sheaf.Algebra.Homology.FiniteFreeQuotientRoosHorizontalCoherence | B4 | new cochain theorem returns the existing data |

The downstream source search has no other occurrence of this declaration. The original target statement and all data fields stay unchanged.

## Status

landed 20261025T201357-L-2465468 2026-10-25 (merge of deliver/B4/Sheaf.Algebra.Homology.FiniteFreeCompletionExchangeCoherence)
