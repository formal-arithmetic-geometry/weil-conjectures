# CategoryTheory.adicBasisResidue

## Reason

Expose the existing constant quotient sheaf as an abbreviation. The term and its meaning are unchanged; this avoids repeated expensive unification of product objects through the wrapper.

## Old

```lean
def adicBasisResidue (A : Type (max uC vC r)) [CommRing A] (t : A) (n : ℕ) :
    Sheaf J RingCat.{max uC vC r} :=
  letI := adicBasisRingSheafify.{uC, vC, r} J
  (constantSheaf J RingCat.{max uC vC r}).obj
    (RingCat.of (A ⧸ (Ideal.span {t}) ^ (n + 1)))
```

## New

```lean
abbrev adicBasisResidue (A : Type (max uC vC r)) [CommRing A] (t : A) (n : ℕ) :
    Sheaf J RingCat.{max uC vC r} :=
  letI := adicBasisRingSheafify.{uC, vC, r} J
  (constantSheaf J RingCat.{max uC vC r}).obj
    (RingCat.of (A ⧸ (Ideal.span {t}) ^ (n + 1)))
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.AdicBasisLimit | U3 | Own proof uses the explicit quotient reductions; the statement is unchanged. |

`tools/downstream.py Sheaf.CategoryTheory.AdicBasisLimit --uses adicBasisResidue`
finds no downstream importers. The only textual uses are in the item module.
No other module is adapted. Definitions denote exactly the same sheaf and tower,
so no target statement or interpretation changes. Targets reached through this
node remain subject to the normal statement review.

## Status

landed 20261021T140932-L-2777046 2026-10-21 (merge of deliver/U3/Sheaf.CategoryTheory.AdicBasisLimit)
