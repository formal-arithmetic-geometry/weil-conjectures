# CategoryTheory.adicBasisTower

## Reason

The recursive ofOpSequence construction made kernel checking the arbitrary transition-map formula cost about 29 seconds in isolation. Define the same quotient tower directly by factorPow and then apply constantSheaf. The objects and all reduction maps are unchanged.

## Old

```lean
def adicBasisTower (A : Type (max uC vC r)) [CommRing A] (t : A) :
    ℕᵒᵖ ⥤ Sheaf J RingCat.{max uC vC r} :=
  letI := adicBasisRingSheafify.{uC, vC, r} J
  Functor.ofOpSequence (X := fun n ↦ adicBasisResidue.{uC, vC, r} J A t n)
    (fun n ↦ (constantSheaf J RingCat.{max uC vC r}).map
      (RingCat.ofHom (Ideal.Quotient.factorPowSucc (Ideal.span {t}) (n + 1))))
```

## New

```lean
def adicBasisTower (A : Type (max uC vC r)) [CommRing A] (t : A) :
    ℕᵒᵖ ⥤ Sheaf J RingCat.{max uC vC r} :=
  letI := adicBasisRingSheafify.{uC, vC, r} J
  let Q : ℕᵒᵖ ⥤ RingCat.{max uC vC r} :=
    { obj := fun n ↦ RingCat.of (A ⧸ (Ideal.span {t}) ^ (n.unop + 1))
      map := fun f ↦ RingCat.ofHom (Ideal.Quotient.factorPow (Ideal.span {t})
        (Nat.succ_le_succ (leOfHom f.unop)))
      map_id := fun _ ↦ by ext x; rfl
      map_comp := fun _ _ ↦ by ext x; rfl }
  Q ⋙ constantSheaf J RingCat.{max uC vC r}
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.AdicBasisLimit | U3 | Own proof uses the explicit quotient reductions; the statement is unchanged. |

`tools/downstream.py Sheaf.CategoryTheory.AdicBasisLimit --uses adicBasisTower`
finds no downstream importers. The only textual uses are in the item module.
No other module is adapted. Definitions denote exactly the same sheaf and tower,
so no target statement or interpretation changes. Targets reached through this
node remain subject to the normal statement review.

## Status

landed 20261021T140932-L-2777046 2026-10-21 (merge of deliver/U3/Sheaf.CategoryTheory.AdicBasisLimit)
