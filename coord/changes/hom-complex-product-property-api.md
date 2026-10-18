# CategoryTheory.homComplex_isLimit

## Reason

The degree-map construction requires the product property of the chosen Hom complex.
Checking its existential specification after specialization to the one-object ring site
cost roughly 43 seconds in the kernel, and the delivery's axiom probe exceeded the
60-second file limit. Expose the already-proved product property at the generic site,
next to the definition. The caller then specializes a named theorem instead of
rechecking the nested dependent existential specification at the specialized site.
The original Hom-complex construction and every existing declaration remain unchanged.
This is an API lemma for an existing definition, not a new mathematical obligation or
an extra module splitting the proof. The original full proof and the revised construction
both remain in the assigned module.

## Old

There was no named `CategoryTheory.homComplex_isLimit` theorem. The product property
was available only as the first conjunct of
`(homComplex_exists (R := R)).choose_spec.choose_spec`.

## New

```lean
theorem homComplex_isLimit
    (L M : CochainComplex (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ) (n : ℤ) :
    Nonempty (IsLimit (Fan.mk ((homComplex (R := R) L M).X n)
      (fun p : ℤ ↦ (homComplex_exists (R := R)).choose_spec.choose
        L M n p (p + n) rfl))) :=
  (homComplex_exists (R := R)).choose_spec.choose_spec.1 L M n
```

All parameters, universe levels, definitions, existing signatures, existing proofs,
visibility, and imports of `Sheaf.Algebra.Homology.HomComplex` stay unchanged.
The node `def-pur-hom-complex` now records this additional declaration.
No target's mathematical meaning changes or requires a renewed statement review.

## Users

`tools/downstream.py Sheaf.Algebra.Homology.HomComplex --uses homComplex_isLimit`
reported 2006 transitive downstream modules and **zero existing users** of the newly
added name. None of their existing definitions or statements changes: no old constant
has changed. No consumer adaptation is required. The additional module is unclaimed
in the shared claim table; the assigned item is held by T3.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.HomComplex | unclaimed | Adds the fully proved generic API theorem. |
| Sheaf.Algebra.Homology.PerfectRingHomTensorDegreeMap | T3 | Uses the theorem for its existing selected-product fan. |

## Status

landed 20261018T071225-L-1678284 2026-10-18 (merge of deliver/T3/Sheaf.Algebra.Homology.PerfectRingHomTensorDegreeMap)
