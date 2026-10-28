## What changed

Corrected `datum_naturality_of_kflat` from the false claim that the input datum's swap
is natural on all derived objects.  It now states the required transport form: there
exists a replacement datum `A'` with the same ordinary tensor presentation, a re-chosen
biduality isomorphism, and an everywhere-natural signed swap.  The parent theorem
`datum_exists` was adapted to return this replacement datum.

## Statement corrected

The prior statement was false because `SignedSymmetry.representative` constrains swap
only at literal K-flat representatives.  The corrected existential statement permits
re-choosing the swap and the dependent biduality field while preserving the ordinary
presentation.  This is the transport formulation requested by reviewer C-f3ce5.

## Proved and sorry left

No holes were closed and no new holes were added in the assigned item.  The one hole
left is `WeilConjectures.RationalVerdier.datum_naturality_of_kflat`, in node
`lem-coef-rational-verdier-datum-naturality`; it is now a named transport obligation
with the corrected statement.  The adapted parent `datum_exists` is proved from this
corrected existential theorem.

## No longer needed

None.  `Sheaf.SixFunctors.RationalVerdierModels` remains required for the corrected
statement.  The K-flat localization theorem and its node remain needed by the parent.

## Where the brief, the DAG or earlier work was wrong

The earlier delivery treated the false original-datum naturality statement as merely a
commented diagnostic.  The reviewer correctly identified that the swap can be changed
on non-K-flat pairs without affecting the K-flat representative hypothesis.  The DAG
statement and proof route have been updated to the transported replacement-datum form.

## Forced adaptations

`Sheaf.SixFunctors.RationalVerdierDatum` (held by B6) was copied and adapted only at
`datum_exists`'s proof.  The old compiler-valid proof destructured
`datum_naturality_of_kflat` as a direct naturality proof for `A`; the corrected theorem
returns `⟨A', A'.ordinary = A.ordinary, hNatural⟩`, so the proof now unpacks that triple
and returns `⟨A', hNatural⟩`.  The public signature and target statement are unchanged.

## New nodes

None.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.SixFunctors.RationalVerdierDatum": "9309ef60e8b1bf7680468fec116328020967430e", "Sheaf.SixFunctors.RationalVerdierDatumNaturality": "f9ff79cebe43ccd1c872c099d2ca6e30b44b499c"}, "results": {}, "time": "2026-10-28T10:07:29+0800", "transitive": 0, "version": 1}
```

## Second reading by B2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
