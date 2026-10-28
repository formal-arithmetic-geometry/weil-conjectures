## What changed

In `Sheaf.SmoothPurity.TraceExistence`, added a proof-only import of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionUpperShriek`
and constructed the normalized trace for an open immersion in relative dimension zero.
The source is the current blueprint `def-pur-smooth-trace`, `det-sp-trace-basic` (1), (3),
and `sk-thm-purity-transport` Step 3.

The private `smoothTrace_zeroSourceIso` retains the supplied ambient zero-Tate and
zero-shift identification, lifting it through the full inclusion. The private
`smoothTrace_openOrientation` uses the actual open exceptional-unit comparison,
and `smoothTrace_openCounit` is its explicit exceptional counit composite.
No witness is selected from an existence assertion.

Proved all representing Hom bijections for that composite, uniqueness with the
specified adjunct, and its identification with the extension-by-zero counit through
the compactification comparison and the actual monoidal unit map. All added declarations
are private. Existing public signatures, definitions and source-library files are unchanged.
Updated the item's proof plan to distinguish this completed normalized subcase from
the unchanged false unnormalized conclusion.

## Proved and sorry left

Original holes closed: 0 of 1. New holes added: 0. Split off: 0.
The sole remaining hole is
`AlgebraicGeometry.ProEtale.CondensedRing.existsUnique_smoothTrace`
(node `lem-route-smooth-trace-representing-unique`).

Validation: `lcompile.py` compiled the complete module with no errors or warnings in
36.8 seconds. The added import passes `tools/import_direction.py may`.

New proved private theorems:
- `smoothTrace_openCounit_representing`;
- `existsUnique_smoothTrace_openNormalized`;
- `smoothTrace_openUnit_counit_formula`;
- `smoothTrace_openCounit_extensionByZero`.

The explicit construction works also for the empty source, identity open immersions,
ell = 2, and nontrivial changes of the supplied source orientation. It does not assert
that changing that orientation leaves the trace fixed: normalized uniqueness fixes the
actual adjunct, which is precisely the condition absent from the original theorem.

## No longer needed

None. No existing imports, nodes or modules are pruned. The general finite/integral and
condensed reconstruction route remains needed beyond the open case. The new proof import
is used by the canonical open comparison and the actual extension-by-zero counit formula.

## Where the brief, the DAG or earlier work was wrong

`STATEMENT-DISPUTED`: the public assertion of uniqueness among all representing traces is
false. The existing closed counterexample `smoothTrace_char_three_claim_false` and the
independent actual-functor theorem in `Sheaf.SmoothPurity.TraceNonuniqueness` already certify
this. They are preserved and no inconsistent theorem is used in the new proofs.
A sign change of a nonzero coefficient unit changes the representing trace while
preserving every Hom bijection. Uniqueness holds only after specifying the orientation
or natural Hom equivalence, as in the proved open-normalized theorem.

The adopted source `WeilConjectures.SmoothPurity.Defs` chooses its trace from the false
assertion, then uses its unnormalized uniqueness in the open-normalization theorem.
Changing only the assertion to plain existence cannot repair those consumers. The
source-library boundary forbids changing the non-sorry portion of that public definition;
this delivery therefore adds the valid explicit construction locally and preserves the
source and public theorem unchanged. No proof of the false assertion or hole reduction
is claimed. The current queue is a disputed proof item, not a zero-hole rework item;
no rework row or build-error file for this module is present in the shared snapshot.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.SmoothPurity.TraceExistence": "20aaba40db87304bf4a4ed78c089316061c50c37"}, "results": {"WeilConjectures.SmoothPurity.Defs": {"hash": "d391d1bf7bd8841478635f95d13251d0f22a130f", "status": "OK"}}, "seconds": 121, "time": "2026-10-28T14:11:49+0800", "transitive": 0, "version": 1}
```

## Second reading by C1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
