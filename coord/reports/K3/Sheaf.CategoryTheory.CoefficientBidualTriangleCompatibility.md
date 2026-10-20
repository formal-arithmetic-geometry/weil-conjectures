## What changed

Proved `CategoryTheory.CoefficientBidual.subcategory_linearity` directly from the
recorded closed tensor–Hom structure and the central scalar hypothesis. Proved private
helpers establish tensor additivity from adjunction, tensor linearity from the unit
action and monoidal coherence, and contravariant Hom linearity by transposing natural
evaluation. Applying Hom twice and taking underlying full-subcategory morphisms gives
the original statement without new hypotheses.

Updated proof step 11 in the node to this shorter argument. Added two private Mathlib
proof imports. Existing public declarations, definitions and imports are unchanged. The change record
`coord/changes/K3-coefficient-bidual-linearity-proof-scopes.md` documents the scoped
proof commands and consumer check.

## Proved and sorry left

Closed: `CategoryTheory.CoefficientBidual.subcategory_linearity` (one of four original
holes). Added no holes; every new private helper is proved.

Remaining original holes: `CategoryTheory.CoefficientBidual.compatibility`,
`CategoryTheory.CoefficientBidual.slice_compatibility`, and
`CategoryTheory.CoefficientBidual.scalar_compatibility`.

Validation: the complete item compiles with `lcompile.py` in about ten seconds.

## No longer needed

The proof of step 11 needs no explicit Hom-complex or localization-fraction
calculation: the closed adjunction and natural evaluation suffice. No node or module
is withdrawn, since the unchanged shift, slice and scalar clauses still use the
remaining proof plan. No original imports were removed.

## Where the brief, the DAG or earlier work was wrong

The retained attempt made no reduction because it left all four original holes.
Its attempted use of an arbitrary shift structure also lacked a valid normalization
argument. That route and its draft nodes have been discarded. This packet closes the
actual linearity theorem using only proved helpers and leaves the other original
holes unchanged, as permitted for a module containing several holes.

## Second reading by K3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
