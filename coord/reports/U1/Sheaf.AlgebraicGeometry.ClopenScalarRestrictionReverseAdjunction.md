## What changed

Proved `AlgebraicGeometry.Scheme.clopenScalarRestrictionReverseAdjunction` from
`SheafOfModules.ClopenComparisonTensorSquare.clopen_reverse_module_adjunction`
in ordinary mode. Reused the existing private `proEtaleScalarEquivalence`
through a proof-only `import all`, identified the composed restriction functor
by the identity maps on sections, and transported the reverse adjunction using
`Adjunction.leftAdjointUniq`.

Preserved the original theorem signature, header, public imports and docstrings.
The new imports are proof-only; no existing definition or target statement changes.

## Proved and sorry left

Closed the one assigned hole:
`AlgebraicGeometry.Scheme.clopenScalarRestrictionReverseAdjunction`
(node `lem-cbc-clopen-scalar-restriction-reverse-adjunction`).
No sorry remains in the delivered module; no holes added or split off.
The proof uses the existing reverse clopen module adjunction, whose own hole
remains outside this delivery.

## No longer needed

None. The proof implements the existing node's planned dependency and formal
scalar transport. No dependency nodes, modules or imports are withdrawn.
The clopen tool from `sk-rem-sf-pf-done` remains needed as already recorded in
the node; the unit's route is unchanged.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction. The scalar transport requires no further split:
the existing scalar equivalence, identity sectionwise comparison and adjunction
uniqueness supply every step, including the empty-open case without additional
hypotheses. The shared checkout refreshed during the session; the final file is based on
the refreshed original source, with only proof imports and the proof changed.

## Second reading by U1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
