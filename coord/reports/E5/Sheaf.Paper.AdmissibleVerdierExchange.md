## What changed

Restored the quarantined `lean/Sheaf/Paper/AdmissibleVerdierExchange.lean` and proved
`WeilConjectures.AdmissibleVerdierExchange.verdier_exchange` by restricting the existing
`WeilConjectures.VerdierExchange.verdier_exchange` all-stage package. The same unit,
stage data, actual epsilon, projection realization, normalized integral compositor,
and coefficient and signed-shift witnesses are retained. Admissibility proofs only
restrict the domains of the corresponding fields. Existing declaration signatures,
definitions, public imports and the target statements are unchanged.

Updated fix-cor-verdier-exchange's proof and proof dependencies to this actual route.
The invoked node sk-thm-sf-verdier-exchange is already a blueprint same_as entry for
this item. Its unit follows the same composition-mate/tensor-Hom argument; its full
DAG dependency closure does not reach fix-cor-verdier-exchange. This is reuse of an
existing stronger stated theorem, not a new restatement or a split-off obligation.
The independent reader should approve this use of the existing same_as theorem as
needed; no new tool approval has been written by this worker.

## Proved and sorry left

Closed 1 of 1 original holes:
`WeilConjectures.AdmissibleVerdierExchange.verdier_exchange`
(node fix-cor-verdier-exchange). No sorry remains in the delivered module. Added zero
holes and split off zero statements. The proof depends on the existing named theorem
`WeilConjectures.VerdierExchange.verdier_exchange`, whose proof remains sorry in the
library; this delivery does not claim an axiom-free proof of the whole dependency closure.

## No longer needed

Removed private imports `WeilConjectures.SixFunctors.Etale.Derived.Adjunctions`,
`Sheaf.Paper.BasicOperationsCoefficientReduction`, and
`Sheaf.Paper.CanonicalOriginCompactSupportComposition`. No public import was removed.

The item no longer directly needs the old proof dependencies
`def-weil-exceptional-inverse-image`, `fix-lem-tensor-adjunction`,
`fix-prop-adjunctions`, `lem-sf-adic-exceptional-compositor-coefficients`,
`lem-sf-admissible-hom-substitution`, `lem-sf-constructible-exceptional-compositor`,
and `lem-sf-finite-exceptional-compositor-coefficients`: their assembly is reused via
the already stated all-stage exchange. Several remain dependencies of that theorem
or of this module's definitions; none is claimed globally unnecessary or withdrawn.
Removed the item's obsolete direct tool_uses entries `lem-fix-operation-reduction`,
`lem-sf-constructible-exceptional-compositor`,
`lem-sf-finite-exceptional-compositor-coefficients`, and
`lem-sf-adic-exceptional-compositor-coefficients` for the same reason.
No module was withdrawn.

## Where the brief, the DAG or earlier work was wrong

The source is quarantined (coord/rework.tsv), rather than present under lean/. Its
entire archived interface was restored, not deleted or replaced by an empty module.
The original plan duplicated the existing unconditional all-stage exchange package;
restriction of that exact package suffices. The untouched archived source failed at its line 177 coefficient field with a
200000-heartbeat whnf timeout and a subsequent Package application error. The
revised proof compiled in 17.8 seconds; after removing unused private imports the
final module compiled without warnings in 16.9 seconds, within the unchanged limit.
Final validation is recorded by the delivery tool.

## Second reading by E5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
