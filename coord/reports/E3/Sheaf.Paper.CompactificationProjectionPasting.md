## What changed

Proved `CategoryTheory.SuppliedExchangeProjection.CompactificationPastingData.compactification_pasting`
in `Sheaf.Paper.CompactificationProjectionPasting`, with its statement and all definitions unchanged.
The calculation follows the node's seven steps: open comparison naturality and tensor interchange,
proper-exchange naturality, the two factor hypotheses, and first-variable projection naturality.
The final two clauses use endpoint naturality of the supplied diagram maps and functorial congruence.
Single-file compilation passes without warnings after removing the unused proof imports.
The node records the smaller proof dependency set and withdraws its obsolete tool-use approval.

## Proved and sorry left

Closed 1 of 1 original holes:
`CategoryTheory.SuppliedExchangeProjection.CompactificationPastingData.compactification_pasting`
(blueprint: `lem-sf-pf-compactification-pasting`). Zero holes remain in the module.
Zero holes added and zero statements split off. This is a proof, not a decomposition.

## No longer needed

Removed proof imports `Sheaf.Paper.SixFunctorDatum` and
`Sheaf.Paper.DerivedPullbackTensorIso`. No declaration from either is needed: the theorem is
conditional on the supplied functors, natural transformations, isomorphisms, and factor identities.
The supplied-domain definitions in `Sheaf.Paper.ExchangeProjectionSuppliedDomains` remain needed.

Pruned proof dependency `lem-pur-derived-pullback-tensor-iso` and its obsolete `tool_uses` entry.
The endpoint naturality clause follows directly from naturality of the supplied chain morphisms;
it does not require constructing geometric diagram maps or proving pullback-tensor coherence.
`def-sf-datum` remains a conceptual statement dependency; its Lean module is not imported by this
formal conditional proof. No unit statement or step is bypassed, and no module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The earlier proof-dependency import of `DerivedPullbackTensorIso` was unnecessary for this
conditional statement: naturality is already part of the supplied natural transformations and
diagram morphisms. No false statement or definition repair was needed. All existing signatures,
visibility, and docstrings are unchanged. Edge cases include identity comparisons and
noninvertible proper exchange and projection; the proof never inverts either of those maps.

## Second reading by E3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
