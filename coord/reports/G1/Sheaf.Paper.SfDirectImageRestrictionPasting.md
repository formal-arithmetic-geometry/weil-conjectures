## What changed

Filled `WeilConjectures.sfDirectImageRestriction_pasting` in
`Sheaf.Paper.SfDirectImageRestrictionPasting`, without changing its statement.
Added the proof-only import
`import all Sheaf.TraceFormula.CompactSupportDirectImageRestrictionTransition`
to reuse its proved private generic `derived_transition` helper. Its normalization
calculation already handles exact restrictions that need not preserve K-injectives.

Proved private helpers handle representative formulas, section identities, inverse
cancellation, and the abstract derived triangle. The ordinary compatibility follows
from `d.sections` and the two canonical completed comparison characterizations.
Equality induction proves that inverse restriction compositors act as identity on
sections, including after applying an arbitrary functor; this avoids unfolding
completed pushforward on a transport map. The three normalization inputs come from
`d.normalization` and `sfDerivedRestrictionComparison_existsUnique`. The general
transition equation, applied with base level n and targets completed and level n+1,
then gives the required pasting equality by inverse cancellation.

Updated the item's DAG proof and proof dependencies to record this route. No existing
module besides the assigned item is changed. Both public imports remain necessary
for the unchanged statement; the new import is private to this proof.

Validation: the final module compiles through `lcompile.py` in 20.1 seconds,
with no warnings and no remaining `sorry`s. Its public statement matches the
original verbatim; all Lean lines meet the 100-character limit.

## Proved and sorry left

Closed the single existing hole in
`WeilConjectures.sfDirectImageRestriction_pasting`
(node `lem-sf-direct-image-restriction-pasting`).
The item's actual hole count is zero. No holes added; no statements split off.
All private helpers have complete proofs.

## No longer needed

No modules withdrawn and no imports removed. The separately attached
`lem-weil-proetale-direct-image-restriction-of-scalars` is not directly applied by
this proof: the canonical completed comparison and the supplied finite comparison
already give the needed normalizations. It is removed from this node's direct
proof dependencies, while its declarations and transitive uses remain intact.
The needed comparison construction is retained through `SfDerivedDirectImage`.

The proved generic helper of `lem-trf-direct-image-restriction-transition` is used
as a categorical tool, without changing a unit's route or adding any new obligation.

## Where the brief, the DAG or earlier work was wrong

Direct concrete calculations triggered kernel timeouts while converting equivalent
coefficient-category interfaces. The proof now combines the ordinary square and
the derived triangle while the coefficient sheaves remain abstract, then specializes
them through two private proof-valued definitions whose propositions are inferred.
This preserves shared interfaces instead of restating expanded concrete types.
The compositor representative formulas are also applied before specialization.
Both private definitions are fully proved; the localized `linter.defProp` settings
only permit this presentation. No shared definition, statement, instance or public
import is changed. Local irreducibility attributes keep large implementations behind
their APIs; no compile-time or heartbeat limit is raised.

No statement error found. The running server queue lists this as an ordinary
one-hole proof item, with no rework row or build-error record. The planned
resolution comparison does not require another split: an existing proved generic
transition calculation supplies it. The proof works for all n, including zero,
and arbitrary B; it introduces neither a completed input object nor a coefficient
reduction morphism, and never asserts preservation of K-injectives by restriction.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.SfDirectImageRestrictionPasting": "53dd2c27123c63a5fea18630ee116fa1d5c1eddc"}, "results": {"Sheaf.Paper.SfDirectImageTransitionPresentation": {"hash": "e3b1598fc1cb45d2780c26ab5d8969b09ab4cecd", "status": "OK"}}, "seconds": 71, "time": "2026-10-28T03:30:34+0800", "transitive": 0, "version": 1}
```

## Second reading by G1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
