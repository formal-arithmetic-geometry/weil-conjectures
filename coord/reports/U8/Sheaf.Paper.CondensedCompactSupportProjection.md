## What changed

The item module proves `fieldRefinementApp_naturality` from its existing
`fieldProperOpen_existsUnique` statement. A natural transformation constructs the original restriction normalization from
the same compositor and counit. Private helpers establish closure of bounded constructible complexes
under binary sums, and injectivity on the mixed Hom group by uniqueness at the
binary sum. The final proof applies proper direct image and the natural proper
compositor. The binary-sum proof imports the already proved
`Sheaf.Paper.ConstructibleCokernelsExtensions`. Proved tensor-colimit witness
instances and a generic counit-composition construction are attached to the
existing construction node; there are no new assumptions.
The node records this dependency and argument. The final version compiled cleanly in 49.3 seconds through `lcompile.py`.
Delivery validation includes the axiom probe.
Local irreducibility of the derived category's preadditive structure prevents
expansion of the localization's addition during generic uniqueness calculations.
The earlier delivery attempt failed its local timeout check and pushed nothing;
this packet includes the additional abstraction repair.

Local irreducibility of the sheaf and module tensor structures prevents
elaboration from expanding their constructions. Coefficient arguments in the
existing shift proof are explicit, and its mate and composition calculations use
proved generic private lemmas with the same shifts. Existing statement types are unchanged up to definitional equality. The restriction
and refinement component definitions now evaluate natural transformations, with
exactly the original compositor/counit formulas. Named presentations of the
original derived functors, adjunction and compositor are used consistently in
the refinement constructions and their signatures to reduce repeated checking.
The retained identity proofs use proved generic adjunction helpers. The change record is
`coord/changes/U8-condensed-refinement-naturality-proof-context.md`.

## Proved and sorry left

One of the six original holes is closed. The proved declaration is
`WeilConjectures.CompactSupportCondensedRealization.fieldRefinementApp_naturality`.
Five original holes remain, all at
`def-pur-condensed-compact-support-projection`:

- `WeilConjectures.CompactSupportCondensedRealization.condensedProjection_comp`;
- `WeilConjectures.CompactSupportCondensedRealization.condensedProjection_id`;
- `WeilConjectures.CompactSupportCondensedRealization.fieldProperOpen_existsUnique`;
- `WeilConjectures.CompactSupportCondensedRealization.condensedProjection_refinement`;
- `WeilConjectures.CompactSupportCondensedRealization.fieldRefinement_comp`.

No holes are added or split off. This is a partial delivery of the six-hole module.
The chosen comparison continues to use the original unique-existence theorem.

## No longer needed

None. The original proof dependencies and imports remain needed for the retained
proofs and constructions. No module is withdrawn and the blueprint unit route
is unchanged. The private binary-sum argument reuses constructible extension
closure, so a separate public binary-sum module is unnecessary and is not delivered.

## Where the brief, the DAG or earlier work was wrong

The naturality plan needs an injectivity argument after the transpose is composed
with the proper-open restriction. Uniqueness at a single diagonal object does not
directly supply injectivity between two different objects. Applying uniqueness
at their binary sum supplies precisely this missing argument without assuming
invertibility of the proper-open restriction.

At resumption the sandbox metadata recorded `.budget.start` as
2026-10-23T15:24:52Z, while the U8 item claim records
2026-10-23T12:29:44Z and the saved searches include work before that later start.
This packet is the same resumed U8 dispatch; no budget or launcher metadata was edited.

## Second reading by U8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
