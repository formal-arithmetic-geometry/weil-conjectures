## What changed

Proved `IsLocalRing.exists_dvr_subalgebra_same_fraction_field` with its original
signature. Import the existing dimension-one birational overring theorem, normalize
that overring using the proved upstream normalization theorem, choose a prime above
its maximal ideal by integral lying over, and localize at that nonzero prime.
Mathlib's `Localization.subalgebra` constructs the localization directly in the
prescribed field. Restrict scalars through the original ring inclusions; composition
of ideal comaps gives domination and `local_hom_TFAE` gives locality.
Updated the existing node's proof and proof dependencies to match the implementation.
No statement, definition, public import, or other module changed.

## Proved and sorry left

Closed 1 of 1 original holes:
`IsLocalRing.exists_dvr_subalgebra_same_fraction_field`
(node `lem-sfb-local-domain-same-field-dvr`).
No holes remain in the item; no holes added and no lemmas split off.
The proof uses the existing statement
`IsLocalRing.exists_birational_dimension_one_subalgebra`
(node `lem-sfb-local-domain-birational-dimension-one`), whose separate proof remains
unfinished in its own module. This delivery proves the assigned theorem from that
stated dependency, as required by stage 3.

## No longer needed

Removed proof import `WeilConjectures.RingTheory.DimOneResidueFieldsFinite` and
node dependency `lem-weil-pbc-dim-one-residue-field-extensions-finite`, together
with its obsolete top-level `tool_uses` approval. No maximality or residue-field
calculation is needed: the Dedekind localization theorem applies to every nonzero
prime. This is pruning only from this item's proof; no source declaration or module
is withdrawn.
Removed the redundant direct import
`Mathlib.RingTheory.Localization.LocalizationLocalization`; the construction and
its fraction-field instances come from `Mathlib.RingTheory.Localization.AsSubring`.

## Where the brief, the DAG or earlier work was wrong

The planned use of Tag 031F to show the chosen prime maximal is unnecessary.
Nonzeroness follows because a zero prime would contract to a zero maximal ideal
of the dimension-one local domain, making it a field of dimension zero.
All other substantive planned steps and the unit route are retained. The unit's
`realized` record imposes no separate residue-field step on this tool lemma.
The existing declaration docstring describes the earlier, longer argument;
the updated DAG and Lean proof record the actual shorter route.

## Second reading by V8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
