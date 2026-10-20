## What changed

Retired Sheaf.Algebra.FiniteFlatRestrictionProjective in favor of its official
upstream twin, as assigned by coord/retire-items.tsv and the human hand-off in
coord/changes/retire-sheaf-twins-20261020.md. The upstream theorem is named
Module.finitePresentation_and_projective_of_flat; its signature is identical to
Module.finite_flat_restriction_projective, with independent universes and unchanged
hypotheses and conclusion. The DAG node lem-pc-finite-flat-restriction-projective
now names that canonical theorem. The node's proof and every parent dependency
stay unchanged.

Change record: coord/changes/retire-finite-flat-restriction-projective-B3.md.
The packet contains deleted.txt, the updated DAG attachment, and this change record.
No upstream source is edited. No consumer needs adaptation: the downstream tool
and scans of the live and quarantined Lean sources find no importer or external
use of the retired theorem.

Validation: the existing Sheaf source compiles. A separate scratch file importing
only the upstream module proves the entire old statement by applying
Module.finitePresentation_and_projective_of_flat. The compiler accepts it and
#print axioms reports only propext, Classical.choice and Quot.sound.

## Proved and sorry left

This is a retirement repair with zero original holes: X7 had already proved
Module.finite_flat_restriction_projective immediately before the retirement claim.
Proved 0 of 0 sorries in this delivery; closed 0 holes; added 0 holes; split off 0
statements. No sorry remains in the retained upstream theorem
Module.finitePresentation_and_projective_of_flat. No new theorem is introduced.

## No longer needed

Pruned module: Sheaf.Algebra.FiniteFlatRestrictionProjective, including its duplicate
Module.finite_flat_restriction_projective declaration and its seven imports.
No consumer imports are changed because the copy has zero consumers.
No DAG node is pruned: lem-pc-finite-flat-restriction-projective remains needed by
lem-pc-finite-flat-pushforward-locally-free, and its existing three-step proof and
all dependencies are preserved through the upstream theorem attachment.
The Hilbert-functor unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief describes an item containing sorry, but the current queue
row is a retirement item with zero holes. The human-authorized retirement hand-off
supplies the repair scope. The retirement table calls the pair DIFFERENT because
the twin lacks the old name; inspection and a compiler check show that its renamed
theorem has exactly the required statement, so no mathematical repair or new
lemma is necessary. The earlier kept-copies table deferred retirement because a
consumer was in a pending landing; the current source has no such consumer.

## Second reading by B3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
