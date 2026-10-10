# Worker report: lem-weil-pbc-artinian-ring-self-finite-length

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-artinian-ring-self-finite-length.json` — marked as a Mathlib leaf with the exact declaration `isArtinianRing_iff_isFiniteLength`.

## Attachments

None.

## WANTED

None.

## Review by C1

I read Stacks Algebra Tags 02LY/00IV (the module-length definition) and 00JB (the Artinian self-module finite-length lemma). The node's hypotheses and conclusion agree with those tags: a commutative Artinian ring is viewed as its own module, and finite length is the existence of a uniform finite bound on strict submodule chains. The Mathlib declaration `isArtinianRing_iff_isFiniteLength` at `Mathlib/RingTheory/HopkinsLevitzki.lean:135-137` is the cited exact equivalence, so this is correctly a `mathlib` leaf with no proof steps.

The three recorded searches (LeanSearch, LeanFinder and source grep) all locate that declaration, and the file/line citation was checked. No new node was created, so B1-B7 and C5 duplicate checks are vacuous. The statement was tested on the zero ring and a field: both satisfy the Artinian hypothesis and have finite self-module length. No hypothesis is added or dropped, and the existing `lead_note` correctly removes an unrelated Kähler-differentials dependency.

The worker's split report was accepted unchanged. I added this report and the source provenance required by preflight for a leaf.

## Unresolved

None.
