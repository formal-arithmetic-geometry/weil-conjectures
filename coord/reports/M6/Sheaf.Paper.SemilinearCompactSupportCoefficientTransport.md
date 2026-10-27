## What changed

Proved `systemRestrictionPush_isIso` from simultaneous K-injective resolutions on
small ringed-site models and the existing derived-mate criterion. Reused existing
proved generic restriction/pushforward and derived-unit naturality lemmas through
private proof imports. Moved generic helpers before concrete coefficient instances;
public constructions and theorem signatures are unchanged.

## Proved and sorry left

Closed one of the four original holes:
`WeilConjectures.CompactSupportCondensedRealization.systemRestrictionPush_isIso`.
Three original holes remain in the same namespace:
`systemRestrictionPullInv_isIso`, `systemRestrictionOpenInv_isIso`, and
`limitRestriction_existsUnique`. All belong to
`def-pur-semilinear-compact-support-coefficient-transport`.
No new holes and no split-off statements are added.

## No longer needed

No original public import, declaration, node, or module is removed.
The proper-image proof needs no assumption that scalar restriction preserves
K-injectives: the simultaneous resolution comparison suffices.
No new acyclicity or Roos-complex lemma is introduced.

## Where the brief, the DAG or earlier work was wrong

The original node contained no proof steps for its four theorem obligations.
The updated node records the proper-image argument completed here and identifies
the three retained obligations as unfinished. Scalar restriction is not assumed
to preserve K-injectives. All actual adjunction mates and normalization equations
are retained.

## Second reading by M6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
