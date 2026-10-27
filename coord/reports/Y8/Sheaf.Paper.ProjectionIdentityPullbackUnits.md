## What changed

Proved `WeilConjectures.projectionIdentity_pullbackUnits` in
`Sheaf.Paper.ProjectionIdentityPullbackUnits` with the existing
`WeilConjectures.isomorphismFieldTransport` theorem, specialized to the scheme identity.
Added its module as a private proof import. The datum's three normalization equalities
identify the supplied pullbacks with the canonical integral, rational and common-stage
functors; the transport theorem makes each an equivalence, hence full and faithful.
The theorem's signature, public imports and all definitions are unchanged.
Updated the item's node proof, proof dependencies and proof origin to this route.
Validation: the prescribed `lcompile.py` compile passed cleanly in 5.9 seconds.

The space's existing finite-type and quasi-compact witnesses discharge the transport
hypotheses. The coefficient datum provides the prime-to-characteristic condition and
algebraic closure. The transport theorem supplies residue invertibility; its two
structures on the same scheme coincide because invertibility data is subsingleton.
There is no separatedness or nonemptiness assumption. No construction is chosen from
an unproved existential proposition to define new data.

Searches used the prescribed `msearch.py` services: LeanFinder for fullness and
faithfulness of identity-isomorphic functors, Loogle for full functor isomorphism
transport, and grep for `Full.of_iso`, `Faithful.of_iso` and `IsEquivalence.mk`.
Repository search found the existing isomorphism transport clause records and theorem,
which directly cover all three coefficient stages and arbitrary finite E.

## Proved and sorry left

Closed one existing hole: `WeilConjectures.projectionIdentity_pullbackUnits`
(node `lem-sf-projection-identity-pullback-units`). Added zero holes and split off
zero statements. There are zero remaining `sorry`s in the item or delivery.
The proof uses existing declarations whose downstream proofs remain separate work.

## No longer needed

Removed the item's direct proof dependency on `fix-prop-adjunctions`
(`WeilConjectures.SixFunctors.Etale.Derived.Adjunctions`): no separate derivation,
completion reconstruction, rationalization or common-stage descent is needed here.
These operations are already handled by the existing isomorphism transport theorem.
No existing import was removed: the original sole import specifies the statement;
the new private import supplies the proof. No module is withdrawn, and no claim is
made that the adjunction module is globally unused.

The shorter route uses `lem-pod-isomorphism-field-transport` from another unit as an
existing tool, not as a replacement for this unit's statement or proof steps. This
item is below the unit's realized statement `prop-sf-pf-coherence`, and none of the
unit's realized nodes is removed or bypassed. The new import and DAG dependency are
acyclic; the transport node's dependency closure does not reach this item.

## Where the brief, the DAG or earlier work was wrong

The original plan repeated the completed, rational and common-stage identity
construction even though the existing isomorphism field transport theorem already
establishes equivalences for those exact functors. Its identity specialization is
sufficient. No statement or definition repair was needed.

## Second reading by Y8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
