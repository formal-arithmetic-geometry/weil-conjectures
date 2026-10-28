## What changed

Proved `WeilConjectures.AdicQbarRealization.normalized_reindexing_identity_from_finite`
in `Sheaf.Paper.AdicReindexingIdentityAssembly` with its statement unchanged.
Unpack the common-stage pair and its rational-localization object, then apply
`NormalizedReindexingFiniteCertificate.equation` at the resulting integral object.
The certificate already contains the displayed source-identity equation.
Updated the item's DAG proof and proof dependencies to match this argument.

Searches: LeanFinder returned generic localization natural-transformation extensionality;
Loogle returned `CategoryTheory.NatTrans.ext`. Neither is needed because common-stage
objects are literal pairs and raw rational localization retains integral objects.
Local source search found the same two object eliminations in
`AdicReindexingCompositionCancelledDescent`.

## Proved and sorry left

Closed 1 of 1 holes:
`WeilConjectures.AdicQbarRealization.normalized_reindexing_identity_from_finite`
(node `new-lem-sf-adic-reindexing-identity-assembly`).
No sorry remains in the item. Added 0 holes and split off 0 statements.

## No longer needed

No imports were removed and no modules were withdrawn. The inherited public import
provides the certificate type and preserves the existing public interface.
The proof does not use `normalized_reindexing_identity_finite` (node
`new-lem-sf-adic-reindexing-identity-finite-certificate`): certificate construction
belongs to the caller. Replaced that proof dependency by the certificate-data node
`new-lem-sf-adic-reindexing-identity-finite-data`.
No naturality, common-stage transport or source-unit calculation is needed here.

## Where the brief, the DAG or earlier work was wrong

The previous proof plan described transport along stage isomorphisms. In the actual
implementation every common-stage object is definitionally a finite inclusion of
a localized integral object, so two constructor eliminations suffice. The supplied
source-unit hypothesis is redundant but is retained verbatim. The unit route and
all existing declaration signatures are unchanged.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.AdicReindexingIdentityAssembly": "8dd3db915ccff481cbc3725390a77dba751ee945"}, "results": {}, "time": "2026-10-28T11:54:37+0800", "transitive": 0, "version": 1}
```

## Second reading by E6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
