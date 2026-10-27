## What changed

The finite agreement proof is reduced to a componentwise interface.  The main theorem
unfolds `tensorFiniteAgreement`, introduces a finite coefficient field and a pair of
integral objects, and applies the new component theorem.  The component theorem
states the exact `HEq` comparison for that fixed field and pair.

## Proved and sorry left

`completed_tensor_common_lift_agreement` is proved by assembling the componentwise
comparison.  One strictly smaller theorem remains as a named split obligation:
`completed_tensor_common_lift_agreement_component` in
`Sheaf.Paper.AdicCompletedTensorCommonLiftAgreementComponent`; its proof is still
`sorry` and is the single hole added by this delivery.  No definition contains a
`sorry`.

## No longer needed

No imports were removed.  The component route needs only the existing finite model,
native realization, and common-lift coherence interfaces; no additional nodes from
the original finite normalization narrative are needed below this split.

## Where the brief, the DAG or earlier work was wrong

The prior split exposed the whole `tensorFiniteAgreement` family but did not expose
its atomic equality for one finite field and one pair of integral objects.  The new
component interface is a strict substatement, and the parent theorem combines its
instances by ordinary introductions.  The target statement is unchanged.

## New nodes

`lem-sf-adic-completed-tensor-common-lift-agreement-component` records the fixed
finite-field, fixed-integral-pair `HEq` comparison and is realized by
`Sheaf.Paper.AdicCompletedTensorCommonLiftAgreementComponent`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.AdicCompletedTensorCommonLiftAgreement": "22da3122e168f417eef90323a9242db453961295", "Sheaf.Paper.AdicCompletedTensorCommonLiftAgreementComponent": "2f517183cffeedebdc581604645eb5213f5c7943"}, "results": {}, "time": "2026-10-28T05:28:32+0800", "transitive": 0, "version": 1}
```

## Second reading by W2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
