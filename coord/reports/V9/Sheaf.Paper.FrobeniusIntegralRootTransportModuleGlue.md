## What changed

Proved `WeilConjectures.frobeniusIntegralRootTransport_moduleGlue` by reducing it to an
additive module lift, an isomorphism statement for the module adjunction unit, and
reflection of isomorphisms along the direct-image equivalence for an isomorphic scheme
map. The proof imports `ProEtaleIsomorphismInverseImage` for that equivalence.

## Proved and sorry left

The original glue theorem is proved. Two strictly smaller intermediate statements are
split off and remain `sorry`:

- `WeilConjectures.frobeniusIntegralRootTransport_moduleLift`
- `WeilConjectures.frobeniusIntegralRootTransport_moduleUnit_isIso`

## No longer needed

None. No original public import is removable because the theorem signature uses the
coefficient and module definitions and the canonical adjunction. The root-comparison
lemmas belong to the parent transport argument and were not imported by this module.

## Where the brief, the DAG or earlier work was wrong

The original proof route omitted the necessary reflection argument. The direct-image
functor is an equivalence only after installing the inverse-image equivalence instance;
this is supplied by `proEtaleIsoInverseImage_equivalence` with explicit universe levels.

## New nodes

- `new-weil-frobenius-integral-root-transport-module-lift`
- `new-weil-frobenius-integral-root-transport-module-unit`

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.FrobeniusIntegralRootTransportModuleGlue": "73dd29473cb2abc81c5cffc76a4120799ab00aa3", "Sheaf.Paper.FrobeniusIntegralRootTransportModuleLift": "ab77787fc6c6ee621e66f83886416bc812319f02", "Sheaf.Paper.FrobeniusIntegralRootTransportModuleUnit": "5c09ba1636fdbf253d00bf2becedfdd1889e9e00"}, "results": {"Sheaf.Paper.FrobeniusIntegralRootTransport": {"hash": "5485d25f6d1c738e2a6eb7ed6823b7c2a1e0d897", "status": "OK"}}, "seconds": 197, "time": "2026-10-28T10:53:51+0800", "transitive": 0, "version": 1}
```

## Second reading by V9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
