## What changed

Proved `WeilConjectures.frobeniusIntegralRootTransport_moduleUnit_isIso` in
`Sheaf.Paper.FrobeniusIntegralRootTransportModuleUnit`, with its original signature.
Added a private proof import (`import all`) of
`Sheaf.AlgebraicGeometry.ProEtaleIsomorphismInverseImage` to reuse its already proved
`isoModulePushforwardEquivalence` for arbitrary isomorphic coefficient sheaves.
The coefficient adjunct is invertible because the scheme map is an isomorphism.
The resulting module direct-image equivalence makes the canonical adjunction unit
invertible; the underlying additive sheaf functor preserves this isomorphism.
No definitions, statements, public imports, attributes, or other existing modules changed.

The final file compiled cleanly in 4.5 seconds using `lcompile.py`. The import-direction
check passed. The current server queue classifies the item as proof/route, with no
rework row or recorded build error. Mathlib searches used LeanFinder, Loogle and grep;
both semantic services found the adjunction-unit equivalence instances.

## Proved and sorry left

Closed 1 of 1 holes:
`WeilConjectures.frobeniusIntegralRootTransport_moduleUnit_isIso`
(node `new-weil-frobenius-integral-root-transport-module-unit`).
There are zero `sorry` declarations left in the item and zero holes added or split off.

## No longer needed

None. All three existing public imports are needed by the statement. The proof needs
only the additional private import stated above. No module or node is withdrawn.
No root-limit, tensor-generator, or sectionwise semilinearity lemma is needed for this
categorical unit assertion. The unit route remains unchanged.

## Where the brief, the DAG or earlier work was wrong

The old proof plan described transport through coefficients but did not cite the
existing general module-pushforward equivalence. The helper
`isoModulePushforwardEquivalence` already handles arbitrary ring sheaves whenever the
coefficient direct-image map is invertible, so completed coefficients require no new
tensor or sheafification proof. The DAG proof now records this reuse, the coefficient
adjunct calculation, and the Mathlib unit-isomorphism step. Its statement is unchanged.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.FrobeniusIntegralRootTransportModuleUnit": "5154c2a7342a100bbb913005fd6cf5371da942f5"}, "results": {}, "time": "2026-10-28T11:55:34+0800", "transitive": 0, "version": 1}
```

## Second reading by C7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
