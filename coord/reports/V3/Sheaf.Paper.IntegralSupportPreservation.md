## What changed

Filled `integral_support_preservation` using the recorded normalized finite compact-support
functor and its canonical completed compact-support realization. The proof installs residue-field
invertibility from the finite-field coefficient unit, uses `integral_residue_tor` to identify
integral constructibility with finite-Tor constructibility, transports the functor's object
property across the realization isomorphism, and converts the result back to the target
finite-Tor predicate. Added proof-only imports of `Sheaf.Paper.CompactSupportFiniteAction` and
`Sheaf.Paper.IntegralResidueTor`; the public statement import is unchanged.

## Proved and sorry left

Closed the sole `sorry`, `WeilConjectures.ConstructibleExceptionalCoefficients.integral_support_preservation`.
No `sorry` remains and none was added.

## No longer needed

The previous planned dependencies `lem-sf-exceptional-finite-operations`,
`lem-sf-exceptional-system-transport`, `lem-pur-normalized-reconstruction-adjunction-calculus`,
and `lem-sf-integral-compactification-system-realization` are not used by this shorter route.
Their modules are not imported. The proof uses the existing nodes
`def-weil-compact-support-finite-action`, `def-weil-integral-rational-qbar-compact-support`,
and `lem-coef-integral-residue-tor` instead.

## Where the brief, the DAG or earlier work was wrong

The DAG proof plan treated the full normalized system transport as necessary. The already
recorded finite compact-support action and its completed realization expose the needed object
membership directly, and `integral_residue_tor` supplies the exact predicate conversion.

## New nodes

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.IntegralSupportPreservation": "c53e3de858a772522bed68bd2b19fd8afdaf0630"}, "results": {"Sheaf.Paper.ExceptionalIntegralSupportAdjoint": {"hash": "2e1ac3a56dee7137e759447d24a5569987a192aa", "status": "OK"}}, "seconds": 78, "time": "2026-10-28T03:28:15+0800", "transitive": 0, "version": 1}
```

## Second reading by V3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
