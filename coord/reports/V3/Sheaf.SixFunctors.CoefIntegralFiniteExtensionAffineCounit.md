## What changed

Proved `WeilConjectures.IntegralFiniteExtension.affineCounit_isIso` with its existing
signature and public imports unchanged. Added proof imports
`Sheaf.Paper.EtaleSystemQuotientNormalization` and `Sheaf.Paper.SfBcAdicRingDomain`.
The single-ring normalization theorem applies to the native cross-field map itself
and to the supplied adjunctions. Its counit equation identifies `globalMate` with
an invertible mate component followed by the image of the scalar-unit isomorphism.
Updated the item node's proof, proof dependencies and proof origin accordingly.
Validation: the item compiled through `lcompile.py` without errors or warnings in 8.9 seconds.

## Proved and sorry left

Closed the one original hole in
`WeilConjectures.IntegralFiniteExtension.affineCounit_isIso`
(node `lem-sf-integral-finite-extension-affine-counit`). Zero holes remain in the
item; zero holes were added and no statements were split off.

## No longer needed

The planned direct proof dependencies `lem-coef-finite-free-extension`
(`Sheaf.Paper.FiniteFreeCoefficientExtension`), `lem-coef-finite-dualizing`
(`Sheaf.SixFunctors.FiniteDualizing`), and `def-coef-finite-dualizing-data`
(`Sheaf.SixFunctors.FiniteDualizingData`) are not used as proof dependencies of
this theorem. The existing arbitrary-finite-ring normalization theorem covers
native nonflat maps and arbitrary supplied adjunctions directly, so explicit
ramification reindexing, quotient composition, and right-adjoint transport are
unnecessary here. No existing public imports or modules are removed; the finite
dualizing definitions remain needed in the statement through the public model import.
These nodes may still be required by other consumers or transitively.

## Where the brief, the DAG or earlier work was wrong

The planned ramification-and-quotient route is valid but unnecessary for this
statement: `AlgebraicGeometry.Etale.etaleCoefficientQuotientNormalization` already
proves invertibility of the counit-normalized mate for every map between finite
l-power-torsion coefficient rings, for the actual supplied compactification and
right adjoints. The proof checks both ring hypotheses before applying it and
identifies the exact arrow, including the inverse comparison's nonzero branch.
No statement or definition is changed. Empty schemes and identity embeddings
require no separate case, and no flatness of the native map is asserted.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.SixFunctors.CoefIntegralFiniteExtensionAffineCounit": "d4b2befaf102d8204465a97b009f01fac5d974d5"}, "results": {"Sheaf.SixFunctors.CoefIntegralFiniteExtensionFiniteUIsInvertible": {"hash": "96bcf04044febeab57b4bb19626b299c5ca0ff19", "status": "OK"}}, "seconds": 81, "time": "2026-10-28T16:01:00+0800", "transitive": 0, "version": 1}
```

## Second reading by V3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
