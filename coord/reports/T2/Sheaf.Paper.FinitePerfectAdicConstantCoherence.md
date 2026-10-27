## What changed

Proved `AlgebraicGeometry.Scheme.finitePerfectAdicEtaleConstant_coherence` with its
statement and public imports unchanged. Added a proof import of
`WeilConjectures.SixFunctors.Etale.Derived.UpperStarRestrictScalars` and five proved
private helpers: identification of the canonical coefficient mate with the source
library mate, its composition equation with a named composite, the derived version
of that equation, the defining equation of the pulled normalization arrow, and
coherence for an arbitrary coefficient arrow.

The proof postcomposes by the coefficient restriction of the invertible composition
comparison, uses coefficient-mate composition and naturality, and cancels the two
comparison isomorphisms. Updated the item's DAG proof to record these actual steps.
No statement, definition, instance, attribute, or public import was changed.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.finitePerfectAdicEtaleConstant_coherence`
(node `lem-weil-pbc-finite-perfect-adic-constant-normalization-coherence`).
Added 0 holes and split off 0 statements. No `sorry` remains in the item module.
All five private helpers are proved. The completed module compiled without warnings
in 12.1 seconds using `lcompile.py`. The delivery tool also checks compilation and
prints the axioms of the delivered declarations.

## No longer needed

Removed the proof dependency on
`lem-weil-pbc-derived-scalar-extension-local-systems`
(`Sheaf.AlgebraicGeometry.DerivedScalarExtensionLocalSystems`): this equation needs
only coefficient restriction and inverse-image composition, rather than construction
of scalar-extension functors or their adjunctions. Its module was never directly
imported by this item; no existing import was removed. The public import of
`Sheaf.Paper.FinitePerfectAdicConstantCohomology` remains necessary for the statement.
No module is withdrawn, and no other node or module is claimed globally unused.
The unit's statement and proof route are preserved.

## Where the brief, the DAG or earlier work was wrong

The planned appeal to the general derived scalar-extension/local-systems theorem
was unnecessary: the adopted source already proves the precise underived
coefficient-mate composition law and the theorem transporting it to derived
categories. The required canonical mates are definitionally identical to those
source constructions. The same argument works for any specified coefficient arrow;
no finite-perfect or normalization property of the adic tower is needed.
The current server queue lists this as a proof item with one hole, with no rework
row or build-error file. No mathematical statement was disputed or changed.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.FinitePerfectAdicConstantCoherence": "7df3941add187576e42082139c369a15ba248ca8"}, "results": {"Sheaf.Paper.FinitePerfectAdicConstantNormalization": {"hash": "d1ded0f7d17708d681bd5d52ff685b706373f936", "status": "OK"}}, "seconds": 69, "time": "2026-10-28T04:08:42+0800", "transitive": 0, "version": 1}
```

## Second reading by T2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
