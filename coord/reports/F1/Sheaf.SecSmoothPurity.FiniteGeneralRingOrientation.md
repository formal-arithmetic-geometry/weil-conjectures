## What changed

Restored the assigned quarantined item and replaced its original sorry by an explicit
coefficient/orientation assembly. The existing theorem signature and public import are unchanged.
No other existing Lean module is changed.

The proof constructs the bottom-extension quotient equivalence with ZMod using the p-adic
integer reduction kernel; constructs the common-exponent root-generator Tate comparison;
constructs the ordinary orientation by the actual smooth diagonal, normalized Rees family,
normal bundle and inverse integration adjunct; and applies the existing proved
normalizedOrientation_scalar. A proved site/scalar-unit calculation and exceptional-mate
naturality identify the actual exceptional reduction map. A categorical pasting lemma proves
its invertibility and the required orientation equation, including the intrinsic scalar
presentation comparison.

The ordinary construction previously appeared only as a private helper in
FiniteSmoothAdjunctionGeneralBase. Importing that module here creates an import cycle, so
FiniteSmoothNormalizedExistence exposes the construction in a module preceding this item.
The adopted source library is unchanged.

## Proved and sorry left

Original hole closed: AlgebraicGeometry.ProEtale.finiteGeneralRingOrientation
(lem-sp-general-ring-orientation). Its proof combines the stated comparisons in Lean.

One hole added: WeilConjectures.PurityFiniteSetting.diagonalOrdinaryReesNormalization
(lem-pur-diagonal-ordinary-rees-normalization), in its own new module. This is only the
prime-power geometric comparison between coordinate-counit normalization and the explicit
ordinary diagonal/Rees/integration equation. It assumes the given coordinate-normalized
ordinary orientation and has no arbitrary coefficient ring, exceptional reduction map,
coefficient-line comparison or scalar-extension conclusion.

This is a decomposition: one original hole closed and one strictly smaller geometric hole
added, net zero holes closed. It is not reported as a net proof. The item contains zero holes;
the delivered new modules contain exactly the one named hole above. No hole is in a definition.

Complete auxiliary proofs: generalRingNormalizedOrientation, generalRingCoefficientLine,
primeQuotientEquiv, scalarPresentation_naturality, assembleOrientation, scalarUnit_origin,
scalarUnit_formula, ordinaryScalarUnitSandwich, and scalarDualizingUnit_square,
together with their private categorical/unit helpers.

Validation: the full sandbox compiled in import order through lcompile.py. The final
site-square and item checks took 34.2 and 34.0 seconds; every new module passed
within the 60-second limit. The theorem signature was compared with the current shared
source and is unchanged. DAG declarations, dependencies, source paths, line lengths,
and the actual one-hole count were checked. Delivery preflight runs with this packet.

## No longer needed

No original import is removed: the item originally imported only FiniteGeneralRingData.
No existing module or declaration is withdrawn, and no global module pruning is claimed.

The original node's following direct proof dependencies are replaced by the existing normalized
orientation and ordinary-dualizing-scalar APIs, or by the new smaller geometric bridge:
cor-pur-vector-bundle-purity, def-amb-vector-integration, def-pur-dnc-section-family,
det-sp-reduction-exceptional, det-sp-scalar-extension-functor,
lem-amb-affine-space-top-trace, lem-asd-etale-finite-twist-pullback,
lem-pur-diagonal-base-change, lem-pur-diagonal-regular-immersion,
lem-pur-dnc-coefficient-transport, lem-pur-finite-ring-site-tensor-transpose,
lem-pur-sheaf-hom-cover-gluing, lem-weil-pbc-derived-single-fully-faithful,
lem-weil-pbc-ringed-topoi-derived-tensor-pullback, sk-def-sfb-dc-setting,
thm-amb-vector-bundle-purity, thm-pur-cohomological-smoothness and thm-pur-dnc-invariance.
These are not invoked separately by the item. The relevant diagonal/DNC/integration
mathematics remains in the APIs used by this proof; transitive dependencies and every
blueprint unit route remain intact. The source-library declarations remain untouched.

## Where the brief, the DAG or earlier work was wrong

The item was quarantined, rather than withdrawn. Its current server rework record and preserved
source were read before restoration. The assigned original theorem still had one sorry.

The DAG predated the proved normalizedOrientation_scalar theorem. That theorem already
performs the coefficient comparison of the diagonal, specialization and integration factors.
The missing interface is the comparison between the coordinate normalization used by
PurityDiagonalDualizingObject and the Rees normalization used by that theorem. It is isolated
as the new geometric lemma, rather than duplicating the full general-ring obligation.

The common-exponent Tate comparison is proved as an existence theorem with all fields built
explicitly. Its imported private isomorphism helper is used only in that theorem proof,
never in a public definition body.

## New nodes

lem-pur-diagonal-ordinary-rees-normalization: the sole new sorry, relating the two geometric
normalizations at prime-power coefficients. Its docstring gives the source, full argument,
and dimension-zero, empty-scheme and zero-ring cases.

lem-sp-finite-smooth-normalized-existence: proved construction of the ordinary orientation
from the actual diagonal, normalized specialization and inverse bundle integration.

lem-sp-general-ring-orientation-assembly: proved categorical square pasting and invertibility.
Its private helper proves site-adjunction unit compatibility by naturality and the triangle law.

lem-sp-general-ring-common-exponent-line: proved explicit coefficient-line construction.

lem-sp-general-ring-prime-quotient-equivalence: proved identification of the actual
bottom-extension quotient with the prime-power residue ring, independent of uniformizer choice.

lem-sp-general-ring-scalar-presentation-naturality: proved naturality of the canonical
intrinsic-to-fixed scalar isomorphism.

lem-sp-general-ring-ordinary-scalar-unit: proved cancellation of the concrete single-functor
unit conversions before site comparison. This names the ordinary unit calculation so its
proof remains behind an API when applying the comparison functor.

lem-sp-general-ring-scalar-unit-formula: proved identification of the fixed scalar-unit
map with the site comparison followed by the ordinary scalar-unit map. Profiling showed
that the large concrete unit models dominate checking; this separately checked result
uses the named ordinary unit theorem and explicit outer projection equations.

lem-sp-general-ring-scalar-unit: proved transport of the comparison-adjunction unit.

lem-sp-general-ring-site-scalar: proved compatibility of the ordinary dualizing coefficient
map with the pro-etale exceptional coefficient map at the unit.

No existing statement or definition changes, so no change record or consumer adaptation is
required. The original node's proof, proof_deps and proof_origin are updated to this route.

## Related modules compiled before delivery

2 related module(s) compiled against this delivery by deliver3.py: 2 OK.

```json
{"capped": false, "direct": 2, "left_out": 0, "own": {"Sheaf.Paper.DiagonalOrdinaryReesNormalization": "dcfdda5cb120cce1e4cdf8d5f8c7e76ef749dd43", "Sheaf.Paper.FiniteSmoothNormalizedExistence": "2b6449430be94998bcb06c78c6882123e5b57cc2", "Sheaf.SecSmoothPurity.FiniteGeneralRingOrdinaryScalarUnit": "aacab4822c628e3302727186dd8b602a6109d7ac", "Sheaf.SecSmoothPurity.FiniteGeneralRingOrientation": "d0e996de75c401dd5753905d7cd699ae18a9754b", "Sheaf.SecSmoothPurity.FiniteGeneralRingOrientationAssembly": "fecf31cdafa078fd67f583eadea6b157ec10eade", "Sheaf.SecSmoothPurity.FiniteGeneralRingOrientationSupport": "92efe06f53570815959c3954528c40c6c803c7da", "Sheaf.SecSmoothPurity.FiniteGeneralRingScalarUnit": "9b5b0e1b56698df051b80458533acf5e6f5c176b", "Sheaf.SecSmoothPurity.FiniteGeneralRingScalarUnitFormula": "64e135a88402494dccfbaa48a38c61fbc2e7b2df", "Sheaf.SecSmoothPurity.FiniteGeneralRingSiteScalar": "73e121c208cf5e9cb1f8120636478f6af16781e0"}, "results": {"Sheaf.Paper.PurityConjugatesTowerReduction": {"hash": "1e086facd08a557ee70cd2b11daed249cb5fb1fd", "status": "OK"}, "Sheaf.SecSmoothPurity.FiniteGeneralRing": {"hash": "e9aa1fa8be93b0c261eb152b281ed40461bbae41", "status": "OK"}}, "seconds": 85, "time": "2026-10-28T01:33:49+0800", "transitive": 0, "version": 1}
```

## Second reading by F1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
