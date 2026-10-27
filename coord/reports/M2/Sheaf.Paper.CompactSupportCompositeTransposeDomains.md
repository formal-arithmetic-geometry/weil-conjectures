## What changed

Filled eleven theorem proofs in `Sheaf.Paper.CompactSupportCompositeTransposeDomains`.
The tensor, pullback, unit, origin and compact-support membership proofs use existing
fixed-scalar etale/pro-etale comparison APIs. The projection-isomorphism proof uses the
published bounded-constructible compactification projection formula. The normalized Hom
naturality proof lifts source maps to chosen etale origins and applies the two ordinary
adjunction naturality equations; injectivity gives the counit normalization.

Added only proved private helpers and four private source-library imports:
`Etale.Derived.Stability.Reduction`, `ProEtale.FiniteCoefficient.Derived.HomComparison`,
`ProEtale.FiniteCoefficient.Derived.ProjectionFormula` and
`ProEtale.FiniteCoefficient.Derived.AmbientAdjointClass`, all under
`WeilConjectures.SixFunctors`.

Existing signatures, definition bodies and public imports are unchanged. Local
transparency settings keep the derived category and normalized Hom construction folded.
The node records the auxiliary proof route and preserves the remaining assembly plan.
No source-library module is changed and no new module is delivered.

## Proved and sorry left

Original hole count: 12. Closed: 11. Added: 0. Remaining: 1.

All names below are in `AlgebraicGeometry.ProEtale.CompactSupportTranspose`.
Closed `exceptionalOriginProperty`, `unitCTF`, `tensorInputBC`, `tensorInputCTF`,
`imageBC`, `imageOrigin`, `forwardProjection_isIso`, `coefficientProductCTF`,
`smoothImageCTF`, `pullCTF`, and `hom_natural`.

The only remaining sorry is `compactSupportCompositeTransposeDomains`, attached to
`lem-pur-compact-support-composite-transpose-domains`. Its existing statement and
complete six-step natural-language proof are retained. This is a partial proof delivery,
not a proof or decomposition of that final assembly theorem. There are no new holes,
no private holes and no holes inside definitions.

The eleven-proof version compiled successfully during development. The final packet
is checked again by lcompile and by the required deliver3 compile/preflight.

## No longer needed

None at module or node level. The completed auxiliary tensor and pullback proofs do not
need the intrinsic presentation lemmas, and the Hom naturality proof directly uses the
published ordinary adjunctions and comparison map fullness. However, the final theorem
still needs its accepted projection-coherence and compositor-transport route. Its original
proof-dependency imports and all original node dependencies are therefore retained. No
upstream declaration or quarantined module is removed, and no pruning is claimed.

## Where the brief, the DAG or earlier work was wrong

No statement is disputed. The finite-Tor restrictions have been kept on coefficients;
`imageBC` makes no Tor-amplitude assertion about compact-support images.

The remaining work is the final assembly, especially unit/associativity of the specified
inverse projections and compatibility with the exact canonical compact-support compositor.
Experimental proofs elaborated the abstract naturality calculation but hit kernel-checking
costs around `alpha`; these are unfinished proofs, not a tool failure. Experimental split
modules and nodes were removed from the packet. No replacement compositor or arbitrary
isomorphism is used in the delivered code.

## Second reading by M2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
