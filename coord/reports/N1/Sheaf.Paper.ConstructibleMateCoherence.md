## What changed

Prove `WeilConjectures.PodConstructibleMate.frobenius_exchanges_isIso` for the actual
rational and common-stage exchanges, using the literal whole-system construction.
Private helpers construct the pullback equivalence from the inverse scheme map,
apply mate invertibility, identify the integral realization as a composite of
isomorphisms, and pass to scalar localization. The common-stage conclusion uses
`StageSystem.Morphism.isIso_descNatTrans`. All public statements and definitions
are unchanged. Update the owning node with this route.

## Proved and sorry left

Closed one of the three holes in the current synchronized baseline:
`WeilConjectures.PodConstructibleMate.frobenius_exchanges_isIso`.
No holes added and no statements split off.

The following two named theorem holes remain, both owned by
`lem-pod-constructible-mate-coherence`:

- `WeilConjectures.PodConstructibleMate.rational_comparisons_coherent`.
- `WeilConjectures.PodConstructibleMate.common_comparisons_coherent`.

The earlier R1 adjunction and evaluation proofs are preserved. This delivery does
not count those three existing proofs as new work. The new exchange proof uses
existing named theorem dependencies that themselves remain unfinished, in
particular `FrobeniusExchange.compactAlpha_isIso`; it is a proof from the stated
library declarations, not a claim that the target closure is axiom-free.

## No longer needed

The exchange-invertibility clause needs no supplied-domain `IntegralData`,
`RationalData` or `CommonData` from `Sheaf.Paper.FrobeniusCompactSupportExchange`:
the actual construction already exposes its system mate, alpha and beta. No
import of that module is needed for the proof. Its node remains in the owning
node's planned dependencies for the two still-open comparison packages, so no
module or node is withdrawn. No existing public imports are removed.

## Where the brief, the DAG or earlier work was wrong

The synchronized source changed during this session: the initial local snapshot
showed six holes, then the R1 landing became visible with three already closed.
The delivery is based on that updated source and counts only the new exchange
proof. The common-stage evaluation naturality module is now present and held by
another group; it is used unchanged.

The direct component-wise realization proof caused excessive unfolding. The
successful proof keeps the realization isomorphisms folded, writes beta as an
explicit composite of whiskered isomorphisms, and unfolds only the full-subcategory
morphism wrapper at the end. Local reducibility settings retain the existing
public definitions. All existing instance attributes are preserved. No definition repair or forced adaptation is
part of the delivery.

## Second reading by N1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
