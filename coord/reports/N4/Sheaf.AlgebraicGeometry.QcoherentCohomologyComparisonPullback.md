## What changed

Restored the quarantined item at its original Lean module path, preserving the
complete proof, statement, public imports, and its existing DAG attachment.
The proof chooses the unique normalized comparison on each scheme, inverts it,
uses the section normalization in degree zero, applies the declared normalized
pullback square, and obtains scalar compatibility by cancelling the coefficient
naturality identity. Both recorded proof dependencies remain necessary.

## Proved and sorry left

The archived item already has zero holes. The restored theorem is
AlgebraicGeometry.Scheme.Modules.exists_qcoherentCohomologyComparisonPullback.
Holes closed: zero of zero. Holes added: zero. Split off: zero.
The existing imported theorems exists_unique_qcoherentNormalizedComparison and
qcoherentNormalizedComparison_pullback_square retain their existing holes in
separately assigned modules; no dependency module is changed in this packet.

## No longer needed

None. Both declared proof dependencies and the unit route are preserved.
No module, declaration, import, or node is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The item is a zero-hole quarantine restoration, not a new mathematical proof.
Its complete retained Lean file is byte-identical to the quarantined source.
The existing Lean attachment, proof dependencies and unit route remain valid.
No declaration of the root changes, so no downstream cluster adaptation applies.

On this resumed attempt, the required initial deliver3.py invocation again
refused to push: its compile reports that the published build has no
QcoherentNormalizedPullbackSquare.olean. The item cannot reach elaboration of
its proof because that proof import fails first.

A fresh lcompile.py check of the prerequisite's current repository source
confirms its import failure in 1.5 seconds:
`import WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturality
failed, environment already contains
'AlgebraicGeometry.Scheme.Modules.ExtEdgeResolution.moduleComparisonEquiv'
from Sheaf.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturality`.
The claim records assign QcoherentNormalizedComparison to B2,
QcoherentNormalizedPullbackSquare to F4, and
ModuleCohomologyExtResolutionNaturality to F2. The current F2 return records an
independent-reader-approved retirement whose landing failed because an
apply-fixes change-record path was absent from that delivery.

This is the same prerequisite publication/dispatch blocker as the preceding
attempt. No dependency is changed, no replacement declaration is introduced,
and no altered dependency artifacts are used. The retained scratch checks are
not delivered and do not constitute successful validation of this item.
The delivery tool pushed nothing. The packet remains ready for validation
once the separately assigned prerequisite repairs are published.

Latest resumed attempt: the required initial delivery check again failed in
1.8 seconds with the missing QcoherentNormalizedPullbackSquare.olean diagnostic.
A byte comparison confirms that both the retained item and the prerequisite
scratch copy still match their current authoritative sources. Compiling the
unchanged prerequisite again failed in 1.7 seconds with the duplicate
moduleComparisonEquiv diagnostic above. Current claims still assign the three
prerequisite repairs to B2, F4 and F2 respectively. The root's existing proof
uses exactly its two recorded dependency declarations; neither has an alternate
upstream declaration. No root signature or proof repair can publish these
separately assigned prerequisites. No delivery was pushed in this attempt.

Final dispatched retry (2026-10-21): the required initial deliver3.py check
failed in 1.4 seconds before item elaboration because the published build still
has no QcoherentNormalizedPullbackSquare.olean. A fresh lcompile.py check of
the byte-identical prerequisite scratch source failed in 2.2 seconds with the
same duplicate ExtEdgeResolution.moduleComparisonEquiv import error. Both the
item and prerequisite copies were compared to current authoritative sources
and match exactly. The current F2 claim and return still assign the prerequisite
retirement repair elsewhere. The root declares no replacement prerequisite,
changes no interface, and has zero holes; no downstream edit is forced.
The delivery tool pushed nothing. This packet is retained pending publication
of the prerequisite repair and its compiled artifacts.

## Second reading by N4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
