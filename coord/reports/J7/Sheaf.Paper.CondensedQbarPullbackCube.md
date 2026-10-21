## What changed

Restored Sheaf.Paper.CondensedQbarPullbackCube from its assigned rework archive.
In private qbarPullIso_comp, removed the obsolete finiteCoefficientDerivedToAlgCl
identifier from the dsimp list. The existing derivedExtendScalarsToPadicAlgCl
abbreviation directly unfolds to the required canonical derived scalar extension.
The signature repeatedly unfolded full concrete coefficient comparisons. A proof-local
section now keeps constructibleToPadicAlgCl, constructibleToQbarPullIso and
boundedConstructibleUpperStarComp folded,
respects reducibility except in types, explicitly unfolds them for normalization,
infers the already-unfolded Omega bounded object, and normalizes Over.Hom.left.
The final complete repair compiled without warnings in 58.3 seconds.
All existing declarations, signatures, visibility, public imports and comparison data
are preserved. The proof route and dependencies are retained, with this restoration
recorded in the node's proof_origin. The change record is
coord/changes/J7-restore-qbar-pullback-cube.md.

## Proved and sorry left

This is a zero-hole rework repair: the archive has zero sorry occurrences and the
restored file has zero. Holes closed: none. Holes added: none. Split off: none.
Retained complete proofs are coefficientCube_of_iso, qbarPullIso_comp, qbarPull_eq,
qbarPull_square_cube_iso, qbarPull_square_cube, and the public
AlgebraicGeometry.ProEtale.CondensedRing.constructibleToQbar_pullback_cube.
No proof holes are introduced in another module.

## No longer needed

No imports, nodes, or modules are pruned. The obsolete finiteCoefficientDerivedToAlgCl
normalization name is removed, not a mathematical dependency. Existing composition
coherence and diagram-pasting helpers remain needed and imported. The parent
lem-weil-pbc-qbar-condensed-exchange-left-adjunct still uses the cube. The full unit
route is preserved. No new nodes are introduced.

## Where the brief, the DAG or earlier work was wrong

The historical handoff names an E1 sandbox and requests its old dry run. That sandbox
is absent on this machine. The current rework row instead preserves the completed
module in quarantine/Sheaf/Paper/CondensedQbarPullbackCube.lean, with an upstream-sync
unknown-identifier diagnostic. That archive, rather than a blank file or an old
five-hole version, is the starting point. Zero current live importers does not make
this module unused: the quarantined exchange-left-adjunct consumer and the DAG both
still require it. Validation: the initial alias-only repair compiled without diagnostics in 51.3 seconds,
but subsequent complete and artifact-writing checks reached the 60-second limit.
A signature-only diagnostic then exhausted 5000 heartbeats in definitional equality
before entering qbarPullIso_comp. Respecting scoped irreducibility and explicitly
unfolding the two comparisons in the proof fixes that cost. The complete updated file
compiled in 49.5 seconds, with only an unused reflexivity tactic subsequently removed.
The required delivery tool performs the final warning and axiom checks.

Delivery attempts encountered saturated delivery slots and repeated compile-server
no-answer responses. Missing published CondensedQbarComparisons.olean.server and
OverSquare.olean.server artifacts were separately reproduced and subsequently cleared.
No published artifacts, shared sources, or launcher tools were edited. Optional proof
experiments remain outside the delivery packet.

The final warning-free compile includes boundedConstructibleUpperStarComp in the
local irreducibility scope, preserving the same mathematical comparison and proof route.

## Second reading by J7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
