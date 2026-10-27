## What changed

Replaced the one hole in `Sheaf.AlgebraicGeometry.EtaleGraphAmbientSourcePasting`
by a componentwise proof for both selected sides. The existing statement,
docstrings and public import are unchanged. Four proved private helpers carry
the vertical exchange specialization, cancellation in the B/e grid, the proper
terminal compositor calculation, and their assembly.

Added private proof imports of
`Sheaf.AlgebraicGeometry.EtaleProperAmbientTransportComposition` (its proved
`comp_assoc` and `comp_assoc_inv` helpers) and
`Sheaf.AlgebraicGeometry.OpenExchangeTower` (its proved
`direct_image_right_unit` helper). The tower theorem itself is not used.
Updated the item's DAG proof and dependencies to match this argument.

## Proved and sorry left

Closed: `AlgebraicGeometry.Etale.etaleGraphAmbientSourcePasting`
(node `lem-pur-etale-graph-ambient-source-pasting`), one of one original holes.
Added: zero holes. Left in the item: none. No split-off statements.

Verified with the required remote single-file compiler: clean compilation in
32.1 seconds, with no warnings. Delivery preflight supplies the independent
mechanical checks.

## No longer needed

No original import was removed and no module is withdrawn. The direct proof
uses no open-extension compositor, so `lem-cbc-extension-zero-composition`
is removed from this node's direct proof dependencies. The general ringed-topos
composition existence theorem
`lem-weil-pbc-ringed-topoi-derived-pushforward-composition` is likewise replaced
as a direct dependency by the already proved concrete associativity and unit
helpers. These modules may still be needed transitively or elsewhere; this
delivery makes no claim that they can be deleted from the library.

Neither the supplied k-square nor the Q exchange nor the horizontal exchange
pasting clause enters the proof. The fixed unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The DAG's description was mathematically sound,
but its second step listed the open-composition law even though this source-only
calculation needs only vertical exchange pasting and proper direct-image
associativity and its right-unit law. Those concrete helpers already exist, so
no further split of the obligation is needed. All arguments are functorial and
apply equally to empty schemes and identity morphisms.

## Second reading by Z9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
