## What changed

Complete the retirement listed in coord/retire-items.tsv:1560. Withdraw
Sheaf.AlgebraicGeometry.Modules.DeterminantWedgeMorphism via deleted.txt and
redirect lem-sc-determinant-wedge-morphism to the proved adopted theorem in
WeilConjectures.AlgebraicGeometry.Modules.DeterminantWedgeMorphism. Its
local-construction and gluing proof remains the mathematical route.

Adapt the sole direct consumer, DeterminantShortExactExists: privately import
the adopted theorem, obtain its canonical morphism, and transport it through
the existing exteriorSheafPowerIso comparisons to the unchanged legacy formula.
Move the proved private hom-wedge helper from the retired file into the consumer.
Keep its public signature, visibility, public imports and docstring verbatim.
Update the sole parent node to describe this proof. No upstream source file changes.
Change record: coord/changes/B7-retire-determinant-wedge-morphism.md.

The adapted consumer compiles cleanly (4.4 seconds); --all with the empty retired
module also passes. The unchanged next consumer DeterminantShortExact compiles
against the adaptation (3.3 seconds). The original consumer fails against the
empty retired module at line 68: Unknown identifier determinant_wedgeMorphism_exists.
The import-direction check passes. LeanFinder, Loogle and grep searches were
recorded through msearch.py; direct source search found the proved adopted twin
and the required comparison API. The sole DAG parent was checked using actual
stmt_deps, proof_deps and proof-step uses, rather than provenance mentions.

## Proved and sorry left

The assigned item has 0 holes before retirement, and 0 remain. Closed 0, added 0,
split off 0. No remaining sorry in any delivered Lean declaration.
The adapted AlgebraicGeometry.Scheme.Modules.determinant_shortExact_exists
is completely proved; its unchanged public statement has the original wedge
formula for arbitrary quotient lifts. The moved private
exteriorSheafPowerIso_hom_wedge is completely proved. The adopted
AlgebraicGeometry.Scheme.Modules.determinant_wedgeMorphism_exists is the existing
proved replacement, without any changes. This delivery is a retirement repair,
not a new hole closure or a decomposition.

## No longer needed

Retire only Sheaf.AlgebraicGeometry.Modules.DeterminantWedgeMorphism and remove
its private import from DeterminantShortExactExists. Its copied implementation
and private hom-wedge helper are replaced by the adopted theorem and the helper
moved to the consumer. The retired node no longer has a direct proof dependency
on lem-sc-exterior-sheaf-power-comparison; the legacy parent retains and uses it.
Keep lem-sc-determinant-wedge-morphism and the parent's dependency on it, now
attached to the adopted theorem. Keep its local-data and gluing dependencies.

No other module or node is claimed pruned. The historical prerequisite list in
the retirement row is not a list of additional withdrawals: other consumers and
adopted proofs remain unchanged. No top-level tool_uses approval was removed.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief describes a still-open proof split twice, but the current
source has zero holes and the live queue assigns duplicate retirement. The two
signatures differ in their exterior-sheaf representation, so a bare import swap
would not repair the consumer. The existing proved comparison isomorphisms
supply the required transport, including rank zero and empty opens. No false
statement or change to the fixed unit route was found. No current return or
rework entry applies to the item.

## Second reading by B7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
