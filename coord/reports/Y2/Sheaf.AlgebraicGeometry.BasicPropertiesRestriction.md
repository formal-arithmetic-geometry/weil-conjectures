## What changed

Replaced the sorry in `moduleCohomologyFMap_basic_restriction` with a reduction
using `Adjunction.leftAdjointUniq`, target-isomorphism naturality, and
`Adjunction.unit_leftAdjointUniq_hom_app`. The existing signature is byte for
byte unchanged. The only new import in the item is the proof-only import
`Sheaf.AlgebraicGeometry.RestrictionNaturality`. The new module states the
resolution-comparison step independently of the downstream functoriality module.
The second reader expanded its source-based proof documentation and updated
both DAG proof plans.

## Proved and sorry left

Hole closed: `AlgebraicGeometry.Scheme.Modules.moduleCohomologyFMap_basic_restriction`
(node `lem-weil-pbc-module-cohomology-fmap-basic-restriction`). Its body is now
proved conditionally on the new lemma.

Hole added and still open:
`AlgebraicGeometry.Scheme.Modules.moduleCohomologyFMap_target_iso_naturality`
(node `lem-weil-pbc-module-cohomology-fmap-target-iso-naturality`, new module
`Sheaf.AlgebraicGeometry.RestrictionNaturality`). Its proof is exactly `by sorry`.
No other holes are introduced. This is a decomposition: one original hole closed,
one lower hole added, net zero holes closed. The original module has 1 of 1
original theorem bodies filled, but is not axiom-free because of this dependency.

## No longer needed

No original Lean import was removed; no module is claimed as pruned from the
actual targets import closure. The old item-node proof dependencies no longer
used directly are:

- `def-pc-module-pullback`
- `def-weil-sheaf-of-modules-category`
- `lem-weil-pbc-acyclic-map-to-injective-nullhomotopy`
- `lem-weil-pbc-derived-functor-map-via-lift`
- `lem-weil-pbc-kinjective-hom-derived`
- `lem-weil-pbc-lift-along-injective-quasi-iso`
- `lem-weil-pbc-lift-to-injective-unique-up-to-homotopy`
- `lem-weil-pbc-module-pushforward-injectives-sections-quasi-iso`
- `lem-weil-pbc-scheme-modules-enough-injectives`
- `pqf-def-cohomology`

The derived-functor and K-injective comparison dependencies now belong to the
new lower lemma; several other dependencies remain transitive through the map
construction. This list is pruning of the item's proof plan only, not a claim
that the corresponding modules are unreachable from the targets.

## Where the brief, the DAG or earlier work was wrong

The first delivery omitted the update to the existing node, overstated progress
as a proof rather than a decomposition, and gave only a sketch for its new hole.
The new proof separates the adjunction comparison from the resolution comparison.

`moduleCohomologyFMap_target_naturality` in
`Sheaf.AlgebraicGeometry.ModuleCohomologyFMapFunctorial` already proves the
broader coefficient-morphism result, but that module imports
`ModuleCohomologyFMapBasicProperties`, which imports this item. Likewise
`ModuleCohomologyFMapDataTargetNaturality` imports that functoriality module.
Neither is usable here without a cycle. The new lemma only isolates the
isomorphism comparison step; it neither constructs the adjunction isomorphism
nor proves the unit equation, so it does not restate the item.

## New nodes

`lem-weil-pbc-module-cohomology-fmap-target-iso-naturality` states the
comparison for a fixed scheme map, h-map, coefficient isomorphism and degree.
Its docstring gives the resolution lifts, K-injective comparison, homotopy
uniqueness, cancellation and derived-functor transport argument. Searches in
Lean Finder, Loogle and local Mathlib/library sources were repeated with new
queries and recorded in the node. No change record is needed: no existing
statement, definition or public import changed.

## Second reading by Y2

1. Compared the entire item with the repository by diff. Only its proof,
   proof documentation and a plain import changed. Checked the signature from
   `theorem` through the conclusion byte for byte; all hypotheses, quantifiers,
   the existential isomorphism, the chosen tensor adjunction and the equality
   orientation are preserved. The second delivered module is new.
2. Compiled both modules in import order through lcompile.py. Checked the source
   for forbidden declarations and data holes. The sole remaining sorry is the
   named lower theorem listed above. Scratch `#print axioms` checks and the
   delivery tool's declaration probe verify the allowed axioms, with sorryAx
   admitted only because that named comparison remains open.
3. Read the new lemma against the definition of ModuleCohomologyFMapData.map
   and the Stacks sources, Lemma 01F8 and Remark 01FB
   (https://stacks.math.columbia.edu/tag/01F8 and
   https://stacks.math.columbia.edu/tag/01FB). It is true: comparing resolution
   lifts gives both commuting homology squares; invertibility of the vertical
   maps and naturality of the derived resolution isomorphisms give the result.
   Checked the identity isomorphism (reflexivity by functor laws), zero h-map
   (both sides zero), degree zero (naturality of ordinary sections), and empty
   source scheme (zero section groups). None requires a new hypothesis.
   Repeated alternative searches; the broader existing result is cyclic here,
   as detailed above. The lower statement isolates a part of the argument,
   leaving the actual adjunction construction and unit calculation to the item.
4. Read from the target downward: the proof constructs the canonical isomorphism
   and reduces its equality with Mathlib's unit equation. No shorter independent
   library naturality theorem was found. Imports are minimal: the public map
   import supplies the signature and the plain new import supplies its proof.
   Read dag/units/sk-thm-p1.json: neither the item nor any dependency removed
   from its direct proof plan is a realized statement or step of that unit.
   The unit's realized nodes and all chapter/unit steps are unchanged.
5. Updated the existing node's proof, proof_deps and proof_origin to the exact
   reduction. Updated the new node's self-contained statement, resolution
   comparison steps, dependencies, search evidence and audit fields. Its Lean
   record matches the new declaration verbatim. No existing statement or
   statement dependency was changed. Checked that proof_deps is the union of
   each node's proof-step uses.

Changes by this reader: expanded the new theorem's proof docstring, added its
module docstring, replaced the item's outdated proof description, repaired both
DAG proof plans and new-node metadata, and rewrote this report to count the
decomposition honestly and list every old dependency no longer directly used.
The original worker's Lean proof body was retained unchanged.
