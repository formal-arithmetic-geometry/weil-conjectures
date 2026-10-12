## What changed

Kept the existing signature of `AlgebraicGeometry.exists_lerayEdge_isIso_of_vanishing`
byte for byte. Its proof combines the construction of a natural cocycle edge and
collapse for an edge satisfying that cocycle characterization. The new modules are
`Sheaf.AlgebraicGeometry.LerayEdgeCocycleData` and
`Sheaf.AlgebraicGeometry.LerayEdgeVanishingIso`. `LerayEdge` and
`LerayEdgeCocycle` abbreviate the two displayed types with real definitions.
Their sole public prerequisite is `PQFCohomology`; the collapse statement publicly
imports the module defining the edge types. All other added imports are proof-only.

## Proved and sorry left

The sole original theorem, `AlgebraicGeometry.exists_lerayEdge_isIso_of_vanishing`,
has a Lean proof conditional on two strictly smaller named obligations:

- `AlgebraicGeometry.leray_edge_cocycle_data`, node
  `lem-pc-leray-edge-cocycle-data`: existence and the cocycle characterization only.
- `AlgebraicGeometry.leray_edge_isIso_of_vanishing`, node
  `lem-pc-leray-edge-vanishing-iso`: collapse for a specified edge satisfying that
  characterization; it does not construct the edge.

Both remain `sorry`, with sources and natural-language proofs. The delivery does
not claim that the original theorem is axiom-closed.

## No longer needed

Removed the original direct proof imports from `LerayDegenerateSections`:
`ModulePushforwardInjectiveAcyclic`, `TensorPullback`, `GrothendieckComposablePair`,
`GrothendieckEdgeCocycle`, `GrothendieckSpectralSequence`,
`RingedSiteKInjectiveResolutions`, and
`WeilConjectures.CategoryTheory.SpectralSequence.Grothendieck`.
The new construction and collapse modules import the generic edge-cocycle and
pushforward-acyclicity modules privately. Other former imports are available
transitively to those generic arguments.

The original node's direct `proof_deps` are replaced by the two split nodes.
All twelve former dependencies remain in the split nodes' construction/collapse
plans; none is globally pruned or claimed unnecessary. No unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The first worker's collapse statement omitted the cocycle characterization of
its arbitrary natural transformation. This is false: take the zero natural
transformation for the identity of an affine scheme, with a nonzero degree-zero
coefficient module. Positive cohomology vanishes but the zero endomorphism is not
invertible. Added `hε : LerayEdgeCocycle f ε` to this new, unpublished statement
and passed the constructed characterization from the original theorem.

The initial split nodes depended on the theorem being proved, forming a circular
proof plan, and lacked chapter/unit, accurate signature records, real search
records, and full theorem docstrings. Replaced those dependencies by the original
generic construction/collapse ingredients and corrected the records.

## Second reading by A3

1. Compared the original module and the delivery. The existing theorem signature
   is byte for byte unchanged. No existing definitions or statements change.
   The added cocycle hypothesis repairs a new statement not present in the repository.
2. Compiled all delivered modules locally, and inspected every definition and
   theorem body. Only the two reported named theorems contain `sorry`; no hollow
   definitions or forbidden proof mechanisms occur. Axiom probes show only the
   standard axioms and `sorryAx` from those open obligations.
3. Read the new statements and the generic `grothendieck_left_edge_cocycle` and
   `module_pushforward_injective_acyclic` statements. Detected and repaired the
   false arbitrary-edge collapse clause as above. For degree zero and the identity
   of an affine scheme the repaired characterization selects the canonical edge.
   The zero coefficient case is consistent. Neither split restates the target:
   construction lacks collapse, while collapse assumes a specified cocycle edge.
   Actual Mathlib searches via LeanFinder, Loogle, and grep found no applicable
   theorem; LeanSearch returned HTTP 500 and is recorded as unavailable. Reviewed
   repository and upstream cohomology declarations; no specialized duplicate found.
4. Kept the cocycle construction followed by Grothendieck collapse route. Inspected
   `dag/units/sk-thm-picard-rr.json`: its `realized` fields are empty, and no unit
   realization is removed. Pruned redundant direct imports as listed above; the
   generic dependencies remain in the split obligations. Neither split is closed
   by an immediately applicable existing specialization.
5. Updated the original node's proof, proof_deps, and proof_origin. New nodes carry
   exact Lean signatures, chapter/unit, sources, real searches, and noncircular
   proof plans using the original dependencies. Their proof_deps are exactly the
   union of their proof steps' uses.

Changed during second reading: fixed the false collapse statement and its caller;
expanded source/proof docstrings; corrected circular and incomplete DAG metadata;
removed redundant imports; replaced the inaccurate initial report and searches.

## New nodes

`lem-pc-leray-edge-cocycle-data` records only construction of the natural edge and
its universal resolution formula. It uses the original node's first two steps.

`lem-pc-leray-edge-vanishing-iso` records collapse for an edge satisfying that
formula, using the generic Grothendieck edge theorem and uniqueness on cycle
representatives. Both new nodes have chapter `sec-picard-framework` and unit
`sk-thm-picard-rr`. No change record is needed: all existing signatures and
public imports are unchanged; the corrected signature is a new declaration.
