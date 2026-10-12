## What changed

Replaced the hole in `AlgebraicGeometry.Smooth.exists_noetherian_section_component_stable_locus`
with an explicit fibrewise locus and a reduction following Stacks 055Q: trace strict
specialization by a DVR, apply the existing cartesian section-component equality, compare
sections over the trait, and transport the connected component by the first projection.
Both existing public signatures and visibility are unchanged. Only three private proof
imports and the core proof change in the item module; its wrapper proof is unchanged.

Three new modules provide the tracing theorem (`NoetherianSpecializationTrait`), the
trait comparison (`SmoothTraitSectionComponents`), and the remaining generic-connectedness
input (`ConnectedGenericFibreTrait`). The first two have complete Lean proofs. The core
and wrapper nodes now describe their actual reductions. No definition, statement, unit,
chapter, or change record is changed.

## Proved and sorry left

Closed the existing local hole:
`AlgebraicGeometry.Smooth.exists_noetherian_section_component_stable_locus`
(node `lem-sbc-smooth-section-component-noetherian-generalization-core`).
`AlgebraicGeometry.Smooth.section_component_generalization_of_isNoetherian` remains proved
from that core, with its original proof.

The new declarations `AlgebraicGeometry.exists_trait_of_strict_specializes` and
`AlgebraicGeometry.Smooth.trait_sections_mem_same_generic_component` have no local holes.

Added exactly one named whole-theorem hole:
`AlgebraicGeometry.connectedSpace_generic_fibre_of_flat_trait`
(node `lem-sbc-connected-generic-fibre-trait`). This is the complete list of remaining
sorries in the delivery. Its docstring gives the source and full denominator, gluing,
and nonemptiness proof. It concerns arbitrary connected flat schemes over a DVR with
reduced closed fibre, without sections, smoothness, or noetherian specialization arguments.
It is strictly a part of the argument, not a restatement of the item.

This is a decomposition: one upper hole closed, one lower hole added, net zero. The tracing
theorem uses only standard axioms; the trait comparison and both item declarations also
use `sorryAx` through this one documented lower hole. The available ring idempotent-extension
lemma does not supply the remaining scheme affine identifications and gluing.

## No longer needed

No old repository import, proof dependency, or module is pruned: the original core node
had no proof dependencies and the item had only the necessary public Smooth import.

The second reading removed the undelivered redundant module
`Sheaf.AlgebraicGeometry.SectionComponentBaseChangeAscent` and its new node
`lem-sbc-section-component-base-change-ascent`. Its proof was just the existing proved
`AlgebraicGeometry.section_component_preimage_of_isPullback` in
`Sheaf.AlgebraicGeometry.SectionComponentPullback`. The core now uses that declaration
directly and records `lem-sbc-section-component-cartesian` as its dependency. This removes
one proposed new module, not an existing reachable library module.

## Where the brief, the DAG or earlier work was wrong

The original core was marked split but had no proof dependencies for its geometric
argument. This delivery exposes the actual tracing, cartesian base change, trait comparison,
and continuous-image steps, leaving only Tag 055J open.

The earlier report and new ascent node described a standalone rational-component proof,
but the sandbox ascent proof had already become a wrapper around the repository's cartesian
theorem. The second reader removed that redundant wrapper and corrected the records.
`SlicingFlat` remains unusable because importing it is cyclic; the now available
`SectionComponentPullback` supplies exactly the needed cycle-free theorem.

No data are chosen from an unproved mere-existence theorem. The locus and open component
are explicit; the DVR existence theorem is proved; the lower hole supplies only a proposition.
The unit `sk-prop-normal-form` already has empty realized arrays. This delivery preserves
its slicing/component-openness route and leaves those pre-existing records unchanged.

## New nodes

`lem-sbc-noetherian-specialization-trait`: the proved affine-chart reduction to
`Ideal.exists_isDiscreteValuationRing_of_lt` (Stacks 054F).

`lem-sbc-smooth-trait-section-components`: the proved open connected-component construction,
section factorization, and continuous-image comparison (Stacks 055Q), using the next node.

`lem-sbc-connected-generic-fibre-trait`: Tag 055J, connected generic fibre of a connected
flat scheme over a DVR with reduced closed fibre; the only unproved new theorem.

All three nodes include source, self-contained statement, proof, dependency union,
proof origin, searches, creation/blueprint records, and verbatim Lean signatures.
No change records or forced adaptations.

## Second reading by S3

1. Compared the delivered item with the repository by `diff -u`. Both existing signatures,
   docstrings, visibility, and wrapper proof are byte-for-byte unchanged. All other delivered
   modules are new. No target or public definition changes. Verdict: pass.
2. Compiled the delivered modules in import order and checked scratch copies with
   `#print axioms` for every public declaration. Only `propext`, `Classical.choice`,
   `Quot.sound`, and the documented `sorryAx` occur. A source scan finds exactly the
   one named whole-theorem hole, no hollow definitions or prohibited declarations.
   Verdict: pass as a decomposition, not a complete standard-axiom proof.
3. Read [Stacks Tag 055J](https://stacks.math.columbia.edu/tag/055J) directly and verified
   the minimal-denominator and unique-gluing argument. Lean's nonemptiness conclusion
   follows from a nonzero flat affine algebra embedding into its generic localization.
   Empty total space is excluded; empty closed fibre is allowed; equal specializations
   are handled before tracing. Re-searched with LeanFinder for extension of clopen
   partitions over valuation traits, Loogle for ConnectedSpace/IsReduced, and `rg` for
   generic connectedness and idempotents. No ready-made scheme Tag 055J theorem was found;
   the ring extension lemma exists but completing scheme gluing is not a few-minute repair.
   The existing cartesian theorem was found and used directly. Verdict: pass after repair.
4. Read the proof top-down: each geometric reduction is real and follows the slicing
   route. Private imports supply only proofs; public imports supply signature notions.
   Removed the redundant ascent wrapper rather than adding another version of an existing
   theorem. No old proof dependency is unused, and the No longer needed section is complete.
   The unit's existing realized fields are unchanged. Verdict: pass after repair.
5. Checked each node against its Lean signature and proof. The core's dependency union
   now names tracing, the existing cartesian theorem, and trait comparison; comparison
   names only the generic-connectedness hole; the wrapper names the core. All new node
   records meet the standing brief. Verdict: pass after repair.

Second reading changed the core to use the existing cartesian theorem directly, removed
one redundant new module/node, updated the core dependency record and report, and replaced
a deprecated simp lemma. No existing public signature changed. Holes closed: one; added:
one; net zero. Existing library modules pruned: none.
