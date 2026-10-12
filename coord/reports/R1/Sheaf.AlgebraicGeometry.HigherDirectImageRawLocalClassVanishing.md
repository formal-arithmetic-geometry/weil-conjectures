## What changed

Replaced the sorry in
`AlgebraicGeometry.Etale.exists_higherDirectImage_raw_local_class_eq_zero`
with a complete proof of the local-to-affine reduction. The existing statement,
docstring, universes and public imports are unchanged.

The private proved helper `covering_of_affine_arrows` uses the affine open cover
and `Scheme.ofArrows_mem_smallEtaleTopology_iff`. The main proof uses
`Presheaf.equalizerSieve_mem` to make the raw limit-zero sieve covering. It
constructs a downward-closed sieve of arrows with a later stage killing all
further restrictions, proves its pullbacks cover by testing on affine objects,
and applies topology transitivity. Evaluating the further-restriction condition
at the identity gives exactly the original conclusion.

Added `Sheaf.AlgebraicGeometry.HigherDirectImageRawAffineRestrictionVanishing`
for the strictly smaller affine continuity step. Its hypothesis is equality
with zero in the raw limit group, and its test object is affine. It asserts
one stage killing that affine restriction and its further restrictions;
it has no sheafification or covering-sieve assertion. The uniformity only
concerns restrictions of one affine object, so no common stage across a cover
is introduced. Updated the original node's proof route and dependencies.

Both modules compile without warnings through lcompile.py: 14.1 seconds for
the intermediate and 20.5 seconds for the item on the last full compile.
No existing interface or definition was changed; no forced adaptations.

## Proved and sorry left

Closed the item's sole hole:
`AlgebraicGeometry.Etale.exists_higherDirectImage_raw_local_class_eq_zero`
(node `lem-sbc-higher-direct-image-raw-local-class-vanishing`).
The private helper `covering_of_affine_arrows` is also proved.

Added one named public hole:
`AlgebraicGeometry.Etale.exists_higherDirectImage_raw_affine_restriction_eq_zero`
(node `lem-sbc-higher-direct-image-raw-affine-restriction-vanishing`).
This is a decomposition: one upper hole closed, one lower hole added, net zero
holes. The item is proved from this intermediate, not yet axiom-free from
proved continuity alone. There are no other sorries in the delivered modules.

The remaining argument is the degree-zero specialization of complex cohomology
continuity after base change to an affine etale test object, with derived
adjunction, canonical-map compatibility and the filtered colimit zero criterion.
Its docstring and node give the proof, including naturality of further
restriction. Edge cases checked mathematically: p = 0 is section continuity;
the empty affine test object has zero raw groups; for a singleton system,
coherence makes the stage and limit maps identify the same class. Arbitrary
further test objects need not be affine, since restriction preserves zero.

## No longer needed

Removed direct proof imports from the item:
`Sheaf.AlgebraicGeometry.EtaleComplexCohomologyLimit` and
`Sheaf.AlgebraicGeometry.AbelianHigherDirectImagePresheaf`.
The first is replaced by the new affine restriction module. Both old plan
nodes, `lem-weil-pbc-etale-cohomology-limit-complex-systems` and
`sbc-lem-higher-direct-image-presheaf`, remain dependencies of the new
intermediate. Neither underlying module is pruned from the full import closure;
there are no globally pruned modules or discarded mathematical plan steps.
The item's direct proof dependency is now only the affine restriction node.

## Where the brief, the DAG or earlier work was wrong

The previous report treated unproved intermediate theory as an obstacle.
The stage permits a proof from named lower statements. The local injectivity,
affine covering criterion, restriction composition, downward closure and
cover transitivity are now real Lean proofs, isolating only affine continuity.

A separate attempted direct naturality calculation unfolded large derived-Hom
expressions and exceeded the single-file time limit. It is not delivered.
The affine continuity intermediate records naturality and zero preservation
in its own mathematical conclusion; the delivered gluing proof uses only
presheaf composition and never unfolds derived pullback. No compiler timeout
limit or library definition was modified.

The module-coefficient raw affine vanishing node
`sbc-lem-higher-image-raw-affine-class-vanishing` has fixed module coefficients
pulled back from a common scheme. It does not supply this varying abelian
coefficient system. The existing abelian raw affine representative node is
surjectivity, not vanishing, so neither is a substitute.

## New nodes

`lem-sbc-higher-direct-image-raw-affine-restriction-vanishing`, in
`dag/nodes/sec-smooth-base-change/`, is realized by
`Sheaf.AlgebraicGeometry.HigherDirectImageRawAffineRestrictionVanishing`.
It isolates affine raw cohomology continuity and its stability under restriction
from the local sheafification and covering argument. Sources checked:
[Stacks 09Z1](https://stacks.math.columbia.edu/tag/09Z1) and
[Stacks 0EZM](https://stacks.math.columbia.edu/tag/0EZM).
LeanFinder, Loogle and source grep produced no matching theorem; LeanSearch was
unavailable and is recorded as unavailable. Blueprint searches for raw affine
and affine cohomology continuity found no duplicate. The original unit's
realized lists are empty, and its route is preserved. No change record is
required because existing interfaces are unchanged.

## Second reading by R1

1. **Interfaces — pass.** Compared every delivered existing module and node with the
repository by `diff`. The existing theorem signature is byte-for-byte identical,
including all hypotheses, universes and its conclusion; its docstring and public
imports are unchanged. Only its proof, a private proved helper, private proof
imports, and the node's proof route fields differ. No definitions or existing
interfaces change, so there is no change record or forced adaptation.
2. **Proof and axioms — pass as a decomposition.** Independently compiled both
modules together in import order with lcompile.py, without errors or warnings
(14.3 and 18.9 seconds). Scratch-copy `#print axioms` checks show the affine-cover
helper uses only propext, Classical.choice and Quot.sound; the item and the new
intermediate additionally use sorryAx, as expected from the named open lemma.
Text inspection finds exactly the reported one public theorem sorry, no hollow
definitions, and no forbidden declaration or implementation mechanism. There is
no arbitrary witness chosen from an open existence theorem in any definition.
3. **Split lemma — pass.** Read its full signature, docstring, DAG node, and the
statements of the continuity and higher-image-presheaf dependencies. Checked
Stacks 09Z1 and 0EZM directly: base change to affine W gives qcqs stage schemes,
and the degree-zero complex system has a common lower bound. Continuity detects
a zero raw class at a later stage. Naturality then kills every further restriction
with that same stage, even when V is not affine. Checked p = 0, empty W, singleton
systems, and z = 0; none requires an extra hypothesis. This is strictly smaller
than local sheafified vanishing: it treats one affine raw-zero restriction and
contains no covering conclusion. Repeated LeanFinder with a changing-coefficient
filtered-cohomology query, Loogle for equalizerSieve_mem, and Mathlib grep for
cohomology continuity/colimit; also searched project source under different
names and read the fixed-module-coefficient affine vanishing theorem. No existing
statement supplies this varying abelian coefficient result. Formalizing the
remaining derived-adjunction and canonical-map identifications is substantial,
so the lower hole remains explicitly open.
4. **Route and pruning — pass.** Followed the proof from the target: local
injectivity gives its equalizer cover; affine open covers establish coverage of
the pullback of the downward-closed eventual-zero sieve; transitivity finishes.
The identity restriction supplies exactly the target witness. The removed two
direct dependencies are both listed in No longer needed and retained under the
new intermediate; neither module is globally pruned. Checked sk-lem-failure-field
and its realized fields (empty statement and step lists): the higher-image limit
continuity step remains the same, with no chapter or unit route bypass.
5. **Nodes — pass.** The original node's proof, proof_deps and proof_origin match
the sieve construction in Lean. The new node has the required source, complete
proof steps, union of their dependencies, search records, provenance, attachment,
chapter/unit and verbatim Lean signature. Its single sorry matches the report.

Second reading changed only this report, adding the independent checks and
verdicts. The Lean proof and node records needed no repair. One upper hole is
closed and one strictly smaller lower hole added: net zero, a decomposition,
not an axiom-free proof or a globally pruned module.
