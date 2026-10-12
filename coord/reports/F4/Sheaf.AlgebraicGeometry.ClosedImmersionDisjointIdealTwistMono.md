## What changed

Proved `AlgebraicGeometry.Scheme.Modules.closedImmersion_disjointIdeal_twist_mono`
without changing its signature or any public import. Added proof-only imports of
`Sheaf.AlgebraicGeometry.ClosedImmersionUnitKernel` and
`WeilConjectures.AlgebraicGeometry.Modules.Dual`. Added two proved private helpers:
`ideal_inclusions_disjoint` and `tensor_ideal_inclusions_disjoint`.

The first helper proves zero intersection of ideal inclusions sectionwise. The second
transports it across the tensor equivalence of an invertible module. The main proof
uses the existing chosen-unit kernel fork, identifies multiplication images with their
monic sources, and proves additive zero cancellation. Updated the existing node's proof,
proof dependencies and proof origin to describe this argument.

Sources checked: [Stacks 09NW](https://stacks.math.columbia.edu/tag/09NW),
[09NX](https://stacks.math.columbia.edu/tag/09NX), and
[08KS](https://stacks.math.columbia.edu/tag/08KS). The local literature checkout lacks the
referenced .tex files, so the official pages were read. The zero-intersection hypothesis
is explicit, so reducedness is not needed in this lemma. The tensor equivalence covers
power zero, empty schemes and zero ideals without additional hypotheses.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.Modules.closedImmersion_disjointIdeal_twist_mono`
(node `lem-sc-closed-immersion-disjoint-ideal-twist-mono`).
One of one original sorries closed; zero new holes; zero split-off statements.
No sorry remains in the delivered module. This is a proof from existing library
statements, including `closedImmersion_unit_kernel`; it does not assert that all
transitive proof dependencies are already sorry-free.

The module compiles cleanly with the launcher compiler. The independent scratch-copy
`#print axioms` checks of the main theorem and both private helpers show exactly
`propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`. The delivery dry run
passes compilation, declaration and axiom checks, and preflight; it reports only
the expected independent second reading, which the second reader supplies.

## No longer needed

Removed the redundant proof-only import
`Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct`; it remains publicly available
through `Sheaf.AlgebraicGeometry.TensorPullback`, so its module is still reached.
No old `proof_deps` node is removed, and no module leaves the target closure. The local
trivializing affine-basis calculation, separatedness gluing, and comparison between
adjunctions in the old plan need not be repeated in this item: the existing kernel theorem
already supplies the geometric kernel calculation for the exact chosen adjunction.
There are no separate old plan nodes or modules to remove for those operations.

## Where the brief, the DAG or earlier work was wrong

The statement and its source calculation are correct. The old proof plan cited mostly
definitions, although the existing kernel theorem and invertible tensor equivalence
supply a shorter route. No statement or definition was changed.

`lem-weil-pbc-closed-immersion-unit-kernel` is used as a generic tool from another unit:
it supplies the chosen pullback-unit kernel for all modules, without replacing any
curve-estimate unit statement or step. `lem-pc-tensor-dual-invertible` supplies the
proved invertible tensor infrastructure in the source library. The curve-estimate unit
record realizes only `thm-sc-proper-cohomology`, with no fixed steps involving this item;
the unit route is preserved. No new nodes or forced adaptations are required.

## Second reading by F4

1. **Interface: pass.** Compared the delivered Lean module with the repository using
   `diff`; independently compared the entire existing theorem signature byte for byte.
   It is identical. There are no new public declarations, definition changes, changed
   public imports, change records or forced adaptations. The two added helpers are private.
2. **Proof and axioms: pass.** Compiled the delivered file locally with `lcompile.py`;
   no errors or warnings. Scanned the delivered sources for forbidden constructs and
   holes: none. A scratch copy prints axioms for both helpers and the main theorem:
   only `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`. The chosen
   dual is an existing proved evaluation isomorphism, not data from an unproved mere
   existence theorem. The existing kernel theorem supplies precisely the same unit.
3. **Split statements and edge cases: pass.** No split-off statement or new hole.
   Read both private helper proofs: sectionwise zero intersection forces the common
   value to zero, and the tensor equivalence transports this via fullness, faithfulness
   and the counit. The zero ideal, zero source, empty scheme and power zero are covered;
   if the closed immersion has empty source, hzero forces I to vanish. Searched Lean
   for ideal/disjoint/tensor and restriction/mono formulations and ran the Mathlib
   search `Disjoint.*(range|ker)|mono.*comp.*kernel|inf_eq_bot.*injective` through
   `msearch.py`; no existing exact sheaf theorem replaces the helpers. The similarly
   named private `ideal_image_disjoint` concerns nonvanishing loci, a different claim.
4. **Route and pruning: pass after report correction.** The proof uses the generic
   existing kernel universal property, monic-source image isomorphisms and tensor
   equivalence; no repeated local geometric calculation is needed. The public imports
   provide the signature's notions; both added imports are proof-only. The redundant
   direct TensorProduct import was removed by the first worker, but remains available
   through TensorPullback. Corrected `No longer needed` to record this. No old
   proof-dependency node is omitted. Read `dag/units/sk-thm-curveestimate.json`:
   realized statement is `thm-sc-proper-cohomology`, and realized steps are empty;
   this below-unit alternative neither replaces nor bypasses a fixed unit step.
5. **DAG: pass.** Compared node JSON against the repository: only `proof`,
   `proof_deps`, and `proof_origin` differ. The three steps follow the two helpers
   and the kernel lift in the main proof, and their uses union equals `proof_deps`.
   All old dependencies remain; added dependencies name the kernel theorem and
   the existing Dual module's invertible tensor infrastructure. No new nodes required.

Second reading changed only the report: recorded the removed redundant import,
recorded the independent axiom results, and appended this review. The Lean proof
and node metadata needed no repair. Closed one original hole, added zero holes.
