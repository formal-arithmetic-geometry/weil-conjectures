## What changed

Added the proof-only import of `PuncturedMatchingChartRestrictionRingEquiv` and proved `puncturedMatching_chart_restriction_leftInverse` by taking the underlying ring homomorphism of the localized chart ring equivalence.

## Proved and sorry left

The target declaration `puncturedMatching_chart_restriction_leftInverse` is proved. The new declaration `puncturedMatching_chart_restriction_ringEquiv` remains `sorry` and is recorded by node `new-lem-sbc-punctured-matching-chart-restriction-ring-equiv`.

## No longer needed

No imports or nodes were pruned.

## Where the brief, the DAG or earlier work was wrong

The original node's proof plan omitted the necessary explicit ring-equivalence interface between formal-gluing H0 localization and the geometric principal-chart sections; this delivery records that interface as a lower intermediate theorem.

## New nodes

`new-lem-sbc-punctured-matching-chart-restriction-ring-equiv` is stated in `PuncturedMatchingChartRestrictionRingEquiv.lean` and is used by the target proof.

## Earlier second reading (a previous round; superseded)

The target proof is a direct application of the strictly stronger ring-equivalence intermediate statement; the new node and its signature match the delivered module.

## Second reading by G3

1. **No accidental visible changes.** Compared both delivered Lean modules with the repository
versions. The existing target declaration is byte-for-byte unchanged; only its proof and a
proof-only import changed. The additional module is a new split-off declaration and is recorded
by its node.

2. **Compilation and proof audit.** Compiled both modules with `lcompile.py --all`; both compile
successfully. The target has no `sorry`, and the only remaining `sorry` is the named intermediate
`puncturedMatching_chart_restriction_ringEquiv`, with its source, proof plan, docstring, and DAG
node. There are no forbidden declarations or hollow definitions. The target proof uses only
`RingEquiv.toRingHom`; its axioms are therefore limited to those of the imported intermediate
(the unresolved intermediate may account for `sorryAx` until proved).

3. **Statement and search audit.** The target signature is unchanged. The split-off statement is
well-typed, mathematically the required stronger comparison, and its compatibility clause is
exactly the property used by the target. Repository and recorded Mathlib searches found no
existing declaration duplicating it. No weaker replacement or duplicate of the target was added.

4. **Pruning and route.** The proof follows the stated localized-chart comparison route: obtain
the ring equivalence and take its underlying ring homomorphism. The new import is proof-only and
is therefore plain `import`; the public import needed by the statements remains unchanged. No
old proof dependency is unused, and no unit step is bypassed.

5. **DAG agreement.** The target node now records the ring-equivalence node in `proof` and
`proof_deps`; the new node records its theorem, source, proof plan, and exact Lean declaration.
The unit metadata is unchanged.

Changed in this second reading: expanded this report with the five-point audit; no Lean statements
or proofs required repair.
