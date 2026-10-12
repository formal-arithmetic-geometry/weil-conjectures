## What changed

Completed the proof of `Algebra.exists_gabber_upstairs_tensor_relation` in
`lean/Sheaf/RingTheory/FiniteGabberUpstairsRelation.lean`. The proof uses the
flat split neighbourhood, faithful-flatness criterion, integral polynomial
annihilation, and explicit tensor coefficient construction. No public imports
were changed.

## Proved and sorry left

Proved `Algebra.exists_gabber_upstairs_tensor_relation` (the sole declaration
of the item). Closed the original hole in `Algebra.exists_gabber_upstairs_tensor_relation`; added one hole,
`Algebra.exists_flat_split_gabber_neighbourhood`, in the new module, with node
`lem-weil-pbc-gabber-flat-split-neighbourhood`. This is a decomposition (one hole closed,
one added; net zero), not an unconditional proof.

## No longer needed

No Lean imports removed and no modules claimed globally pruned. All proof imports are used.
The target node no longer directly uses these old proof dependencies:
`def-weil-finitely-generated-module`, `lem-weil-pbc-etale-algebra-flat`,
`lem-weil-pbc-finite-algebra-is-integral`, `lem-weil-pbc-flat-faithfully-flat-maximal-ideals`,
`lem-weil-pbc-flat-ring-map-comp`, `lem-weil-pbc-integral-extended-ideal-element-monic`,
`lem-weil-pbc-lift-idempotent-upstairs`, `lem-weil-pbc-localization-flat`, and
`lem-weil-pbc-nakayama-one-plus-ideal-annihilator`. The neighbourhood construction
still needs idempotent lifting, Nakayama, and flatness in its mathematical plan;
the later polynomial and faithful-flatness steps use Mathlib directly.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt had only polynomial-degree and tensor-normalization goals
remaining. These were resolved by explicit monic degree rewriting and the
`TensorProduct.includeRight` ring hom.

## Earlier second reading (a previous round; superseded)

The completed relation proof preserves the target signature and uses the flat
split neighbourhood exactly as its stated intermediate dependency. The
intermediate declaration is recorded as a new node below.

## New nodes

`lem-weil-pbc-gabber-flat-split-neighbourhood` records
`Algebra.exists_flat_split_gabber_neighbourhood`, which remains a documented
intermediate sorry required by the completed proof.


## Second reading by Y3

1. **Statements and accidental changes.** Compared the delivered module with the repository version. The public theorem signature and its documentation are byte-for-byte unchanged; only proof imports, private helper theorems, and the proof body were added. The new flat-split module is an explicitly documented intermediate statement.
2. **Proof checks.** Compiled both delivered modules with `lcompile.py --all`; compilation succeeds. The proof contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or hollow definition. Explicit `#print axioms` scratch checks show `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx` for both public theorems. The `sorryAx` comes from the one new flat-split hole; no other axiom occurs.
3. **New statement.** Reviewed `Algebra.exists_flat_split_gabber_neighbourhood`: its hypotheses and conclusion match the downstream construction, and its docstring gives the source and complete mathematical route. It is strictly a lower-level decomposition and does not restate the target. No duplicate declaration was found in Mathlib or the library.
4. **Route and pruning.** The proof uses the flat-split neighbourhood required by the unit route, then faithful-flatness, the integral polynomial annihilator, and tensor coefficient construction. All proof-only imports are used. The old DAG dependencies for etale flatness, finite-integral, localization, composition, Nakayama, idempotent lifting, and maximal-fibre faithful flatness are no longer needed as separate declarations: the delivered proof uses the flat-split intermediate node and Mathlib directly.
5. **DAG agreement.** The target node's proof follows the declarations used in the module. The intermediate node records the matching Lean declaration, source, proof route, chapter, and unit. Its status is split because the declaration remains an explicitly documented sorry dependency.

Changed in this reading: corrected the intermediate node status to `split`, synchronized the target node proof and proof dependencies with the delivered proof, and added the required second-reader record. No Lean declarations or target statements were changed.

Verification follow-up: independently searched with `leanfinder` for finite-algebra idempotent lifting/localization and with `loogle` for the quasi-finite etale splitting theorem. The latter is a prime-local result, not this quotient-preserving neighbourhood. Read Stacks 0EM0 in the locally available literature copy and checked the unit realized records: none of the removed direct dependencies realizes a unit step. Edge cases I = top, I = bottom, zero base, and zero factors cause no contradiction; the construction allows zero rings. Corrected the hole accounting and explicit axiom result in the report.
