## What changed

The existing theorem `Algebra.TensorProduct.purelyInseparable_baseChange_localRing`
has exactly its original signature. Its proof combines the structural and residue
conjunctions, imported through two proof-only imports.

The second reading proved `Algebra.TensorProduct.purelyInseparable_baseChange_structural`
directly using Mathlib's tensor basis, finite-basis, flatness, and Noetherianity APIs.
`Mathlib.RingTheory.TensorProduct.Free` is now a proof-only import; so is the added
`Mathlib.RingTheory.Noetherian.Basic`. The redundant basis definition and its node
were removed. The remaining residue theorem has a complete natural-language proof
in its own docstring. The parent DAG now records the proof actually written; both
new nodes have self-contained statements, exact Lean signatures, and explicit steps.

## Proved and sorry left

Closed the original syntactic hole in
`Algebra.TensorProduct.purelyInseparable_baseChange_localRing` by a reduction to
strictly smaller structural and residue conjunctions. The target still depends on
`sorryAx` and is not a completed proof.

Fully proved `Algebra.TensorProduct.purelyInseparable_baseChange_structural`
(node `lem-weil-pbc-purely-inseparable-base-change-structural`), closing the additional
structural hole introduced by the first worker. Its axioms are only `propext`,
`Classical.choice`, and `Quot.sound`.

Added one remaining hole:
`Algebra.TensorProduct.purelyInseparable_baseChange_residue`
(node `lem-weil-pbc-purely-inseparable-base-change-residue`). Its proof is exactly
`by sorry`. No other delivered declaration has a sorry, and there is no definition
with postponed data. Relative to the repository: one original hole closed and one
new hole added, net zero. This is a decomposition, not a completed target proof.

## No longer needed

No existing library module is claimed pruned. The first worker's redundant basis
wrapper `Algebra.TensorProduct.purelyInseparable_baseChange_basis` and its undelivered
node `new-purely-inseparable-base-change-basis` were removed; use Mathlib directly.

All thirteen old direct parent proof dependencies have been replaced by the two
helper nodes. Five remain in the helpers' plans:
`lem-weil-pbc-free-base-change-tower`, `lem-weil-pbc-finite-algebra-noetherian`,
`lem-weil-pbc-tensor-quotient-base-change`, `lem-weil-pbc-tensor-cancel-base-change`,
and `lem-weil-pbc-finite-algebra-local-radical`.

The remaining old proof dependencies are no longer cited in this proof route:
`def-weil-pbc-finite-purely-inseparable-extension`, `def-weil-pbc-free-module`,
`def-weil-finitely-generated-module`, `lem-weil-pbc-projective-module-flat`,
`def-weil-pbc-flat-ring-map`, `def-pc-field-extension`,
`def-weil-vector-space-scalar-extension`, and `def-weil-ring-frobenius`.
Some remain statement dependencies; this does not remove their definitions.
Direct Mathlib basis and free-flat APIs replace the redundant intermediate steps,
and the purely inseparable positive-power lemma replaces the explicit Frobenius
calculation in the residue plan. These are changes below the unit level.

## Where the brief, the DAG or earlier work was wrong

The original delivery unnecessarily left the structural conjunction sorry despite
a short Mathlib proof. Its residue docstring was an outline, not a complete proof.
The new node statements were not self-contained, and the parent node retained the
old proof dependencies instead of recording its actual conjunction reduction.
The basis wrapper duplicated Mathlib's construction. These faults are repaired.

The source uses locality and finite flatness without proving them:
[Stacks Tag 07E5](https://stacks.math.columbia.edu/tag/07E5), proof of (3) => (1).
The expanded proofs are agent-written explanations of those facts, as in the
original node; the source statement is not weakened.

## New nodes

`lem-weil-pbc-purely-inseparable-base-change-structural`: the finite-basis, free,
finite, flat, and Noetherian conjunction of clause (1), fully proved in
`Sheaf.RingTheory.PurelyInseparableBaseChangeStructural`.

`lem-weil-pbc-purely-inseparable-base-change-residue`: the locality, unique prime,
residue map, and closed-fibre conjunction of clauses (2) and (3), with one named
sorry and a full proof docstring in `Sheaf.RingTheory.PurelyInseparableBaseChangeResidue`.
Both nodes replace the first worker's provisional `new-...` identifiers with the
chapter's lemma naming convention. No change record is needed: no existing
signature or definition changed.

## Second reading by G1

1. Compared the target module with the repository using diff and checked its
   signature byte for byte: identical. Only proof-only imports and its proof change.
   No existing definition, statement, visibility, or other module was adapted.
2. Compiled all three modules in import order with lcompile.py. All pass. Scratch
   copies with #print axioms show only the three allowed axioms for the structural
   theorem, and those axioms plus sorryAx for the target and residue theorem.
   No forbidden declaration, unsafe escape, hollow definition, or anonymous hole.
3. Checked the residue helper as a strict subset of the target's conclusion and
   supplied its complete proof. Edge cases checked: k'=k (including characteristic
   zero) gives closed fibre K and residue degree one; A=k reduces to the field k';
   nonreduced local A is allowed because the nilradical argument concerns the fibre,
   not A. Positive degree excludes a zero tensor fibre. Searched Mathlib using fresh
   LeanFinder, Loogle, and grep queries; LeanSearch was unavailable and is recorded
   honestly. Component matches include the positive-power lemma and the spectrum
   homeomorphism, not the whole residue conjunction. Searched lean/ by tensor,
   quotient, locality, and purely-inseparable terminology; no duplicate packaging.
4. Closed the easy structural hole through Mathlib and removed its redundant basis
   wrapper. Imports for proofs are plain imports. No old library module was removed.
   Every old parent proof dependency is accounted for above. Read sk-thm-p1.json
   realized: neither this parent nor either helper realizes a unit statement or
   step, so this reduction below the unit level preserves the unit route.
5. Checked both new nodes' required fields, signatures, self-contained statements,
   sources, steps, and union of uses against proof_deps. Updated the parent's proof,
   proof_deps, and proof_origin to the conjunction proof; no statement field changed.

Second reading changed: proved the structural helper, removed the duplicate basis
wrapper/node, fixed its proof-only import, expanded the residue proof docstring,
repaired both new node records and names, synchronized the parent DAG, and corrected
the report's accounting. The one remaining residue hole is a genuine smaller
argument, not a renamed restatement of the target.
