## What changed

The unchanged statement `Polynomial.adjoinRoot_crt_matrix` is reduced to root
coordinates and their consequence for multiplication by the prescribed lift.
The new statements each have their own modules:
`Sheaf.RingTheory.AdjoinRootCRTRootBlock` and
`Sheaf.RingTheory.AdjoinRootCRTLiftBlock`. The item imports both privately for its
proof. The lift module imports Mathlib's reindex equivalence privately for its
proof; its public imports only supply its signature.

The first worker's lift helper was false: it asserted the conclusion for every
invertible U, without requiring the root-coordinate identity. The repaired helper
`Polynomial.adjoinRoot_crt_matrix_lift_block` assumes that identity and is fully
proved using `AdjoinRoot.ringHom_ext`. Coprimality is not needed in this consequence.
Only the actual construction of root coordinates remains open.

## Proved and sorry left

Hole closed relative to the repository: `Polynomial.adjoinRoot_crt_matrix`, node
`lem-weil-pbc-adjoinRoot-crt-matrix`, by combining the two intermediate statements
with the same d and U and supplying the root identity to the lift theorem.

Hole added: `Polynomial.adjoinRoot_crt_matrix_root_block`, node
`lem-weil-pbc-adjoinRoot-crt-matrix-root-block`, in
`Sheaf.RingTheory.AdjoinRootCRTRootBlock`. Its whole proof is `:= by sorry`, with a
source and complete natural-language construction in its docstring.

Fully proved without any sorry dependency:
`Polynomial.adjoinRoot_crt_matrix_lift_block`, node
`lem-weil-pbc-adjoinRoot-crt-matrix-lift-block`, in
`Sheaf.RingTheory.AdjoinRootCRTLiftBlock`.

This is a decomposition, not a completed proof of the item: one original hole is
closed and one strictly smaller root-coordinate hole is added, for net zero holes
closed in the import closure. Compared with the first worker's draft, the false
lift hole is removed, and there is one remaining split-off obligation instead of
two. No data are chosen from an unproved existence theorem in any definition.

The axiom checks show only propext, Classical.choice and Quot.sound for the lift
helper. The root helper and the item also depend on sorryAx, solely through the
named root-coordinate obligation.

## No longer needed

No existing imports or modules are pruned. The parent's old direct proof dependency
`lem-weil-pbc-monic-quotient-free` is now used in the root-coordinate node's plan;
it remains needed transitively, through Mathlib's `AdjoinRoot.powerBasis'`.
The parent's proof_deps now consist exactly of the root and lift nodes.
Both new nodes' circular proof dependencies on their parent were removed.
The unit's realized route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The first worker's draft confused the existence of suitable root coordinates with
an arbitrary choice of invertible U. For example, take A = Q, I = 0,
f = X*(X-1), g = X, h = X-1, and e = 1-root f. Its residues are one and zero.
With the usual index order and U = 1, the multiplication matrix of e in the
basis (1, root f) is [[1,0],[-1,0]], not [[1,0],[0,0]]. Thus the unpublished
`adjoinRoot_crt_matrix_second` statement was false. Supplying the root conjugation
identity makes the assertion true: conjugated multiplication and the block map
are ring homomorphisms agreeing on scalars and the generator.

The original nodes did not describe the Lean reduction: the parent retained its
old proof plan, while both helpers depended on that parent, forming a cycle.
They also lacked adequate independent proof docstrings. All three proof records
now describe the actual reduction and the remaining construction without a cycle.
No existing library statement, definition, or target is changed.

## New nodes

`lem-weil-pbc-adjoinRoot-crt-matrix-root-block`: the root-coordinate construction,
without e or its lift-coordinate conclusion, in its own module. Monic division,
CRT and power bases give its complete mathematical proof, including empty factors.

`lem-weil-pbc-adjoinRoot-crt-matrix-lift-block`: the proved consequence of a supplied
root-coordinate identity, in its own module. The proof uses Mathlib ring homomorphism
extensionality and scalar/block matrix identities. It is not a restatement of the
parent and is independent of the root helper's sorry.

No change record is required: all existing declaration signatures, definitions,
visibility and public imports are unchanged. The two corrected declarations were
new, unpublished statements in the first worker's sandbox.

## Second reading by V3

1. Compared every delivered module against the repository. The item is the only
existing module changed. Its theorem signature is byte for byte identical and its
original docstring and public imports are preserved. The two new declarations
were moved to new modules. No existing definition or target changed. Verdict: pass.

2. Compiled all three modules in dependency order with lcompile.py, without errors
or warnings. Scanned for forbidden declarations and sorry in data: none. There is
exactly one textual sorry, the entire public named root theorem proof. Scratch
#print axioms checks give only the three allowed axioms for the proved lift theorem,
and those three plus sorryAx for the root theorem and item. Verdict: pass for the
reported decomposition; the item remains dependent on the named root obligation.

3. Independently checked the root-coordinate claim and its construction, including
g = 1, h = 1 and f = 1 (empty bases), and arbitrary nonzero residue rings. Found the
original lift helper false by the Q example above; repaired it by requiring the
root-coordinate identity and proved it. Ran new leanfinder, loogle and grep searches
with different queries, and searched the upstream and Sheaf sources. Mathlib has
CRT, power bases, matrix reindexing and generator extensionality, but no duplicate
of the remaining root-coordinate theorem. LeanSearch was unavailable and is
recorded as unavailable without an absence claim. Verdict: pass after repair.

4. Read the top theorem first and the unit sk-thm-p1's realized entries. The proof
constructs root coordinates, then derives the lift identity from generator
extensionality, using no new lift hole. The remaining root theorem is strictly the
first CRT coordinate part of the parent's argument. No unit step is bypassed.
Proof-only imports are private; new module imports were reduced and recompiled.
No old module is pruned; the old power-basis dependency remains transitively needed.
Verdict: valid decomposition with no net hole reduction.

5. Checked the three node records against the exact Lean signatures and proof
bodies. Updated the parent's proof, proof_deps and proof_origin; rewrote the new
nodes with self-contained statements, independent proof plans, correct signatures,
new module paths, sources and actual search records. Removed both parent-helper
cycles. The union of each node's step uses equals its proof_deps. Unit and chapter
records are unchanged. Verdict: pass.

Changes by the second reader: repaired and proved the false lift helper; supplied
its root-coordinate premise in the main proof; moved both new declarations to
separate modules; restored the original theorem's docstring attachment; supplied
complete helper docstrings; corrected the DAG, import visibility and progress report.
