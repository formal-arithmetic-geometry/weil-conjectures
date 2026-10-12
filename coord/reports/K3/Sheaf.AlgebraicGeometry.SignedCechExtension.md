## What changed

Reduced `AlgebraicGeometry.Scheme.signedCechExtension_differential` to two independently
stated invariants of the full Čech differential. Added proof-only imports of
`Sheaf.AlgebraicGeometry.CechDifferentialPermutation` and
`Sheaf.AlgebraicGeometry.CechDifferentialRepeated`.

The item now proves, in a private helper `signedCechExtension_permutation`, that its
explicit extension transforms by the sign of every permutation. For injective tuples,
Mathlib's equality of sorted permutations and injectivity identify the sorting
permutations; multiplicativity of sign and functoriality of restriction finish the
argument. For repeated tuples, both sides vanish directly. The main proof uses function
extensionality and splits on tuple injectivity. Its injective branch applies differential
permutation compatibility to the sorting permutation; its repeated branch applies
repeated-tuple cancellation. All existing definitions, signatures and visibility are
unchanged. Updated the original node's proof route to agree with this Lean proof.

## Proved and sorry left

Closed the one original syntactic hole:
`AlgebraicGeometry.Scheme.signedCechExtension_differential`
(node `lem-pc-signed-cech-extension-differential`). Also proved the private helper
`AlgebraicGeometry.Scheme.signedCechExtension_permutation` without any new hole.

Added exactly two named holes, each the whole proof of one public theorem in its own
module:

- `AlgebraicGeometry.Scheme.cechDifferential_permutation`, node
  `lem-pc-cech-differential-permutation`, in `CechDifferentialPermutation.lean`.
- `AlgebraicGeometry.Scheme.cechDifferential_repeated`, node
  `lem-pc-cech-differential-repeated`, in `CechDifferentialRepeated.lean`.

This is a decomposition, not an axiom-free proof of differential stability. The net
syntactic hole count is one closed minus two added. Each remaining statement proves
only one invariant of the differential on arbitrary cochains satisfying the stated
conditions; neither restates the signed-extension theorem or defines its input using
that theorem. The proof checking those conditions and assembling the two invariants is
complete Lean. Every delivered module compiles using lcompile.py.

Edge cases were checked in the mathematical statements: empty I gives no tuples;
p = 0 specializes to the two-term difference; no covering, finiteness of I, or linear
order is needed in the two generic lemmas. Repeated-tuple cancellation uses actual
vanishing of repeated input tuples, rather than inferring vanishing from antisymmetry,
which would be invalid in abelian groups with 2-torsion. No data is selected from any
unproved existence statement.

## No longer needed

None. No existing import or dependency node was removed. All four original public
imports serve the existing signatures, construction, or proved sorting helper; the
original Čech complex dependency remains needed. The two new proof imports are both
used. No blueprint unit statement or proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original node's only proof dependency was the construction of the full Čech
complex. Its steps 2 and 3 additionally require deletion-sign reindexing and repeated-pair
cancellation, which that construction does not state. These are now separate theorem
nodes rather than unrecorded glue. The source, Stacks Section 20.23 (01FG), explicitly
omits differential stability verification before Definition 01FH, so both docstrings
and nodes spell out the omitted arguments and mark their origin as agent-written.
Mathlib searches found sorting uniqueness and permutation sign APIs, but no theorem
proving these presheaf differential invariants. LeanSearch was unavailable; LeanFinder,
Loogle, direct Mathlib inspection and searches of both library roots were used.

## New nodes

`lem-pc-cech-differential-permutation` records preservation of permutation equivariance
by the differential, with no linear order or injectivity hypothesis. Its module is
`lean/Sheaf/AlgebraicGeometry/CechDifferentialPermutation.lean`. Its proof plan reindexes
faces through an induced permutation and compares signs by moving the deleted positions
to the end.

`lem-pc-cech-differential-repeated` records vanishing of the differential on repeated
tuples when the input transforms by permutation signs and vanishes on repeated tuples.
Its module is `lean/Sheaf/AlgebraicGeometry/CechDifferentialRepeated.lean`. Its proof plan
pairs the two faces deleting a chosen repeated pair and kills all other faces.

Both nodes inherit the item's chapter, unit and blueprint ancestry. No interface change
record or forced adaptation is needed.

## Second reading by K3

1. Compared `SignedCechExtension.lean` against the repository version. Existing declarations and signatures are unchanged; the two additional modules are new split-off theorem modules, and the DAG records match their Lean statements. Verdict: pass.
2. Compiled all three delivered modules with `lcompile.py --all`; no errors or warnings. The only remaining `sorry`s are the two named public split-off theorems, each documented and represented by a node. No forbidden declarations or hollow definitions occur. Verdict: pass.
3. Checked the two split-off statements on the stated edge cases (p = 0, empty index type, repeated tuples, and possible 2-torsion) and against the existing Cech definitions. They are strictly smaller invariants and do not restate the target. Verdict: pass.
4. Reviewed the proof route and imports. The target proof uses the two split-off invariants, retains the construction dependency, and removes no dependency or unit step. The proof-only imports are used. Verdict: pass.
5. Reviewed the DAG `proof`, `proof_deps`, `proof_origin`, and `lean` records for all three nodes; they agree with the Lean proof and preserve the unit route. Verdict: pass.

Changed only this report by adding this second-reading record; no Lean source or DAG repair was needed.
