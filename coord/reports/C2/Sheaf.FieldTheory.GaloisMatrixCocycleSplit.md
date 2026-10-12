## What changed

Added `Sheaf.FieldTheory.GaloisMatrixCocycleDescent`, splitting the descent construction into a theorem asserting existence of a bijective K-algebra homomorphism. The target module imports it and constructs the requested algebra equivalence with `AlgEquiv.ofBijective`.

## Proved and sorry left

`Field.nonempty_algEquiv_matrix_of_galois_cocycle` is proved from the descent theorem. `Field.exists_algHom_matrix_of_galois_cocycle` remains a single `sorry`, recorded by node `lem-sc-galois-matrix-cocycle-descent`.

## No longer needed

None; the original module had no proof imports beyond its public Mathlib imports.

## Where the brief, the DAG or earlier work was wrong

The DAG proof is a full finite Galois descent argument; it does not expose an intermediate Lean statement. The descent theorem records that missing intermediate explicitly.

## New nodes

`lem-sc-galois-matrix-cocycle-descent`: existence of a bijective base-field algebra homomorphism, used to assemble the target equivalence.

## Second reading by C2

1. The delivered target module was diffed against the repository version. The theorem
statement and all existing declarations are unchanged; only a proof-only import and the
proof body were added. Verdict: pass.
2. Both sandbox modules compile with `lcompile.py`. The target proof has no `sorry`,
`axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`; the split-off theorem is the
single documented `sorry` listed above. Verdict: pass.
3. The split-off statement is a strict reduction: it supplies a base-field algebra
homomorphism together with bijectivity, while the target still packages it as an
`AlgEquiv`. Its hypothesis dependency, docstring, and DAG node are present; searches
found no existing declaration. Verdict: pass.
4. The proof calls `exists_algHom_matrix_of_galois_cocycle` and
`AlgEquiv.ofBijective`; the plain import of the new descent module is therefore minimal
for the proof. No old proof dependency or import became unused. Verdict: pass.
5. The target node's route is preserved: the new node realizes the descent substep and
feeds the existing split-cocycle node, with no unit statement altered. Verdict: pass.

Changed the new node to include its statement dependency and all three required search
records, and added this second-reading record. No Lean statement or definition changed.
