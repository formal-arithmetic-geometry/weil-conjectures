# Stage 1 report

1. Files written: the item node, `lem-sc-matrix-rank-minor-locus` (statement, no Mathlib match), `lem-sc-finite-dimensional-complex-homology-rank` (statement, no Mathlib match), and `citations.json`.
2. Attachments: none.
3. WANTED: none; the Stacks source `literature/stacks-project/perfect.tex`, Tag 0BDI, is present.
4. The imported item had no proof. I checked the source-repository implementation in `WeilConjectures/AlgebraicGeometry/Modules/FreeComplex.lean`: it proves a scheme-level local inequality, but not this affine finite-union statement, so there is no exact attachment. Searches of the DAG found no existing determinantal rank-locus or finite-dimensional homology dimension node. Both new nodes are statement-only as required.

## Review by M1

I read Stacks Tag 0BDI and the source-repository file `WeilConjectures/AlgebraicGeometry/Modules/FreeComplex.lean` around `exists_finrank_homology_pullback_le`. The item keeps the affine formulation from the DAG. Step 1 uses the exact rank formula in `lem-sc-finite-dimensional-complex-homology-rank`; its finite-dimensional vector-space hypotheses are supplied after tensoring the finite-free terms with a residue field. Step 2 uses the exact finite-union-of-principal-opens statement in `lem-sc-matrix-rank-minor-locus`; the matrices are the two adjacent differentials after choosing finite bases. Step 3 combines those statements with the elementary identity `D(f) intersection D(g) = D(fg)` and a finite enumeration of possible ranks. I verified the zero-size and empty-minor cases are covered by the new rank-locus statement, and that boundedness makes only finitely many degrees relevant. Mathlib searches were run with LeanFinder, Loogle, and grep for each new node and recorded verbatim in their JSON. No source or statement correction was needed.

## Not duplicates

lem-sc-finite-dimensional-complex-homology-rank vs lem-sc-finite-free-complex-homology-upper-semicontinuous: the new node is the finite-dimensional vector-space rank identity used in the proof, while the item asserts upper semicontinuity for residue-field fibres and quasi-compact principal-open sublevel sets.
lem-sc-finite-dimensional-complex-homology-rank vs lem-sc-perfect-jump-loci: the new node is a linear-algebra identity for one complex over a field, while the existing node asserts arbitrary-base-change and local constructibility for pseudo-coherent complexes on schemes.
lem-sc-matrix-rank-minor-locus vs lem-sc-finite-free-complex-homology-upper-semicontinuous: the new node describes rank conditions for one finite matrix as a finite union of principal opens, while the item combines two such conditions with a homology-dimension formula.
lem-sc-matrix-rank-minor-locus vs lem-sc-perfect-jump-loci: the new node is the determinantal affine rank-locus ingredient, while the existing node is the global jump-locus theorem for derived fibres.

## Second reading by M1

- Item statement: checked against Stacks Tag 0BDI (Lemma jump-loci), including the affine finite-free specialization and all hypotheses; verdict: correct.
- Step 1: checked the homology dimension formula against `lem-sc-finite-dimensional-complex-homology-rank`; the residue-field reduction and finite-free matrix representation are valid; verdict: correct.
- Step 2: checked the determinantal rank-locus claim against `lem-sc-matrix-rank-minor-locus`; finite intersections satisfy $D(f)\\cap D(g)=D(fg)$; verdict: correct.
- Step 3: checked the finite rank enumeration and inequality against the two cited statements; the $r=0$, zero complex, and empty-minor cases are covered; verdict: elementary and correct.
- `lem-sc-finite-dimensional-complex-homology-rank`: checked statement and edge cases (zero spaces and adjacent zero maps) against Tag 0BDI; verdict: correct, no Mathlib declaration found.
- `lem-sc-matrix-rank-minor-locus`: checked statement for $r=0$, $r>\\min(m,n)$, and zero matrices against Tag 0BDI; verdict: correct, no Mathlib declaration found.
- Searches for existing nodes were made with `rg` over `dag/nodes`; no duplicate rank-locus or finite-dimensional homology statement was found.

Changes made: reviewed the statement dependencies and retained the repository-required definition citation for the complex and linear-algebra notions. The proof steps, citations, and Mathlib search records required no changes.
