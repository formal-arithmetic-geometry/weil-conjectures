## What changed

Proved `HomologicalComplex₂.doubleComplexCokernelHomologyIso` without changing its
signature. Added private, fully proved helpers for coordinate transposition of the
zig-zag direct sum, cycles, boundaries and quotient, its naturality, and bijectivity
of the endpoint map under exact rows. The final proof composes the inverse flipped
endpoint isomorphism, the transpose isomorphism and the row endpoint isomorphism.
Naturality follows by cancelling the flipped endpoint isomorphism and composing
three squares. Added the proof-only Mathlib ShortComplex.ModuleCat import to use
exactness as an elementwise boundary-preimage criterion. Updated the node proof and
proof dependencies to match the Lean proof.

## Proved and sorry left

Closed the one original hole: `HomologicalComplex₂.doubleComplexCokernelHomologyIso`
(node `lem-weil-pbc-double-complex-cokernel-homology-iso`). No sorry remains in the
item, and no hole was added. All private helpers are proved. This is a proof from
existing stated dependencies, not a decomposition into new holes. The existing
`row_cycle_lifts_to_zigzag`, `zigzag_trivial_if_row_boundary`, and
`exists_zigzagToRowCokernel` remain the next proof dependencies, as intended by the
stage. `zigzagMap` also uses the existing `zigzagTotalMap_preserves` theorem.

Local compilation passes with no warnings. All degrees, including zero, and the
independent module universe are retained. The boundary-preimage argument uses
`homologyIsCokernel (n + 1) n`, so it also covers degree zero directly.

## No longer needed

Removed direct imports `Sheaf.Algebra.Homology.ZigzagModuleFunctorial` and
`Sheaf.Algebra.Homology.ZigzagModule`; the latter's definitions are already publicly
imported by the three used dependency modules, so its node remains needed.
The proof no longer uses the conjunction theorem
`HomologicalComplex₂.zigzagModule_functorial`: transpose naturality is proved on
representatives. Its node remains a proof dependency because `zigzagMap` uses
`zigzagTotalMap_preserves`, the preservation clause assigned to that node. This module may still be reached through
`ZigzagTrivialIfRowBoundary`; no claim is made that it is globally unreachable.
No other node or module was pruned. The unit's own statement and realized steps are
unchanged; this node is a tool below the unit level.

## Where the brief, the DAG or earlier work was wrong

The DAG called the transpose identification elementary but its landed direct-sum
and quotient representations require nontrivial Lean glue. That glue is now proved
locally rather than left as a new hole. Its original functoriality step cited the
large zigzag functoriality theorem unnecessarily: only the existing endpoint map's
naturality plus the coordinate-swap calculation is needed. No statement or
definition was changed. The original source's sign/index slips were already
recorded in the node; the proof uses the landed plus-sign boundary definition.

Searches run through msearch: LeanFinder for exact-row/column cokernel homology
returned single-complex exactness and homology-sequence lemmas; Loogle for
HomologicalComplex₂ returned the bicomplex flip API, but no theorem of this type;
grep for zigzag and exact rows/columns found no direct replacement. Source-library
rg likewise found no replacement. Read the Stacks Tag 00M1 proof at the local
read-only copy `/home/ubuntu/c1-stacks-review/algebra.tex`, lines 18397–18522.

## Second reading by C1

1. **Statements unchanged.** Compared the delivered module with the repository version: the
`HomologicalComplex₂.doubleComplexCokernelHomologyIso` signature is byte-for-byte unchanged.
The DAG node statement and the unit statement are unchanged; no target or definition was
altered.

2. **Proof and axioms.** Compiled the sandbox with `lcompile.py --all`; it succeeds with no
warnings. The module has no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or
`extern`. The proof uses only the existing open helper theorems and private proved helpers;
The explicit scratch-copy axiom check for the target, boundary swap, transpose iso, and
endpoint bijectivity shows only `propext`, `Classical.choice`, `Quot.sound`, and (except
for the boundary swap) `sorryAx` from the existing imported theorems. No local hole is
introduced. The chosen endpoint map is uniquely determined on quotient representatives
by its formula: cycle inclusions are injective and the quotient projection is onto.
The transpose is constructed explicitly from coordinate swap before its proved existence
theorem is used; no definition selects an arbitrary witness of an open existence theorem.

3. **Split statements and truth.** No statement was split off and no new node was added.
The private coordinate-swap, cycle, boundary, quotient, naturality, and bijectivity lemmas
are internal proof lemmas, so they do not create public holes. The row endpoint map uses
`exists_zigzagToRowCokernel` exactly through its stated surjectivity, cycle formula, and
representative formula; the injectivity argument uses `homologyIsCokernel` and the stated
row-boundary lemma. Degree zero is covered by the same definitions and was checked in the
proof's natural-number branches.

4. **Pruning and route.** The proof removes the two direct imports
`Sheaf.Algebra.Homology.ZigzagModule` and `Sheaf.Algebra.Homology.ZigzagModuleFunctorial`
but keeps `lem-weil-pbc-double-complex-zigzag-module-functorial` in this node's
`proof_deps`: the definition of `zigzagMap` uses its preservation clause. The remaining
imports and dependencies are used. Independent searches with flip/homology/cokernel
keywords in Mathlib and the library found no shorter replacement; the Stacks 00M1
proof was read at `/home/ubuntu/c1-stacks-review/algebra.tex`, lines 18397–18522. The unit route and its
realized steps are preserved; the coordinate transpose is a below-unit implementation
lemma.

5. **Nodes and repairs.** The node's proof, dependency union, and source route match the
Lean proof. Restored the functoriality node dependency for the preservation theorem used
by `zigzagMap`, and corrected the pruning report accordingly. Only the large conjunction
theorem and the direct import are unused; that entire node is not pruned. No Lean proof,
statement, definition, unit record, or import needed repair. No new nodes or changes
records are required.
