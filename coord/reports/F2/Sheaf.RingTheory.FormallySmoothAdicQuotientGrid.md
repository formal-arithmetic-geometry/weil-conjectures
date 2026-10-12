## What changed

Proved `Algebra.FormallySmoothAdic.exists_quotient_grid` with its original signature.
Added the proof-only import `Sheaf.RingTheory.FormallySmoothAdicDiagonalStep`.
The grid is constructed by projecting a compatible diagonal tower at index
`max a b`. Private proved helpers establish the first-row annihilation exponent
and dependent recursion; private definitions contain only explicit ideals and
a subtype of algebra maps with their required properties.

Added and fully proved `Algebra.FormallySmoothAdic.exists_diagonal_successor`.
Its private helper `lift_surjective` proves independent-universe lifting: choose
representatives, take the generated subalgebra, use `Algebra.small_adjoin`,
transport to `Shrink`, and factor through the quotient by the restricted kernel.
Its private helper `lift_compatible_quotients` constructs the fibre product as an
explicit equalizer subalgebra, proves the quotient-pair map surjective and its
kernel square zero, lifts through it, and proves continuity of the lift.
The diagonal specialization uses ideal modularity and multiplication inequalities.
No target, existing statement, or public definition changed. Docstrings and DAG
proof routes now describe the implemented diagonal argument.

## Proved and sorry left

Closed: `Algebra.FormallySmoothAdic.exists_quotient_grid`
(node `lem-weil-pbc-fs-adic-compatible-quotient-grid`): the item's one original hole.
Added and fully proved: `Algebra.FormallySmoothAdic.exists_diagonal_successor`
(node `lem-weil-pbc-fs-adic-diagonal-step`).
No holes added or left in either delivered module; no decomposition remains.
The first-row power calculation, tower recursion, every transition equation,
both zero-index cases, the square-zero lifting problem, and universe reduction
are proved. Choices of representatives use the proved surjectivity of the map;
no definition selects arbitrary data from an unproved existence statement.

## No longer needed

No existing dependency module, node, or import is removed: the original module
imports only the formal-smoothness definition and quotient algebra API, both used.
The old construction of the bottom row and individual off-diagonal fibre-product
lifts is replaced by successive diagonal lifts. The separate zero-index extension
is unnecessary: projection from the diagonal handles zero indices too.
No unit statement or realized step is bypassed. All imports of the new module
are used: ideal operations and formal smoothness in its public statement, and
small generated subalgebras, algebra transfer, product homomorphisms, and one
linear-combination calculation in its proof.

## Where the brief, the DAG or earlier work was wrong

The local literature tree lacks `literature/stacks-project/more-algebra.tex`.
Read the cited source directly at https://stacks.math.columbia.edu/tag/07NJ.
The existing node's `created.item` is a Lean module name rather than a DAG id,
so `tools/blueprint_refs.py ancestor` returns None; the new node records this
broken provenance chain and cites the exact parent proof steps and source.
LeanSearch returned HTTP 500; recorded as unavailable, not as a negative match.
The local finite lifting statement was checked for k=1, I=0, J=0, unit ideals,
and the zero ring. The kernel-square calculation works in each case, and no
completeness, closedness, or comparison of ideal powers is needed.
An initial broad simplification caused kernel timeouts; explicit quotient-factor
rewrites remove the expensive dependent transports. No heartbeat or time limit
was raised; both final modules compile within the ordinary single-file limit.

## New nodes

`lem-weil-pbc-fs-adic-diagonal-step` in
`lean/Sheaf/RingTheory/FormallySmoothAdicDiagonalStep.lean` is fully proved.
It states one finite lifting problem for two compatible continuous quotient maps.
It requires no infinite grid and supplies only the next diagonal map. The main
theorem proves the recursion and global compatibility glue. Mathlib searches and
the whole-blueprint square-zero search found no matching existing theorem.
The node and docstring record the source and full proof. No change record needed.

Validation: the delivered pair compiles together in import order (3.5 s and
5.3 s), with no warnings. `#print axioms` for both public theorems reports only
`propext`, `Classical.choice`, and `Quot.sound`. The stage-3 delivery dry run is
the final check; no delivery is pushed by this worker.

## Second reading by F2

1. Compared both delivered Lean modules with the repository versions. The existing public theorem signature is byte-for-byte unchanged; the added diagonal module is a new split-off declaration and the report/node record the addition. Verdict: pass.
2. Compiled both modules together with `lcompile.py --all`; compilation succeeds with no warnings. The delivered declarations contain no `sorry`, forbidden commands, or hollow definitions. Verdict: pass; the public theorem axioms are limited to the permitted classical axioms (as recorded above).
3. Checked the diagonal successor statement against the finite quotient lifting argument and edge cases (k=1, zero ideals, unit ideals, and the zero ring). It is a strict intermediate lifting statement, has source/proof docstrings and a matching DAG node, and is not duplicated in the library. Verdict: pass.
4. Read the proof top-down. The quotient factor API and the new diagonal successor are used; the cofinal diagonal tower is a shorter route below the unit level and retains the unit's realized statement. No unused dependency import was found. Verdict: pass.
5. Compared the node proof, proof dependencies, and proof origin with the implemented route. The new node is marked split with complete provenance and Lean metadata; the parent node records the revised diagonal route. Verdict: pass.

Changed during second reading: no proof or statement changes were necessary; this section is the only edit.
