## What changed

Replaced the hole in `AlgebraicGeometry.principalOpenCech_column_step` with a
coordinate proof from the new horizontal-row primitive theorem. The proof derives
horizontal closedness from the total differential, lifts the primitive through the
inverse coordinate isomorphism, and checks cancellation and support directly.
The row theorem is indexed by the degree m of the primitive; writing the total
degree as m+1 makes every deletion transport agree without a dependent rewrite.
Added the proof-only import `Sheaf.AlgebraicGeometry.PrincipalOpenCechSubsetRowPrimitive`.
The original theorem's signature and public imports are unchanged.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.principalOpenCech_column_step`.
Added one hole: `AlgebraicGeometry.principalOpenCech_subset_row_primitive`, node
`lem-sc-principal-open-cech-subset-row-primitive`. This is a decomposition, not a
complete proof of row acyclicity: one hole closed and one strictly narrower hole
added. The new theorem has no total complex, no differential compatibility
assumption, and no total boundary conclusion. The original module has no holes left.

The remaining row statement was checked at k=1, k=r, k+1>r, r=0, and with empty
or repeated basic opens. At the last degree its cocycle condition is vacuous,
but positive-degree exactness still gives the primitive; beyond the last degree
the zero primitive suffices.

## No longer needed

The proof-only row import is required. No existing imports or library modules are pruned. The old direct proof dependencies
`lem-weil-pbc-module-injective-open-cover-cech-acyclic` and
`lem-pc-alternating-cech-computes` are replaced at the column-step node by
`lem-sc-principal-open-cech-subset-row-primitive`; both remain required as
proof dependencies of the new row node, whose module imports them privately. The abandoned sandbox-only
`PrincipalOpenCechColumnStepCore` module is excluded: its theorem merely repackaged
the original conclusion and was not a valid reduction. It was never a library node.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt's core theorem was essentially the original theorem in two
cardinality cases and could not serve as a strict intermediate statement. Its
final simplification also attempted to obtain a coordinate vanishing from an
unrelated subtraction identity. This attempt instead isolates only horizontal
exactness and proves the total-complex calculation explicitly.

The preserved attempt failed when simplifying n-1+1 inside a dependent row sum.
This repair introduces m with n=m+1 before choosing the primitive and indexes the
row theorem directly by m. It uses the original he transports without composition.
Both delivered modules compile cleanly through lcompile.py.

The existing acyclicity and alternating-comparison signatures require substantial
coordinate conversion: increasing tuples to subsets, intersections to product
basic opens, and arithmetic coefficient transports. That conversion remains in
the row theorem, with its full argument documented. LeanSearch returned an
internal server error; LeanFinder and source searches found no direct subset-row
primitive theorem. The local literature checkout lacks cohomology.tex; the cited
Tags [01EP](https://stacks.math.columbia.edu/tag/01EP),
[01FM](https://stacks.math.columbia.edu/tag/01FM) and
[08C1](https://stacks.math.columbia.edu/tag/08C1) were read from the Stacks website.

## New nodes

`lem-sc-principal-open-cech-subset-row-primitive` states positive-degree horizontal
exactness in subset coordinates, with extension by zero outside cardinality k.
It follows the original dependencies (injective module Čech acyclicity and the
alternating comparison), with the coordinate identification made explicit. Its
module is `Sheaf.AlgebraicGeometry.PrincipalOpenCechSubsetRowPrimitive`.
No interface change or forced adaptation is included.

## Second reading by P2

1. **Interfaces: pass.** Diffed the only existing delivered module against the
   repository. The full `principalOpenCech_column_step` signature is byte-identical;
   its public imports and definitions are unchanged. Only the proof and one private
   proof import differ. The existing node changes only `proof`, `proof_deps`, and
   `proof_origin`. There is no interface change or forced adaptation.
2. **Proof: pass.** Both delivered modules compile through `lcompile.py --all`.
   Read the cancellation calculation: support kills the vertical contribution at
   size k+2; the row lemma gives b at size k; the inverse coordinate isomorphism
   lifts it to u; at size k+1 the horizontal sum equals t; at larger sizes each
   erased subset still has size greater than k, so every summand vanishes.
   The original theorem has no sorry; the new row theorem is the sole named hole.
   No forbidden axiom, unsafe code, opaque declaration, or hollow definition occurs.
   Scratch `#print axioms` checks for both declarations return exactly `propext`,
   `Classical.choice`, `Quot.sound`, and `sorryAx` (the open row theorem).
3. **Split statement: pass.** Read the entire new signature and its matching node,
   and independently checked Stacks Tags [01EP](https://stacks.math.columbia.edu/tag/01EP),
   [01FM](https://stacks.math.columbia.edu/tag/01FM), and
   [08C1](https://stacks.math.columbia.edu/tag/08C1).
   The coefficient at size k+1 is J^(n+1-k), also the coefficient of b at size k.
   The cocycle equation at size k+2 uses precisely that coefficient after deletion.
   For k=1 this is ordinary degree-one exactness, including r=2 where there is no
   cocycle condition but flasqueness makes the last restriction difference onto.
   For k=r-1 it is the last nonzero row; for k>=r or r=0 there are no size-k+1
   coordinates and b=0 works. Empty or repeated opens do not alter the indexed
   exactness argument, and no assumption of distinct opens or a cover of Spec(A)
   is added. It isolates horizontal exactness only, not the original total-boundary
   assertion. LeanFinder, Loogle, and source searches with new queries found tuple
   exactness, enumeration, and total subset insertion, but no duplicate row lemma.
   The conversion is substantial and cannot be closed in a few minutes.
4. **Route and pruning: pass, with a pre-existing recording gap.** The proof follows
   the finite-row argument and retains both original mathematical dependencies
   underneath the new row node. No library module or import is pruned. The report
   now lists both old dependencies replaced in the column node's direct
   `proof_deps`. `dag/units/sk-thm-picard-duality.json` currently has empty statement
   and step realization arrays; this pre-existing gap is not changed or bypassed
   by this local reduction, which remains beneath the same unit and ancestor.
5. **Nodes: pass after repairs.** The existing node describes the actual reduction
   and has exactly the new row dependency. The new node's Lean signature matches
   verbatim, its proof-step dependency union is correct, its source and complete
   natural-language proof agree with the Lean, and its chapter, unit, creation,
   origin, searches, and blueprint ancestry are recorded.

Changed in the second reading: added the two proof-only imports required by the
row node's plan; expanded its docstring and node proof to explain the open-subscheme
comparison and the integer/A sign agreement; added independent search records and
`blueprint.same_as`; corrected the last nonzero row from k=r to k=r-1 in the node; corrected the direct-dependency accounting in `No longer needed`.
No mathematical statement or existing proof was changed. One original hole closed,
one strictly smaller hole added: decomposition, net zero among these declarations.
