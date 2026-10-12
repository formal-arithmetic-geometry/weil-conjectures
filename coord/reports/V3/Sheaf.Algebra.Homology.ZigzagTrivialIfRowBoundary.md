## What changed
The proof of `HomologicalComplex₂.zigzag_trivial_if_row_boundary` combines two
strictly smaller intermediate statements: initial boundary reduction and the exact-row
induction for a zero-component cycle. Its existing signature is unchanged. Added modules
`Sheaf.Algebra.Homology.ZigzagBoundaryReduction` and
`Sheaf.Algebra.Homology.ZigzagZeroComponentBoundary`; their named theorem holes have complete
source-backed natural-language proofs. Both helpers are plain proof imports of the target.

Second reading removed the unused direct proof import of `ZigzagModuleFunctorial` from the
target, placing it in the helper modules whose proof plans use its boundary-cycle clause.
Removed redundant public imports `Mathlib.Algebra.Homology.HomologicalComplexAbelian`,
`Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex`, and
`Mathlib.Algebra.Category.ModuleCat.Abelian` from the new zero-component module; its signature
needs only `ZigzagModule` and `ShortComplex.Exact`. Existing public target imports are retained.
Updated the existing target DAG proof to the actual two-helper combination, completed the
new nodes' statements and dependencies, and replaced unsupported search records with real
searches logged during second reading.

## Proved and sorry left
Hole closed in the item: `HomologicalComplex₂.zigzag_trivial_if_row_boundary`
(node `lem-weil-pbc-double-complex-zigzag-trivial-if-row-boundary`). Its proof body is complete,
but it depends on the following two open intermediate theorems.

Holes added and left:
- `HomologicalComplex₂.zigzag_boundary_reduction`
  (node `new-zigzag-boundary-reduction`).
- `HomologicalComplex₂.zigzag_zero_component_boundary`
  (node `new-zigzag-zero-component-boundary`).

This delivery is a decomposition, not a completed proof of the target from standard axioms:
one upper hole is closed and two lower holes added. Arithmetic for these delivered
declarations alone is net -1; target-closure and whole-library figures are for the pinned
sorry ledger to compute. No hole is added inside a definition. No existing statement is changed.

## No longer needed
The target no longer directly imports `Sheaf.Algebra.Homology.ZigzagModuleFunctorial`, but
both split-off proof plans still need its first clause and import it. It is not pruned from
the delivery's import closure.

Old target `proof_deps` no longer used directly by its proof are
`def-weil-pbc-exact-sequence`, `def-weil-pbc-module-chain-complex-homology`, and
`lem-weil-pbc-double-complex-zigzag-module-functorial`. They remain required through the
helper signatures or proof plans. `def-weil-pbc-double-complex-zigzag-module` remains a direct
proof dependency for the boundary linearity calculation. The two helper nodes are the other
direct proof dependencies. No old dependency module becomes globally unreachable on this
basis; modules pruned: none. Redundant imports removed from the new helper are listed above.

## Where the brief, the DAG or earlier work was wrong
The earlier report called the item proved without distinguishing decomposition from a proof
independent of new holes. The helper docstrings were only summaries, their node statements
were not self-contained, the original target node still described its old proof plan, and
the search records had no matching local search log. These were repaired in second reading.
The mathematical two-step reduction is valid and was retained. The initial boundary-reduction
lemma carries the common row-exactness hypothesis although that step does not need it.

The source read was Stacks Algebra Tag 00M1 (`lemma-no-spectral-sequence`), especially the
injectivity paragraph at lines 18483--18504. Its displayed cokernel indices in that paragraph
are transposed relative to `a_(0,i)`; the following `delta ⊕ d` formula and the target's
`A.opcycles 0` correctly use the cokernel of `A_(1,q) → A_(0,q)`. No target correction is needed.

## New nodes
`new-zigzag-boundary-reduction` states only the initial cokernel-boundary lift and subtraction,
not triviality of the entire cycle. Its proof lifts `y` to `c`, lifts the resulting kernel
element to `e`, and uses the two-component tuple together with the first functoriality clause.

`new-zigzag-zero-component-boundary` states the residual exact-row induction, with the
stronger zero-component premise instead of the target's cokernel-boundary premise. Its proof
has a base case, a finite invariant, and an exact-row step with an accumulated preimage.
Both nodes are in `dag/nodes/sec-proper-base-change/`, with matching new Lean modules.
No change record is necessary: existing signatures and definitions are unchanged.

## Second reading by V3
1. Compared the target source against the repository baseline with `diff`; the declaration
signature, docstring, universes, `CommRing` instance, exact-row hypothesis, cycle hypothesis,
cokernel-boundary hypothesis and conclusion are byte-for-byte unchanged. Only the proof and
plain helper imports change; the unused plain functoriality import is removed. No other
existing module is adapted and no target definition is changed.
2. All three delivered files compile through `lcompile.py`. Explicit `#print axioms` probes
on scratch copies show only `propext`, `Classical.choice`, `Quot.sound`, and the expected
`sorryAx` from the two open helpers. The only delivered proof holes are those two named
theorems. There is no `axiom`, `unsafe`, `opaque`, `extern`, `implemented_by`, or definition
with missing data. The target combines witnesses `b` and `c` by `map_add`, `hc`, and `abel`,
so the algebraic conclusion really is `D(b+c)=a`.
3. Checked each helper against Tag 00M1 and the actual zig-zag definitions. For boundary
reduction, surjectivity of the cokernel projection lifts `y`; its kernel-image property gives
`e`; the tuple supported at `(0,n+1)` and `(1,n)` kills the first component. For the residual
lemma, row exactness is used only at `k>0`; the cycle relation gives a horizontal kernel
element, and the boundary supported at `(k+1,n-k)` kills it without restoring earlier
components. At `n=0`, the residual lemma is direct-sum extensionality for the sole zero
component, and reduction still has both supporting indices in total degree one. At `n=1`,
the last lift lies at `(2,0)` and has no vertical term, so it terminates. No column exactness
or division by two is assumed. These are two proper parts of the source argument, neither
a restatement of the target. Docstrings now give the complete proofs and matching nodes.
Searched Mathlib through `msearch.py` using LeanFinder (zero-first-component bicomplex cycle),
Loogle (`HomologicalComplex₂`), and grep (`opcycles.*(surjective|exact)|zigzag|total.*exact`).
The hits give single-complex identities or bicomplex definitions, not either helper.
LeanSearch was attempted and returned Internal Server Error, recorded as unavailable.
Also searched `lean/Sheaf/Algebra/Homology`, `lean/WeilConjectures/Algebra`, and the upstream
`WeilConjectures/Algebra` for zig-zag and exact-row terms; no duplicate helper was found.
4. The two stages reproduce the source's initial reduction followed by exact-row induction.
The node is below the unit level and is not an entry in `sk-thm-p1.json`'s `realized` fields;
that unit route is unchanged. Import-pruning probes showed the zero-component statement
compiles with only its two public imports, while removing the homological-complex opcycles
import from the reduction fails. The original direct functoriality import is moved to the
helpers. Every old target proof dependency removed from the direct list is accounted for
above, with no claim that a transitively required module is pruned.
5. Read the existing and both new node records. The existing node now names the two helper
applications and the elementary linearity combination. New nodes now have self-contained
statements, full verbatim Lean signatures, source places, actual search results, the item's
chapter and unit, and the existing blueprint ancestor and route. Their proof-dependency
lists equal the unions of their steps, including the boundary-cycle functoriality clause
and the cokernel-complex definition where used. No node statement used by other modules
was changed.

Changes made in this reading: expanded the helper and module docstrings; repaired node
statements, proof plans, dependency lists, blueprint provenance and search records;
removed redundant imports and moved the functoriality proof import; corrected the progress
accounting and wrote this review. The correct target proof body was retained.
