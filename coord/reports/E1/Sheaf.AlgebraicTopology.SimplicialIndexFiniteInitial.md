## What changed

Proved `SSet.simplicialIndex_finite_initial` in
`lean/Sheaf/AlgebraicTopology/SimplicialIndexFiniteInitial.lean`, with its signature,
visibility, existing docstring, and imports unchanged. Five proved private helpers
implement the existing DAG plan:

- `simultaneous_repeat`: if neither map repeats simultaneously, the sum of their
  values increases at every adjacent pair, contradicting the two dimension bounds.
- `common_factor`: induction on the source degree, using Mathlib's
  `SimplexCategory.eq_σ_comp_of_not_injective'` and the face-degeneracy identity.
- `bounded_ancestor`: Mathlib's `SSet.exists_nonDegenerate` and the given degree bound.
- `common_ancestor`: packages the factorization as morphisms of `S.Elements`.
- `four_step`: constructs the four arrows connecting arbitrary truncated endpoints.

The main proof supplies finite objects and hom sets, reachability, the explicit
sequence with `r = 2` and constant tail, connected costructured-arrow categories,
and Mathlib's initial-functor limit existence and comparison results. This follows
all six steps of the recorded plan, so no DAG route changes or new nodes are needed.
The original nonemptiness hypothesis is retained, as are all other binders.

Searches used the prescribed msearch LeanFinder, Loogle, and grep interfaces,
plus local searches of Mathlib, `lean/WeilConjectures`, and `lean/Sheaf`.
LeanFinder returned finiteness results, but no initial-truncation theorem; Loogle
found `SSet.exists_nonDegenerate`. All required underlying lemmas are in Mathlib.

## Proved and sorry left

Closed the only original hole: `SSet.simplicialIndex_finite_initial`
(node `lem-weil-pbc-simplicial-index-finite-initial`). All seven conjuncts are proved.
Added no holes and split off no statements. No `sorry` remains in the delivered
module, including its five private helpers.

## No longer needed

None. No imports, nodes, or modules were removed. All four original public imports
are needed by the statement, and all mathematical steps of the DAG plan are used.
No additional Sheaf proof dependencies were imported: the plan's supporting nodes
are already Mathlib leaves.

## Where the brief, the DAG or earlier work was wrong

No statement or route errors found. The combinatorial argument is formalized by
counting growth of the sum of the maps, which proves the planned simultaneous
repeat without constructing finite sets of ascent indices. The case `m₀ = 0`,
source degree zero, and endpoints of degree exactly `2 * m₀` are covered by the
same proofs. No definitions, statements, or other modules were changed.

## Second reading by E1

1. **Signatures and accidental changes.** Compared the delivered module with the
repository version. The theorem statement, all existing declarations, visibility,
docstrings, and public imports are byte-for-byte unchanged; only the target proof
and private proof helpers were added. Verdict: pass.
2. **Proof and axioms.** Compiled the module with `lcompile.py`; it has no `sorry`,
axiom, unsafe, opaque, extern, or implemented-by declarations. A scratch
`#print axioms SSet.simplicialIndex_finite_initial` reports only
`propext`, `Classical.choice`, and `Quot.sound`. Verdict: pass.
3. **Statements split off.** No statements were split off and no new nodes were
added. The proof uses existing Mathlib declarations for simplex factorization,
degeneracy injectivity, zigzags, and initial-functor limit comparison. Verdict:
pass.
4. **Shortest route and pruning.** Checked the proof from the target downward:
finite objects and homs, bounded ancestors, the common-factor descent, the
four-step zigzag, initiality, and the two limit clauses. All four original public
imports remain used and no unnecessary proof import was introduced. The unit's
six-step route is preserved. Verdict: pass.
5. **DAG agreement.** The existing node's `proof`, `proof_deps`, and
`proof_origin` remain accurate for the declarations used by the proof; no node
fields require changes. Verdict: pass.

Changed in this second reading: appended this review section only; no Lean,
definition, statement, import, or DAG changes were needed.
