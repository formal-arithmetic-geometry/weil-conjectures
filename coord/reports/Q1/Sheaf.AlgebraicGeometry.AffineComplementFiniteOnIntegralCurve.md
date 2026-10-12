## What changed

Proved `AlgebraicGeometry.IsAffineOpen.finite_compl_of_integral_dim_one` by the existing,
sorry-free `IsOpen.finite_compl_of_topologicalKrullDim_le_one` in
`WeilConjectures.Mathlib.Topology.KrullDimension`. Construct the local `IsNoetherian X`
instance from the two existing hypotheses, then apply the topological theorem to
`U.isOpen`, `hdim.le`, and `hne`. All signatures and public imports are unchanged.
The existing docstring retains the mathematical argument implemented by that theorem.
Single-file compilation passed without warnings. Empty complement (`U = X`) is included;
nonemptiness rules out the empty open. No separatedness or affineness is needed by the proof.

## Proved and sorry left

Closed one of one holes: `AlgebraicGeometry.IsAffineOpen.finite_compl_of_integral_dim_one`
(node `lem-sc-affine-complement-finite-on-integral-curve`). No holes remain in the item;
no holes were added. This is a proof, not a decomposition. The imported topological
finiteness theorem and its point-closedness theorem have complete Lean proofs.

## No longer needed

Removed the proof import `Sheaf.AlgebraicGeometry.FiniteOfIsClosedOfClosedPoints` and
its node `lem-sc-noetherian-closed-points-finite` from this item's proof dependencies.
Its further finite-component argument is already implemented in the source theorem.
The point-outside-open node `lem-sc-dim-one-point-outside-open-closed` is no longer a
direct dependency; it is retained under the source-theorem node because that proof uses it.
Scheme sobriety remains needed through Mathlib instances. No unit statement or unit
proof step is bypassed (`sk-thm-curveestimate.realized.steps` is empty). The removed
module may remain needed by other items; no whole-closure pruning claim is made.

## Where the brief, the DAG or earlier work was wrong

The planned proof was valid, but unnecessarily depended on a sorry-bearing scheme
closed-points finiteness lemma: a stronger, fully proved source-library theorem already
combines the point argument and finite-component argument. No mathematical statement
was wrong or changed.

Retry validation: single-file compilation again passed without warnings (exit code 0).
The prescribed `deliver3.py Q1
Sheaf.AlgebraicGeometry.AffineComplementFiniteOnIntegralCurve --no-push` passed
local compilation and axiom probing, then failed at branch preparation because
`.git/index.lock` already exists. No process held the lock when checked.
Automatic approval review rejected the attempted lock-removal command because
`rm -f` style commands are not permitted. The brief limits direct writes to this
sandbox, so no alternative removal was attempted. The lock remains unchanged;
the dry run has not printed OK. Proof and node files are preserved for retry.

## New nodes

`lem-sc-nonempty-open-complement-finite-dim-le-one` records the existing source theorem
`IsOpen.finite_compl_of_topologicalKrullDim_le_one`, its hypotheses, and complete
finite-union-of-singletons proof. It adds neither a module nor a declaration nor a hole.
No change records are required because the public interface is unchanged.

## Second reading by Q1

1. **Statements and accidental changes.** I diffed the delivered module against the repository version. The theorem signature and docstring statement are byte-for-byte unchanged; only the proof and its proof-only import changed. The existing item node records the same statement, and the added source-theorem node records the exact declaration it uses.

2. **Proof and axioms.** The delivered file compiles with `lcompile.py` without warnings. The proof constructs `IsNoetherian X` from the existing local-noetherian and compact-space instances and applies the fully proved `IsOpen.finite_compl_of_topologicalKrullDim_le_one`. It contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`; no definition contains a proof hole. The unused affine-open hypothesis is intentionally retained to match the target signature.

3. **Split statements and truth.** No new theorem or proof hole is added. The auxiliary DAG node names the existing general topological theorem, with its exact Lean statement and source proof; it is strictly more general than the target and is not a restatement of the item. Small cases (the whole open, a one-point complement, and a generic-point open in a DVR) are consistent with the conclusion.

4. **Shortest route and pruning.** The proof uses the existing source-library theorem directly, so the earlier closed-points finiteness import and its node are no longer needed by this module. The unit route remains represented by the item node; no unit statement or step is bypassed. Public imports are unchanged except for removing the proof-only closed-points module.

5. **DAG agreement.** The item node's `proof`, `proof_deps`, and `proof_origin` match the Lean proof. The auxiliary node's `lean` record points to `WeilConjectures.Mathlib.Topology.KrullDimension.IsOpen.finite_compl_of_topologicalKrullDim_le_one`, and its proof dependencies match that theorem's documented route.

Changed during second reading: added this audit section only; no Lean statements or definitions were changed.
