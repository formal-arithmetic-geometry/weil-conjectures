## What changed

Filled `isN1_of_isAnalyticallyUnramified` with a complete proof. The proof constructs the
adic completion, obtains its Nagata property, proves finiteness of its normalization by
mapping into the product of residue fields at minimal primes, embeds the base-changed
normalization using flatness and localization, and descends module finiteness by faithful
flatness. Added only proof-only Mathlib imports required by these constructions.

## Proved and sorry left

The theorem `isN1_of_isAnalyticallyUnramified` is proved with no `sorry` remaining. No new
public theorem or node was added. Holes closed: 1, by
`isN1_of_isAnalyticallyUnramified` (node `lem-weil-pbc-analytically-unramified-n1`).
Holes added: 0. Both private helper theorems are completely proved. The imported
`isNagataRing_of_complete_local` and the product decomposition dependency retain their
existing proof obligations; this is a proof from the stated dependencies.

Validation: `lcompile.py` compiles the module without errors or warnings.

## No longer needed

The direct import `Sheaf.RingTheory.NagataRing` was removed because it is already supplied by
`Sheaf.RingTheory.NagataOfCompleteLocal`. No DAG node is pruned: the completion-locality and completion-completeness nodes are
Mathlib leaves whose instances are still needed. Their content is used through typeclass
inference. No proof-dependency module other than the redundant direct import is removed.

## Where the brief, the DAG or earlier work was wrong

The DAG proof plan was mathematically sound but substantially longer than necessary in Lean:
Mathlib's `Module.Finite.of_finite_tensorProduct_of_faithfullyFlat` directly performs the final
descent, while `Module.Flat.lTensor_preserves_injective_linearMap` and localization APIs make
the tensor embedding concise. No statement was changed. The retained extra universe and namespace-opening command
were removed; tensor products are fully qualified, preserving the original public commands.
The node proof now records the actual Lean APIs and its proof dependencies are the union
of the steps' dependencies, including the local-completion-local-ring leaf.

The earlier import-source tool failure is fixed. After removing the unnecessary public
commands, `deliver3.py --no-push` printed OK: the module compiles and passes preflight
except for the independent second reading, which the dry-run tool correctly reserves for
the second reader. Nothing was pushed.

## Second reading by H2

1. **Declarations unchanged.** I compared the delivered module with the repository version;
the public theorem signature and all existing declarations are byte-for-byte unchanged.
Verdict: pass.
2. **Proof validity.** The module compiles cleanly with `lcompile.py`; it contains no
`sorry`, forbidden declarations, or hollow definitions. The two private helpers are fully
proved, and the target proof uses only the permitted imported obligations. Verdict: pass.
3. **Statements and dependencies.** No public statement or new node was added. The target
node remains exactly the stated analytically-unramified-to-N-1 claim; its proof metadata now
mentions the concrete Mathlib APIs used by the helpers. Verdict: pass.
4. **Pruning and route.** The redundant public `Sheaf.RingTheory.NagataRing` import was
removed; all remaining imports are used by declarations or proofs. The unit route through
completion, normalization, and faithful-flat descent is preserved. Verdict: pass.
5. **DAG agreement.** The node's proof text, origin, and dependencies agree with the Lean
proof, and no split-off holes were introduced. Verdict: pass.

I changed only the proof imports, proof body, corresponding node proof metadata, and this
second-reading report section.
