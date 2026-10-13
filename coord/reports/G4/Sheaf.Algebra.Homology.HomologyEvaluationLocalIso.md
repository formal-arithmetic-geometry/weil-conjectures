## What changed

Copied the missing HomologyEvaluationDefinitions dependency into the sandbox so the local compiler can build it. Added HomologyEvaluationLocalIsoCore, which states the finite-free roof calculation as an intermediate theorem, and proved the assigned theorem by unpacking HasFiniteFreeZeroModel and applying that core theorem.

## Proved and sorry left

The target theorem `CategoryTheory.homologyEvaluation_local_iso_of_cycle` is proved by a real Lean reduction. The intermediate theorem `CategoryTheory.homologyEvaluation_local_iso_of_roof` remains `sorry`; it is the finite-free roof calculation and is strictly smaller than the target.

## No longer needed

The target proof does not use the prior direct proof-plan imports beyond the definitions and core interface. No DAG nodes were pruned.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt reported a missing published `HomologyEvaluationDefinitions.olean`; compiling that dependency in the sandbox resolves the tool failure. The substantive finite-free roof calculation remains split into a named intermediate theorem.

## New nodes

Added `new-b2-homology-evaluation-local-iso-core` for the finite-free roof calculation, sourced from Stacks Tag 0BQY. Its Lean declaration is `CategoryTheory.homologyEvaluation_local_iso_of_roof` in `Sheaf.Algebra.Homology.HomologyEvaluationLocalIsoCore`.

## Earlier second reading (a previous round; superseded)

The target proof was independently checked by compiling the full sandbox with the copied definitions dependency. The new core theorem is a strictly smaller roof-specialized statement; its remaining `sorry` is the finite-free calculation delegated to the next worker.

## Second reading by G4

1. **Visible changes and statements.** Compared the delivered target module against the repository version. The existing target signature is byte-for-byte unchanged; the only interface addition is the explicitly split core theorem. Verdict: pass.
2. **Proof validity.** Compiled all sandbox modules with `lcompile.py --all`; the target theorem has a real proof reducing to the named core theorem, and the only remaining `sorry` is the documented core theorem. No forbidden declarations or hollow definitions were added. Verdict: pass.
3. **Split statement.** Checked `CategoryTheory.homologyEvaluation_local_iso_of_roof`: it fixes the finite-free roof data explicitly, so it is strictly more specialized than the target and is mathematically the finite-free subcalculation described in its docstring. Its DAG node now depends only on definitions and foundational quasi-isomorphism/K-injective nodes, with no circular dependency on the target. Verdict: pass.
4. **Pruning and imports.** The target uses the core theorem through a proof-only import; the public definition import remains required by the signature. No unused public imports were introduced, and the unit route still passes through the local evaluation node and its finite-free roof step. Verdict: pass.
5. **DAG agreement.** Updated the core node's `stmt_deps`, `proof_deps`, and proof route to match the Lean proof and removed the prior circular target dependency. The target node's proof dependency remains the core theorem. Verdict: pass.

Changed the core node metadata to remove the circular dependency and appended this second-reading record. No Lean declarations required repair.
