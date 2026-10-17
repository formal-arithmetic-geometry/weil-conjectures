## What changed

Repaired the returned duplicate-lemma delivery. Removed the private duplicate
`Ideal.dimAt_openEmbedding` and replaced both dimension transports with
`Algebra.dimAt_openEmbedding`, imported directly with the proof-only
`import all WeilConjectures.RingTheory.SmoothAtPrimeDifferentialsDimension`.
Importing the former Sheaf wrapper does not expose this upstream private helper.
The remaining retained proof, including the concrete presentation and stable-free
rank calculation, is preserved. The public theorem signature is unchanged.
Updated the existing node's proof metadata to record the direct upstream import.
No definitions, statements, or other modules were changed.

## Proved and sorry left

`Ideal.exists_basis_cotangent_localization_of_completeIntersection` closes the
current source's one hole. The two private helpers
`Ideal.basis_of_stably_free` and `Ideal.principal_ci_presentation_dimension`
are proved. Zero holes remain, zero holes were added, and zero were split off.
The module compiles without errors or warnings using `lcompile.py`.

## No longer needed

Removed the duplicate private lemma `Ideal.dimAt_openEmbedding`.
Replaced the obsolete proof-only
`import all Sheaf.RingTheory.SmoothAtPrimeDifferentialsDimension` with its
upstream defining module. Pruned the unused import
`Mathlib.LinearAlgebra.Dimension.Constructions` from the current source.
No DAG dependency is pruned: the smooth-dimension node remains recorded because
its upstream module supplies the private open-embedding dimension theorem.
No other nodes or modules become unnecessary through this repair.

## Where the brief, the DAG or earlier work was wrong

The previous repair correctly observed that the Sheaf wrapper did not expose
`Algebra.dimAt_openEmbedding`, but duplicated its proof locally. The landing
checker rejected that duplication. Importing the defining upstream module
with `import all` exposes the original helper and resolves the return directly.
The prime above `q` still excludes the zero-ring presentation branch; zero
variables and zero equations remain allowed. The unit route is preserved.

## Second reading by J2

1. **Signatures and statements.** Compared the sandbox module with the repository
   version. The existing public theorem signature is byte-for-byte unchanged; the
   added declarations are private proof helpers, and no target or definition was
   altered. Verdict: pass.
2. **Proof and axioms.** Compiled the module with `lcompile.py` and checked the
   target's axioms in a scratch copy. There are no errors, warnings, `sorry`s,
   forbidden declarations, or extra axioms beyond `propext`, `Classical.choice`,
   and `Quot.sound`. Verdict: pass.
3. **Split statements and reuse.** No split-off statements were added. The private
   dimension transport reuses the existing upstream `Algebra.dimAt_openEmbedding`,
   and the remaining helpers are local reductions required by the proof. Verdict:
   pass; no duplicate public lemma was retained.
4. **Pruning and route.** Checked the proof dependencies and imports. The Sheaf
   wrapper import and `Mathlib.LinearAlgebra.Dimension.Constructions` are removed;
   the upstream proof-only import supplies the dimension theorem. The stable
   conormal and global-complete-intersection route, including the unit's realized
   steps, is preserved. Verdict: pass.
5. **DAG agreement.** The node's proof, proof dependencies, and proof origin record
   the direct upstream dimension transport and match the Lean proof. Verdict: pass.

I changed the module to import the defining upstream dimension module, removed the
old duplicate private dimension lemma and the unused dimension-constructions import,
updated the node proof metadata, and added this second-reading record.
