## What changed

The target proof now combines two strictly smaller named subclaims: bounded support and termwise finite-free retracts. Their modules are imported privately by the target proof.

## Proved and sorry left

`affine_finite_free_perfect_core` is proved by a real conjunction introduction and applications of the two subclaims. The subclaims `affine_finite_free_model_bounded` and `affine_finite_free_model_retracts` remain as documented `sorry`s, with nodes `lem-affine-finite-free-model-bounded` and `lem-affine-finite-free-model-retracts`.

## No longer needed

No existing proof dependency was removed; the original direct construction is replaced by the two finer dependencies.

## Where the brief, the DAG or earlier work was wrong

The original node bundled support and finite-basis transport into one unmanageably large step. Splitting those independent obligations gives compilable intermediate statements.

## New nodes

Added `lem-affine-finite-free-model-bounded` and `lem-affine-finite-free-model-retracts`.

## Earlier second reading (a previous round; superseded)

The target conjunction proof was checked against `Scheme.IsStrictlyPerfect`; both remaining subclaims are strictly smaller and retain the stated unit route. A second worker should verify the two signatures and their documented sources.

## Second reading by Y2

1. **Statement preservation.** Compared the delivered `AffineFiniteFreePerfectCore.lean` with the repository version. The target theorem signature is byte-for-byte unchanged; only its proof and proof-only imports changed. Verdict: pass.

2. **Proof and axioms.** Compiled all three delivered modules with `lcompile.py --all`. The target has a genuine conjunction introduction applying the two named subclaims. The only remaining `sorry`s are the two documented split theorems; no definitions contain `sorry`, and no forbidden declarations occur. Their open proofs account for `sorryAx`; the target proof itself adds no other axiom. Verdict: pass.

3. **Split statements.** Checked both new theorem statements against `Scheme.IsStrictlyPerfect`: bounded support is exactly its finite-support conjunct, and the retract theorem is exactly its termwise finite-free conjunct. Both are strictly smaller than the target, true in the stated edge cases (including zero terms and rank zero), have source/docstring explanations, and have matching DAG nodes. Search records found no existing project or Mathlib theorem duplicating either statement. Verdict: pass.

4. **Pruning and route.** The two proof-only imports are required by the target proof; the public imports remain minimal for the target statement. No prior proof dependency is unused, and the DAG proof and `proof_deps` match the two applications. The unit route recorded for the item is retained. Verdict: pass.

5. **DAG and delivery consistency.** The node records, Lean declarations, module paths, and report agree, and the dry-run delivery checks compile and static consistency. Verdict: pass.

Changed during second reading: added this review section only; no Lean statements, definitions, or proof dependencies were altered.
