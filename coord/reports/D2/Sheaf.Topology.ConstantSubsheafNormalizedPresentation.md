## What changed
Added `ConstantSubsheafNormalizedCore.lean`, defining `NormalizedPresentationData` and reducing the target to two named intermediate theorems. The target module now invokes the core existence theorem and completion theorem. Both modules compile in the sandbox.

## Proved and sorry left
The target theorem `TopCat.Sheaf.constantSubsheaf_normalized_presentation` is reduced by a complete Lean proof to `constantSubsheaf_normalized_core` and `constantSubsheaf_normalized_completion`. The latter two remain `sorry`, representing (1) finite clopen refinement, gcd closure, stalk bound, and epi construction, and (2) extraction of canonical sections and the divisibility conclusion.

## No longer needed
No planned imports were removed. The target's existing proof imports remain available; the new core module imports only the statement-level sheaf and extension modules needed for its data structure.

## Where the brief, the DAG or earlier work was wrong
The previous attempt stopped without writing a Lean reduction. The blueprint's normalization argument requires substantial finite refinement and stalkwise epimorphism constructions; these are now explicit named intermediate statements.

## New nodes
`lem-sc-constant-subsheaf-normalized-core` (new module declaration `constantSubsheaf_normalized_core`) and `lem-sc-constant-subsheaf-normalized-completion` (declaration `constantSubsheaf_normalized_completion`) are represented in `ConstantSubsheafNormalizedCore.lean`; their proofs are documented at the declarations and remain open for follow-up workers.

## Earlier second reading (a previous round; superseded)
The target reduction compiles. The two intermediate statements are strict subproblems: core data construction and completion of the target witnesses. Both remain open for follow-up workers.

## Second reading by D2

1. Compared the delivered target module with the repository version. The theorem signature and all existing declarations are unchanged; only the proof and the required new core import were added. Verdict: pass.
2. Compiled both delivered modules with `lcompile.py --all`; compilation succeeds without errors. The only remaining `sorry`s are the two named intermediate theorems, each with a public declaration, source docstring, and matching DAG node. No forbidden declarations or hollow definitions were introduced. Verdict: pass.
3. Checked the split statements. `constantSubsheaf_normalized_core` supplies the normalized finite data, while `constantSubsheaf_normalized_completion` supplies the canonical sections and value equations from that data; together they imply exactly the target. Both are true subproblems rather than aliases of the target. Verdict: pass.
4. The proof follows the declared split route. The target DAG proof and dependencies now name the two intermediate nodes. The duplicate `ConstantSubsheafNormalizedCore` import was removed as unused. Verdict: pass.
5. The unit route remains represented by the target node and its two strictly lower split nodes; no target statement or definition changed. Verdict: pass.

Changed during second reading: removed the duplicate core import, and synchronized the target DAG proof/proof_deps with the Lean proof. No statements were changed.
