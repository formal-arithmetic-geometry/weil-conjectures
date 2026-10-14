## What changed

Copied the completed proof of `ModuleCat.projective_resolution_ext_degree` into the sandbox. The proof establishes the equivalence by Ext-class vanishing in the forward direction and induction on the projective-dimension bound in the reverse direction, using the kernel short exact sequence and the existing successor splicing theorem. No imports were added or removed.

## Proved and sorry left

`ModuleCat.projective_resolution_ext_degree` is proved. No `sorry` remains in the delivered module, and no new declarations were added.

## No longer needed

None. All imports in the module are used by the proof or its statement.

## Where the brief, the DAG or earlier work was wrong

The repository module already contained the completed proof and the node records it as reviewed. No discrepancy was found.

## Earlier second reading (a previous round; superseded)

The module compiles independently; the theorem signature is unchanged, no sorry remains, and the proof follows the DAG route through Ext vanishing, induction, and successor splicing.

## Second reading by A2

1. Compared the sandbox module with the repository version. The theorem signature,
   imports, and proof are byte-for-byte unchanged; the sandbox only adds a comment.
   Verdict: pass.
2. Compiled the module with `lcompile.py`; it compiles cleanly. No `sorry`, `axiom`,
   `unsafe`, `opaque`, `implemented_by`, or `extern` occurs. The proof introduces no
   postponed data. Verdict: pass.
3. The existing declaration is the exact module-specific bounded-resolution versus
   projective-dimension equivalence. Its zero and successor cases are valid, and no
   split-off statements or new nodes are present. Searches found no shorter existing
   declaration. Verdict: pass.
4. The proof follows the DAG route: Ext representation for the forward implication,
   induction through the projective kernel short exact sequence, and the existing
   successor splicing theorem. No unit route is bypassed and no imports are unused.
   Verdict: pass.
5. The node's statement, proof steps, dependencies, and proof origin agree with the
   Lean declaration. No node metadata needs changing. Verdict: pass.

This second reading found no repair necessary; the delivered comment is the only
sandbox difference from the repository module.
