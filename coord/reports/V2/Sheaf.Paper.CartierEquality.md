## What changed

The proof of `cartier_equality` is present in
`lean/Sheaf/Paper/CartierEquality.lean`. It chooses a finite transcendence basis and a
finite generating set, applies the complete-intersection fraction-field model and its
cotangent comparison, then combines rank-nullity and quotient dimension formulas. The
finite-extension clause follows from zero transcendence degree. The file compiles
cleanly and contains no `sorry`.

## Proved and sorry left

`cartier_equality` is proved. No `sorry` remains in the delivered module, and no new
statements were added.

## No longer needed

No imports or DAG nodes were removed: the proof uses the complete-intersection model,
the fraction-field cotangent model, finite transcendence-basis enumeration, and the
Mathlib linear-algebra and field-theory APIs already imported by the module.

## Where the brief, the DAG or earlier work was wrong

Nothing was found to be wrong. The existing proof follows the DAG's complete-intersection
and cotangent-model route and proves the unchanged target statement.

## Earlier second reading (a previous round; superseded)

The proof was compiled from the unchanged theorem signature. Its only dependency
statements are the existing complete-intersection and cotangent-model declarations; no
new nodes or holes are open.

## Second reading by V2

1. **Signatures and visibility.** Compared the delivered module with the repository
   version. The theorem signature and all existing declarations are byte-for-byte
   unchanged; the only difference is a proof comment.
2. **Compilation and axioms.** Compiled the module with `lcompile.py`; it succeeds
   without errors or warnings. The proof contains no `sorry`, `axiom`, `unsafe`,
   `opaque`, `extern`, or `implemented_by`, and introduces no definitions with
   unfinished data.
3. **Statements and dependencies.** No statements were split off and no new nodes
   were added. The target statement is unchanged and its proof uses the existing
   complete-intersection and cotangent-model declarations, together with the standard
   finite-dimensional linear algebra and transcendence-basis APIs.
4. **Pruning and route.** The complete-intersection and fraction-field cotangent route
   recorded by the unit is retained. Every listed import is used by the proof, so no
   import or proof dependency can be removed safely.
5. **DAG agreement.** The node's declaration, proof route, proof dependencies, and
   proof origin agree with the Lean proof; the unit's `realized` route is preserved.

No repair was needed beyond adding this second-reading record; no holes were added.
