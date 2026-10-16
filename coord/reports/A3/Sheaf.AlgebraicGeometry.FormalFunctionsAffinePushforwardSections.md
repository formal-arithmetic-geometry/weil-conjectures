## What changed

Replaced the `sorry` proof of `AlgebraicGeometry.formalFunctions_affine_pushforward_sections` with the affine restriction transport proof. The proof uses `formalFunctions_affine_restriction_dictionary` to identify sections and quotient systems, applies `globalSections_formal_functions` on the affine chart, and transports the quotient and inverse-limit projection equations through the resulting isomorphisms. No public statement or definition changed.

## Proved and sorry left

The declaration `AlgebraicGeometry.formalFunctions_affine_pushforward_sections` is proved. No `sorry` remains in the delivered module and no new holes were added.

## No longer needed

None. Both proof-only imports are used: the affine restriction dictionary and theorem on formal functions, together with adic-completion functoriality for the completion transport.

## Where the brief, the DAG or earlier work was wrong

The checked-in affine restriction dictionary source currently contains its theorem in a withdrawn/commented block, while the compiled library interface provides the declaration used by this proof. The proof follows the DAG route and relies on that dependency being restored by its assigned repair.

## Second reading by A3

1. Compared the delivered module with the repository version. The theorem signature,
   definitions, visibility, and imports are unchanged; only the body of the existing
   theorem was filled in. Verdict: pass.
2. Compiled the module with `lcompile.py`, checked that it contains no `sorry`, `axiom`,
   `unsafe`, `opaque`, `extern`, or `implemented_by`, and checked its axioms. The theorem
   depends only on `propext`, `Classical.choice`, and `Quot.sound`. Verdict: pass.
3. The proof adds no split-off statements or nodes. The existing theorem statement is
   unchanged and the dictionary and global formal-functions declarations are used as
   stated; no duplicate library theorem was introduced. Verdict: pass.
4. Read the proof from the target downward. It uses the affine restriction dictionary,
   then `globalSections_formal_functions`, and transports the quotient and inverse-limit
   equations through the corresponding isomorphisms. This is the route recorded in the
   node and preserves the unit route. All imports are used. Verdict: pass.
5. Compared the node's statement, proof steps, proof dependencies, and proof origin with
   the Lean proof. They agree, and no old dependency is unused. Verdict: pass.

Changed only the theorem proof and added this second-reading record; no declarations,
statements, imports, nodes, or split-off holes were added or removed.
