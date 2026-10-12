## What changed

Proved `IsAlgClosed.artinSchreier_surjective_and_kernel` in
`lean/Sheaf/AlgebraicGeometry/ArtinSchreier.lean`. The proof uses the existing
sorry-free `IsAlgClosed.surjective_pow_sub_self` theorem and the finite-field
lemmas `Subfield.mem_bot_iff_pow_eq_self` and
`ZMod.fieldRange_castHom_eq_bot`. Added the required proof-only imports.

## Proved and sorry left

The declaration `IsAlgClosed.artinSchreier_surjective_and_kernel` is proved;
no `sorry` remains in the delivered module.

## No longer needed

The proof does not require the blueprint's separate abstract declarations
`def-pc-field-characteristic`, `def-weil-algebraic-closure`, or
`lem-sc-field-artin-schreier-kernel`; their roles are discharged directly by
the existing surjectivity theorem and Mathlib's prime-subfield lemmas.

## Where the brief, the DAG or earlier work was wrong

The DAG proof plan listed abstract characteristic, algebraic-closure, and
field-kernel nodes, but the source library already contains a direct
sorry-free surjectivity theorem, and Mathlib supplies the kernel identification.
No statement was changed.

## Second reading by A3

1. Compared the delivered module with the repository version. The theorem signature and all existing declarations are byte-for-byte unchanged; only the proof and imports differ. Verdict: pass.
2. Compiled the module with `lcompile.py`; it succeeds with no errors, and the delivered module has no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`. The proof uses only the existing theorem and Mathlib results; no new split statements were introduced. Verdict: pass.
3. Checked the proof route and searched the library for duplicate declarations. The surjectivity theorem and prime-subfield lemmas are existing declarations, and the kernel statement is exactly the target's set equality. No new statement was split off. Verdict: pass.
4. Read the proof and imports. It follows a shorter valid route through `surjective_pow_sub_self`, `Subfield.mem_bot_iff_pow_eq_self`, and `ZMod.fieldRange_castHom_eq_bot`; the finite-field import is proof-only and is now plain `import`. The three abstract blueprint dependencies are no longer needed, as recorded above. Verdict: pass.
5. The node's Lean declaration, proof, proof dependencies, and proof origin agree with the delivered proof; the unit route remains represented by the item's node. Verdict: pass.

Changed during second reading: changed `Mathlib.FieldTheory.Finite.Basic` from `public import` to proof-only `import`, since it is not needed by the public statement.
