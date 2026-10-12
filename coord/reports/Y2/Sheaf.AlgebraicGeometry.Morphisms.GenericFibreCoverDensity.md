## What changed
Proved `AlgebraicGeometry.Scheme.genericFibre_cover_reduced_and_dominant` without
changing its signature. Two proved private helpers establish reducedness of smooth
algebras over domains and smooth schemes over integral bases. Reducedness follows
by flat injection into fraction-field base change and the existing source theorem
`Algebra.Smooth.isReduced_of_field`. Dominance follows from openness, preimages of
dense sets, pullback point lifting through `Scheme.Pullback.range_fst`, and pasting
the given squares. Added proof imports of `Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen`
and `WeilConjectures.Mathlib.RingTheory.Smooth.StandardSmoothOfFree`.
The node's proof and proof dependency list now record this argument.

## Proved and sorry left
Closed the one original hole:
`AlgebraicGeometry.Scheme.genericFibre_cover_reduced_and_dominant`.
No holes remain in the item and no holes were added. The two private helpers are
fully proved. The existing field-smooth reducedness input has a closed source audit.
The single-file compiler passes without warnings. The proof handles an empty X;
nonemptiness of an affine base neighborhood is derived only after fixing a source
point, and density uses no nonemptiness hypothesis on X.

## No longer needed
No baseline imports, nodes, or modules were removed. The general theorem that smooth
schemes over arbitrary reduced bases are reduced is unnecessary for this proof:
integrality permits the fraction-field argument. No new module is required for it.

## Where the brief, the DAG or earlier work was wrong
The earlier plan had no Lean proof dependencies and described general reduced-base
reducedness as unformalized. Its integral-base case follows from the existing
smooth-algebra-over-field theorem using flat tensor-product injectivity. The
existing node `lem-sc-smooth-algebra-reduced-field` is used as a generic tool; this
keeps the unit route unchanged. No statement correction was needed.

## Second reading by Y2

1. Compared the delivered module with the repository version. The theorem signature and all existing declarations are unchanged; only proof imports, private helpers, and the theorem proof were added. Verdict: pass.
2. Compiled the module with `lcompile.py`; it passes without warnings. There are no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by` declarations, and the helpers contain no postponed data. Verdict: pass.
3. Checked the private helper arguments and target edge cases. The smooth algebra reducedness argument uses injective fraction-field base change, and the dominance proof works when X is empty. No new split-off statements were introduced. Verdict: pass.
4. Reviewed the proof route and imports. The route uses the existing smooth algebra over a field result, Mathlib openness and pullback range lemmas, and the two added imports are proof-only. Verdict: pass.
5. Compared the node's `proof`, `proof_deps`, and `proof_origin` with the Lean proof. They record the fraction-field reducedness and openness/density route, retain the unit route, and agree with the unchanged target statement. Verdict: pass.

Changed only the proof imports, private helper proofs, target proof, node proof metadata, and this review report; no statements or definitions were changed.
