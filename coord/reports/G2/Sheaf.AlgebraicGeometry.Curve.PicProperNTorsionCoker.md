## What changed

Retained the standalone theorem `AlgebraicGeometry.Scheme.Hom.pic_proper_ntorsion_coker`
and its original imports to repair the returned retirement. The only Lean difference from the
current repository is a comment explaining why the public declaration remains standalone.
The parent `Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion` is not adapted or delivered.
No statement, definition, visibility, or proof body changes.

## Proved and sorry left

`AlgebraicGeometry.Scheme.Hom.pic_proper_ntorsion_coker` has a complete local proof and no
`sorry` in its module. It is a reduction to
`AlgebraicGeometry.Scheme.Hom.exists_mulEquiv_prod_picZero` and
`AlgebraicGeometry.Scheme.Hom.pic_proper_ntorsion_div`, followed by Mathlib's first isomorphism
theorem. The latter imported theorem still depends transitively on `sorryAx`, so the cokernel
result is not yet proved under the project's final axiom criterion.

Holes closed relative to the current repository: none (the local proof was already present).
Holes added: none. Holes left in delivered modules: none. No statements are split off.
This is a repair of a returned retirement, not net proof progress.

## No longer needed

No imports, proof-dependency nodes, or library modules are pruned. Both old proof dependencies,
`lem-sc-pic-proper-decomposition` and `lem-sc-pic-proper-ntorsion-div`, are used.
The previously attempted parent adaptation, inlined `hc`, module withdrawal, and duplicate
retirement are withdrawn from this delivery. The original cokernel node and theorem remain.
The stale parent-node update and obsolete interface-change record were removed from the
sandbox's delivery directories; they had described the withdrawn inlining.

## Where the brief, the DAG or earlier work was wrong

The earlier retirement broke the existing parent importer and left an empty module without
the command elaborator used by the maintainer's batch probe. Restoring the original API
avoids those failures. The previous report also described the result as fully proved without
noting its imported `sorryAx` dependency. This report distinguishes the complete local
reduction from the final axiom criterion.

The unrelated batch collision between `PicardTensorFrameCoordinates` and `PicardCupProductMap`
is outside this delivery. Neither module nor the parent is changed.

## New nodes

None. No statement or definition change requires a change record.

## Second reading by G2

1. Compared every delivered Lean module with the repository using `diff`: there is one module,
   and its existing signature, visibility, docstring, imports, and proof body are byte for byte
   unchanged. Only a comment was added. No other module is adapted. Verdict: pass.
2. Compiled the standalone module and a scratch copy with `#print axioms`, using only
   `lcompile.py`. Repeated the axiom check without the stale sandbox build overlay. No error,
   warning, local `sorry`, forbidden declaration, or hollow definition was found. The cokernel
   and divisibility theorems use exactly `propext`, `Classical.choice`, `Quot.sound`, and
   `sorryAx`; the decomposition uses only the three permitted final axioms. The imported
   `sorryAx` is disclosed above. All witnesses are eliminated inside a theorem proof; no data
   definition is chosen from an undetermined existence theorem. Verdict: pass as a reduction.
3. No new or split-off statements exist, hence no new docstrings or nodes are needed.
   Checked the boundary cases: `n = 0` contradicts the nonzero-cast hypothesis; `n = 1`
   gives the trivial quotient and `ZMod 1`; positive prime-to-characteristic `n` is exactly
   the divisibility theorem's hypothesis. Verdict: pass.
4. Read the proof from its conclusion back to the decomposition and divisibility inputs.
   Searched local Lean and Mathlib with different cokernel/quotient/power terms and recorded
   `msearch.py` grep and Loogle searches. The relevant Mathlib first-isomorphism theorem is
   already used. Product-quotient and integer-quotient APIs do not remove the geometric inputs
   or shorten this direct kernel calculation enough to justify rewriting it. Public imports
   support the signature; the decomposition, divisibility, and type-tag homomorphism imports
   are proof-only plain imports. No proof dependency is unused. Inspected
   `dag/units/sk-thm-curveestimate.json`: its realized statement is
   `thm-sc-proper-cohomology` and its realized steps are empty; the curve-estimate route is
   preserved. Verdict: pass.
5. The cokernel node's `proof`, `proof_deps`, and `proof_origin` match the Lean calculation:
   decomposition and divisibility, integer cast surjectivity, kernel equality, and the first
   isomorphism theorem. Its recorded Lean signature matches the declaration. The parent
   remains a conjunction of the three component theorems, so its stale inlining metadata
   must not be delivered. Verdict: pass after that metadata repair.

Second-reading changes: withdrew the stale parent-node update and obsolete change record,
removed stale sandbox compilation outputs from the active overlay, corrected the report's
axiom/progress claims, and appended this review. No proof or signature was rewritten.
