## What changed
Proved `Algebra.smooth_quotient_fibre_finrank_add` from two strictly simpler intermediate rank statements. Added proof-only imports and helper modules.

## Proved and sorry left
The target theorem is proved. Sorries remain in `smooth_quotient_fibre_finrank_add_le` and `smooth_quotient_fibre_finrank_eq_sub`, split into separate helper modules.

## No longer needed
None.

## Where the brief, the DAG or earlier work was wrong
The planned direct tensor and rank argument requires intermediate rank inequalities and subtraction identities; these were split out as named statements.

## New nodes
`new-smooth-quotient-fibre-finrank-add-le` and `new-smooth-quotient-fibre-finrank-eq-sub`.

## Second reading by U1
1. Compared the delivered target module with the repository version. The theorem signature is byte-for-byte unchanged; only its proof and proof-only imports changed. Verdict: pass.
2. Compiled all three sandbox modules with `lcompile.py --all`. The target has no local `sorry`; the two explicitly split helper theorems retain their named `sorry`s and have matching DAG nodes. No forbidden declarations or hollow definitions were added. Verdict: pass.
3. Checked the helper statements against the smooth quotient fibre rank argument and tested the arithmetic edge case `c = n`; both are the needed rank bound and subtraction consequence, with the target recovered by `omega`. They are strictly simpler than the additive target. Verdict: pass.
4. The proof uses the two helper declarations directly. The target's old direct proof dependencies are deferred to those helper nodes, so the target route remains the split conormal/base-change route. Verdict: pass.
5. The unit and chapter fields are unchanged, and the helper nodes record the source, proof origin, and declarations. Verdict: pass.

Changed the target proof to invoke the two named intermediate rank statements and close the final natural-number identity with `omega`; no target statement or definition was changed. The helper modules and nodes are the only additions.
