## What changed

Proved `Algebra.bijective_augmented_polynomial_truncations_injective` without changing its signature. The sole module now contains proved private helpers for degrees zero and one, formal-smooth inverse lifting, and injectivity of an endomorphism close to the identity modulo a nilpotent ideal power. The final proof performs the degree-two induction and uses the existing surjectivity theorem. Added proof-only imports of `Mathlib.RingTheory.Ideal.Quotient.PowTransition` and `Sheaf.RingTheory.Smooth.AugmentationPolynomialTruncationsSurjective`.

The DAG proof is updated to the Lean argument. Explicit polynomial substitution is replaced by the general estimate `e(x) - x ∈ L^(r+k)` for `x ∈ L^(k+1)`. This also handles zero variables and the zero base ring without extra hypotheses. All intermediate helpers are proved, so no new statement modules or nodes are delivered.

## Proved and sorry left

Closed the only local hole: `Algebra.bijective_augmented_polynomial_truncations_injective` (node `lem-sbc-formally-smooth-augmentation-truncations-injective`). Holes closed: 1. Holes added: 0. No `sorry` remains in the delivered module.

The proof uses the existing named theorem `Algebra.bijective_augmented_polynomial_truncations_surjective` (node `lem-sbc-formally-smooth-augmentation-truncations-surjective`), as the original DAG plan requires. This dependency was proved in the repository during the session and is not changed by this delivery. `#print axioms` for both the target theorem and the surjectivity theorem reports exactly `propext`, `Classical.choice`, and `Quot.sound`: no `sorryAx` is reachable. The complete module compiles cleanly via `lcompile.py`.

## No longer needed

No original imports, nodes, or modules are pruned. The second reading removed the redundant newly added proof import `Mathlib.Tactic.Ring`; the ring tactic is already available through the retained imports. No polynomial substitution or formal inverse-substitution API is required: the nilpotent ideal-power estimate replaces that calculation inside the target's node. The surjectivity dependency remains necessary. No tentative split modules or nodes are part of the delivery.

## Where the brief, the DAG or earlier work was wrong

No mathematical errors found. The original DAG statement's degree-zero, zero-ring, and rank-zero cases are covered. The Stacks 05D5 final correction step admits the simpler general ring-endomorphism proof implemented here. The independent second reading is recorded below.


## Second reading by W4

1. **Interfaces: pass.** Read the complete module and its diff against the repository. The existing public theorem signature is byte-for-byte identical, as is its docstring. No existing declaration, definition, visibility, or public import changed. The only new declarations are four proved private theorem helpers; no change record is needed.
2. **Proof and axioms: pass.** Compiled the delivered module locally with `lcompile.py`, without errors or warnings. Compiled a scratch copy with `#print axioms` for both `Algebra.bijective_augmented_polynomial_truncations_injective` and `Algebra.bijective_augmented_polynomial_truncations_surjective`: each uses exactly `propext`, `Classical.choice`, and `Quot.sound`. Inspected every helper and found no sorry, forbidden declaration, hollow definition, or arbitrary witness taken from an unproved existence theorem. The lifted map comes from Mathlib's proved formal-smooth lifting theorem.
3. **Intermediate statements: pass.** No statement is split off and no holes are added. Checked the proved helpers: degrees zero and one require no nontriviality or positive rank; the correction estimate uses r >= 2 precisely for 2r-1 >= r+1; zero variables, the zero base ring, and L = bottom are included. The lift sends I into the image of J by reduction and degree-one injectivity, so its descent through I^(r+1) is justified. An independent LeanFinder query for an endomorphism congruent to the identity modulo a nilpotent ideal power, and `rg` searches of Mathlib and both library roots, found supporting results but no applicable shorter replacement.
4. **Route and pruning: pass after import cleanup.** The target is proved downward by degree-two induction, using the original surjectivity dependency, Mathlib formal-smooth lifting, and proved local ideal-power estimates. No unit step is bypassed. Read `dag/units/sk-prop-input-spreading.json`: the completion computation remains within its existing depth-two extension step; its `realized` lists are already empty and are unchanged. The sole old proof dependency remains used, so the no-longer-needed node list is complete. A scratch compile succeeds without the newly added `Mathlib.Tactic.Ring` import. A separate scratch experiment fails without `PowTransition` because `Ideal.Quotient.factor_ker` is unavailable, confirming that import is necessary. Existing public imports retain the statement's APIs.
5. **DAG: pass.** Compared the node records as parsed JSON: only `proof` and `proof_origin` change. Its statement and Lean signature are unchanged, and `proof_deps` remains exactly the original surjectivity node. Read that dependency's actual proved declaration. The updated proof steps describe the lift, its descent, the ideal-power estimate, and the final induction as implemented. No new nodes are required for unresolved work because there is none.

Second-reading change: removed only the redundant proof import `Mathlib.Tactic.Ring` and updated this report. Kept the correct proofs and node record. Holes closed: 1 (`Algebra.bijective_augmented_polynomial_truncations_injective`); holes added: 0; split off: 0; modules pruned: none.
