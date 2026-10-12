## What changed

Proved `MvPolynomial.ideal_coefficients_monomial` by decomposing its conjunction into two named intermediate theorems. Added proof-only imports of the membership and coefficient-map modules. The two intermediate theorem bodies remain `sorry` because their substantial algebraic arguments are separate stage-3 items.

## Proved and sorry left

The target declaration `MvPolynomial.ideal_coefficients_monomial` is proved by applying the two intermediate theorems. The following named theorem sorries remain:

- `MvPolynomial.ideal_coefficients_monomial_membership` in node `new-polynomial-ideal-coefficients-membership`.
- `MvPolynomial.ideal_coefficients_monomial_map` in node `new-polynomial-ideal-coefficients-map`.

## No longer needed

No existing imports or DAG dependencies were removed; the original dependency was replaced by the two strictly smaller intermediate statements.

## Where the brief, the DAG or earlier work was wrong

The original node combines the coefficient membership criterion and the full direct-sum quotient construction into one theorem. The proof plan treats these as distinct substantial arguments, so they were split into two named, independently provable statements.

## Earlier second reading (a previous round; superseded)

Pending the independent second reading; the decomposition compiles and preserves the original target signature.

## New nodes

`new-polynomial-ideal-coefficients-membership` adds `MvPolynomial.ideal_coefficients_monomial_membership`.

`new-polynomial-ideal-coefficients-map` adds `MvPolynomial.ideal_coefficients_monomial_map`.


## Second reading by N1

1. **Visible changes.** Compared the delivered target module with the repository version. The theorem signature and all existing declarations are byte-for-byte unchanged; only proof-only imports and the proof body differ. The two additional modules and their declarations are new split-off nodes, as declared in the report and DAG.

2. **Compilation and axioms.** Compiled all three sandbox modules with `lcompile.py --all`; each compiled without errors. The target has no remaining `sorry`. The two split-off declarations intentionally retain their named `sorry` proofs and have matching DAG nodes. No `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by` was added. The target proof uses only the two split-off declarations, so its only unresolved dependencies are those named theorem sorries.

3. **Statements and split nodes.** The target statement is unchanged. The membership node is exactly the first conjunct, and the map node is exactly the second existential conjunct, with the same parameters and conclusion as the target. Both are strictly smaller than the target and are required by its conjunction proof. Their docstrings state the source and the complete intended proof arguments. The map node now records the membership node as a proof dependency for its kernel identification.

4. **Shortest route and pruning.** Searched the existing Lean library and pinned Mathlib for coefficientwise ideal-membership and quotient-map results; no declaration directly proves these scalar-weighted coordinate-generator statements. The target therefore uses the shortest available route through the two necessary intermediate statements. No existing import or proof dependency became unused, so there is nothing to prune.

5. **Unit route.** The proof remains below the unit level and preserves the unit's coefficientwise-membership then quotient-decomposition route. No unit statement or realized step was changed.

**Changed in this second reading.** Updated the map node's proof steps and `proof_deps` to record its dependence on the membership criterion, and replaced the placeholder second-reading report with this review.

