# Worker report

Files written:

- `dag/nodes/sec-smooth-purity/lem-route-twist-scalar-maps-exists-unique.json`: repaired statement, hypotheses, proof steps, dependencies, search records, proof origin, and route tool declarations; no new nodes and no Mathlib leaves.
- `citations.json`: verbatim statement quotes for every cited node in every repaired proof step.

Attachments: none. `WeilConjectures.twistScalarMaps_existsUnique` in `lean/Sheaf/Paper/CoefficientTwistsDetailed.lean:500-502` still has `sorry`, so it is not a finished attachment.

WANTED: none.

The previous delivery was returned for missing TeX escapes, a mismatch with the Lean indices and hypotheses, an omitted linearization-isomorphism argument, incomplete search provenance, and undeclared generic route uses. All are repaired below and in the node.

## Not duplicates

- `lem-route-twist-scalar-maps-exists-unique` vs `lem-pur-signed-line-scalar-tensor-tower`: the existing node gives signed-power maps after an already supplied degree-one isomorphism; this item proves existence and uniqueness of the normalized degree-one map and then supplies that isomorphism locally.
- `lem-route-twist-scalar-maps-exists-unique` vs `lem-pur-twist-sheaf-locally-free`: the existing node proves local rank-one freeness of the root and integral twist lines; this item constructs the coefficient-field semilinear family and its normalization.
- `lem-route-twist-scalar-maps-exists-unique` vs `lem-pur-signed-line-native-evaluation`: the existing node supplies the signed-line evaluation pairing; this item uses it to define and uniquely determine the negative-degree maps.

## Repair notes

1. Every TeX command in the statement is now escaped (`\\ell`, `\\mathbf`, `\\hookrightarrow`/algebra map notation, `\\otimes`, `\\operatorname`, and all displayed symbols).
2. The statement now includes `[Algebra (Padic \\ell) L]` and `[FiniteDimensional (Padic \\ell) L]` as “an algebra structure over `\\mathbf Q_\\ell` and finite-dimensional over it”, and `\\iota:E\\to_{\\mathbf Q_\\ell}L` as the algebra map. Clause (iii) is exactly the Lean range `n : \\mathbb N`, equivalently `m\\ge1` with output degree `m+1`; clause (iv) uses degree `-(n+1)` (`Int.negSucc n`) paired with degree `n+1`.
3. The proof now cites completed coefficient definitions and explicitly explains semilinearity and restriction of scalars. Before invoking the signed-line tower, Step 2 trivializes the root line by compatible roots, checks that degree one sends generator to generator, and proves the linearization `R_L\\otimes_{R_E}\\mathcal O_E(1)\\to\\mathcal O_L(1)` is an isomorphism using the completed coefficient tensor normalization.
4. Mathlib searches were rerun after the repaired statement: LeanFinder, Loogle, Mathlib grep, and LeanSearch. Their exact queries and returned hits are recorded in the node’s `mathlib_searches` and the sandbox `searches.jsonl`; no Mathlib declaration matches this project theorem.
5. `proof_origin.by` is now `agent`, since the blueprint defines the twist lines but does not state the E-to-L normalized family. Generic route departures are declared in `split_report.tool_uses`: `sk-def-sf-admissible`, `sk-prop-an`, and `sk-def-sp-scalar-extension`.

## Review by NA

I reread the attached Lean context at `CoefficientTwistsDetailed.lean:435-502`, including the exact `TwistScalarMaps` and `IsCanonicalTwistScalarMaps` clauses, and checked the repaired statement against each binder and index. I reread the latest blueprint `def-coefficient-twists-detailed.md`, the completed coefficient and scalar-data nodes, the completed coefficient tensor-normalization node, and the signed-line local-freeness, scalar-tensor-tower, dual-local-isomorphism, and native-evaluation nodes.

Step 1 now uses the completed inverse-limit ring map induced by `\\iota`, the restriction-of-scalars action, and the root-limit tensor formula; these are stated by the cited completed scalar-data and coefficient-twist nodes. It also records why quotient transition formulas descend and are semilinear. Step 2 checks the hypothesis missing before the return: on a compatible-root cover, both lines are free on the same root generator, and the completed coefficient tensor normalization carries the scalar extension to the target line, so the degree-one linearization is an isomorphism. Step 3 applies the signed-line tower only after that isomorphism has been established and matches the Lean range `m\\ge1`. Step 4 uses the canonical dual comparison and the tower’s evaluation formula with the corrected `-(n+1)` index. Steps 5–6 use local generation and the evaluation pairing to glue and prove uniqueness. Every citation in `citations.json` was checked as a verbatim substring of its cited statement. I checked $m=0,1,-1$, the empty scheme, and $L=E$ with the identity algebra map. No SGA source is used.
