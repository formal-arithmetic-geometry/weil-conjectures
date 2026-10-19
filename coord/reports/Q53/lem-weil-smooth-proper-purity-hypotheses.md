# Q53 stage-1 report

1. Files written:

- `dag/nodes/sec-zeta-weil/lem-weil-smooth-proper-purity-hypotheses.json`: the item, statement, split proof, and review metadata; no new nodes.
- `citations.json`: verbatim statement quotes for every cited node in every proof step.

2. Attachments: none.

3. WANTED: none.

4. Source and statement review:

The imported item was compared with the current main-20261015 blueprint and the existing DAG. Its old clause 1 asserted the ambient exceptional-adjoint admissibility datum. That is a source error in the current six-functor route: `sk-def-set` says the structure morphism uses the constructible exceptional adjoint with no ambient admissibility hypothesis, and its warning records that the ambient full-cohomological-dimension condition fails for smooth proper elliptic curves. I therefore corrected the statement to the unconditional constructible adjunction on the bounded constructible finite-Tor category and recorded the correction in the split summary.

Step 1 uses `sk-def-set` for the setting and `sk-thm-sf-package` for the precise unconditional right-adjoint statement. I read both statements and verified that their morphism and coefficient hypotheses cover the structure map `a_X` at the `\\Qlb` stage. Step 2 uses `prop-weil-operations`, whose statement gives the equivariant lift of `Rf^!` and says that its Weil isomorphism is induced by Frobenius exchange and adjunction maps; applying this to `a_X` gives the canonical dualizing Weil lift. I also checked the Weil-complex definition node for the pair structure. Step 3 uses `sk-lem-finite`, which explicitly gives finite-dimensional field-stage cohomology for ordinary and compactly supported global sections, and `prop-weil-operations` for the induced Frobenius actions. The constant coefficient object is bounded constructible finite-Tor, so the hypotheses apply.

I searched the DAG and blueprint for duplicate statements before deciding that no new node was needed. The three claims are supplied by existing route nodes. Small cases checked include `d=0` (the point), the empty scheme (zero cohomology), and a smooth proper curve; these also expose why the ambient admissibility clause cannot be retained. The proof dependencies equal the union of step uses, and the dependency traversal has no cycle. No Lean, compiler, Lake, or build tool was run.

5. What could not be finished: nothing.

## Review by Q53

I read the item source, the current `sk-input-weights` unit, `sk-def-set`, `sk-thm-sf-package`, `prop-weil-operations`, and `sk-lem-finite`. I checked each corrected hypothesis against the source statements: `a_X` is a separated finite-type structure morphism, the constructible `Rf^!` exists and is adjoint on `\\Dctf`, the canonical Weil lift is built from Frobenius exchange and adjunction maps, and field-stage cohomology is finite-dimensional with induced Frobenius. Each proof step cites the exact node sentence it uses, and `citations.json` records those verbatim quotes. I corrected the imported ambient-admissibility assertion and retained the rest of the intended smooth-proper conclusion.
