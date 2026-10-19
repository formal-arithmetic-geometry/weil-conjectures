# lem-wf-finite-field-tate-no-fixed — Q113

## Files written

- `dag/nodes/sec-purity-real-sheaves/lem-wf-finite-field-tate-no-fixed.json`: repaired existing statement node; no new nodes and no Mathlib leaves.
- `citations.json`: verbatim quotations for every cited dependency in every proof step.
- `report.md`: this repair report.

## Attachments

None. The item has no finished declaration in the read-only Lean source.

## WANTED:

None.

## What was wrong in the returned delivery

The landing was rejected because `lem-wf-geometric-jacobian-galois-action` had changed after the reviewed delivery. The retained imported proof step 2 still said that the scheme-level action was `id × sigma_Q` and allowed either arithmetic or geometric Frobenius according to a convention. The current cited statement instead fixes the semilinear map over `b_sigma = Spec(sigma^{-1})` and explicitly states that the induced action on points is `u ↦ u ∘ s_sigma`. I repaired step 2 to use this exact point-action clause, so for `sigma_Q : z ↦ z^Q` it is directly arithmetic Frobenius on geometric points. The fixed-vector conclusion and the other two proof steps are unchanged. No new lemma is introduced: every dependency is already an existing DAG node, and the item is not a Mathlib statement.

## Review by Q113

I read the current item node and the current `lem-wf-geometric-jacobian-galois-action` node in `dag/nodes/sec-purity-real-sheaves`, together with the main-20261015 blueprint statement and proof. I also opened every dependency cited by the three steps. Step 1 uses the general-field Jacobian theorem for existence and base change, `d-ab-field` for the abelian-variety conditions, and `def-sc-jacobian` for the Jacobian structure; those statements supply exactly the hypotheses and properties asserted. Step 2 now uses the changed Galois-action statement's explicit formula on points, the arithmetic-Frobenius convention from `d-ab-field`, the identification of the abelian-variety and abelian-group Tate modules from `def-wf-abelian-tate-module`, coordinatewise action from `def-tate-module-abelian-group`, and the vanishing of arithmetic-Frobenius fixed vectors from `prop-av-tate-no-frobenius-fixed`. The hypotheses `ell ∤ Q` imply `ell` differs from the characteristic of `F_Q`, as required by the Tate and fixed-vector nodes. Step 3 uses `thm-av-final` parts (c) and (d) for finite-level torsion, finite freeness, and finite-dimensionality; clearing a denominator gives injectivity, and finite-dimensional linear algebra gives surjectivity. I checked the edge case of the zero-dimensional Jacobian: the Tate modules are zero and the assertions remain true. The only correction made in this repair is the step-2 action formula; no statement, hypothesis, or conclusion was weakened, and no new node or duplicate was created.

## Validation

The prescribed server dry run is the next check for this repaired packet. No Lean source, compiler, Lake, or build command was run.
