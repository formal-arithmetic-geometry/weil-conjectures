Files written:

- `dag/nodes/sec-purity-real-sheaves/lem-wf-curve-finite-level-pd.json` — the imported item is now split with five proof steps and one new cited node; Mathlib searches found no matching project theorem.
- `dag/nodes/sec-purity-real-sheaves/lem-wf-bounded-free-complex-projective-cohomology-splitting.json` — statement-only lemma, unsplit; Mathlib searches found no exact splitting theorem.
- `citations.json` — verbatim quotes for every cited node in every item proof step.

Attachments: none. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the item id, title, finite-level pairing terminology, and the Poincare-duality declarations. The source contains no declaration tagged `(blueprint: lem-wf-curve-finite-level-pd)` and no sorry-free declaration with the exact item statement.

WANTED: none.

## Not duplicates

- `lem-wf-bounded-free-complex-projective-cohomology-splitting` vs `lem-pod-perfect-point-complex-field`: the existing node is only the field criterion for perfect point complexes; it does not state a splitting theorem over an arbitrary commutative ring with projective cohomology.
- `lem-wf-bounded-free-complex-projective-cohomology-splitting` vs `def-pc-perfect-ring-complex`: the existing node defines perfect objects in terms of bounded finite-projective models; it does not state that a bounded finite-free complex splits into its cohomology summands.

What was wrong in the imported split: its second paragraph called the finite-free/projective-cohomology splitting “elementary” while using a full descending induction on cycles and boundaries. I made that hidden lemma an explicit statement-only node and cited it. I also changed the formerly null fourth step into a complete argument with the derived-duality and splitting citations, and checked that the degree-one component is the cup–trace adjoint. The item statement itself is unchanged. The slopmaster2 `Degreewise.lean` source has only an abstract finite-field degreewise isomorphism and explicitly says it does not prove the exact perfectness assertion, so it cannot be attached to this item; the DAG’s proper-duality node supplies the natural-language derived isomorphism used here.

What I could not finish: nothing remains in the split. The new splitting lemma is intentionally unsplit for a later worker.

## Review by Q01

I read the current item node, the `sec-purity-real-sheaves` chapter record, the `sk-p-real-rankone` unit record, and both the master and main-20261015 blueprint files for this item. I read the full statements of every cited node. In step 1, `lem-sc-cohomological-dimension` supplies vanishing above degree two for the twisted torsion sheaf; `thm-sc-proper-cohomology` supplies the rank-one degree-two calculation after the primitive-root trivialization; `lem-wf-curve-kummer-jacobian-tate-module` supplies the twisted degree-one Jacobian identification; and `thm-av-final` clause (c) identifies prime-to-characteristic torsion with a free module of rank (2g). Connectedness and the absence of negative cohomology for a sheaf in degree zero are the elementary parts of that step, and the same root choice gives the untwisted finite-free cohomology.

In step 2, I checked the finite-level clause of `thm-pod-point-perfectness` gives bounded finite-free representatives and that the new splitting node states exactly the needed direct-sum decomposition. The new node was searched against the whole DAG and blueprint; the field-only splitting criterion and the definition of perfect point complexes are weaker or differently scoped, so they are cited in the duplicate audit rather than substituted.

In step 3, I checked the hypotheses of `thm-pod-proper-poincare-duality`: (C) is proper of dimension one, the constant coefficient object is finite free and perfect, and its coefficient dual with twist (1) is (A_n(1)). The theorem’s displayed adjoint is exactly the derived isomorphism used. Step 4 then takes its degree-one component after the two decompositions and identifies it with the cup product, evaluation, and normalized trace named in that theorem. Step 5 records the finite-level equivariance consequence from `thm-pod-equivariance-of-the-twisted-pairing`; this is extra structure compatible with, and does not weaken, the stated perfectness conclusion.

I verified every `uses` entry against the cited node’s statement, checked that `proof_deps` is the union of the step uses, and checked every `citations.json` quote as a verbatim substring. The small cases (g=0), (n=1), and the degree-zero/degree-two terms reduce to free rank-one modules, while the degree-one group is zero for (g=0), so the asserted perfectness has the expected edge behavior. No statement correction or undeclared tool use was needed.
