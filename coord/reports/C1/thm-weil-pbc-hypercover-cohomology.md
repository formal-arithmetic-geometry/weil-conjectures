# thm-weil-pbc-hypercover-cohomology

## Files written

- dag/nodes/sec-curve-estimates/thm-weil-pbc-hypercover-cohomology.json: split the comparison into five sourced steps. The statement is unchanged. No new nodes were needed; existing nodes cover injective resolutions, double-complex convergence, local lifting, refinement, and the module case. Mathlib search found no full-hypercover cohomology comparison.
- This report.

## Attachments

None. A concept and blueprint-id search in /home/ubuntu/weil-src-slopmaster2/WeilConjectures/ and a matching search in Comparator/ found no Lean declaration stating the item. The committed audit is slopmaster2: none.

## WANTED

None. Stacks hypercovering.tex, Theorem 01H0 (theorem-cohomology-hypercoverings), supplies the general comparison. The finite degreewise and module details follow the imported agent proof, with the existing finite-refinement and free-resolution nodes.

## Findings

The imported proof took the existence of injective resolutions, K-injectivity, horizontal-first convergence, local surjectivity of sheaf epimorphisms, and exactness of the module-to-abelian forgetful functor without citing nodes. It also compressed the total-complex correction and omitted an explicit degree-zero surjectivity argument. The revised proof cites the existing nodes and writes the bidegree induction, sign choice, and degree-zero cases. The source path to the master blueprint file is absent from this worktree; its imported text is preserved in the node, and Stacks 01H0 was checked in /tmp/c1-lead-current/literature/stacks-project/hypercovering.tex.

The node is not the unit's key statement (sk-prop-h2 is the Kummer computation), so the unit's empty realized record was not edited.

## Verification

- python3 tools/review_split.py thm-weil-pbc-hypercover-cohomology: PASS, zero new nodes, generic cross-unit tool uses accepted.
- python3 tools/check_dag.py: exit 1 from 10 unreachable nodes and 11 route violations in other items; zero cycles and zero self-loops. None of its findings names this item.
- JSON parses. No Lean was written or built. No commit or push.

## Review by C1

I read Stacks `hypercovering.tex` Theorem 01H0 (`theorem-cohomology-hypercoverings`) and compared the unchanged item statement and five new steps with its injective-resolution comparison. The blueprint markdown is unavailable locally, so I also compared the worker's expansion with the imported proof text in this node. The finite split hypercovers and module-coefficient clause are stronger specifications supplied by the existing DAG nodes, not new source hypotheses. There are no new nodes; the blueprint and Lean searches found no identical declaration.

For step 1, I opened `lem-weil-pbc-module-sheaves-enough-injectives`, `prop-weil-pbc-kinjective-resolutions-exist`, and `def-weil-pbc-etale-cohomology`: they supply the injective resolution, the bounded-below K-injective clause, and the derived group being computed. The total complex is first quadrant, so only finitely many bidegrees contribute in degree `q`. For step 2, `lem-weil-pbc-hypercover-free-resolution` states horizontal acyclicity for every injective sheaf and its constant-ring module analogue; `thm-sp-double-complex-spectral-sequences` explicitly supplies the horizontal-first spectral sequence and finite filtration. The map from Cech cochains follows from `F = ker(I^0 -> I^1)` in the resolution.

In step 3 I checked the bidegree `(p,q-p+1)` equation: once earlier components vanish it says `d_I z^{p,q-p}=0`; lifting through the sheaf epimorphism and subtracting a primitive in `(p,q-p-1)` changes only the current and next horizontal positions. `lem-weil-pbc-abelian-sheaf-epi-locally-surjective` supplies the local lift, and `lem-weil-pbc-hypercover-refinement` supplies a finite refinement meeting the finitely many requirements. Step 4 makes the same calculation for a primitive; at `q=1` it starts directly in vertical degree zero, while at `q=0` injectivity follows from `F -> I^0`. The claim that the remaining primitive is in `F` uses the vertical component of `db=a`, which the step states. These checks cover the small-degree cases the imported proof compressed.

For step 5 I opened the refinement node's cofilteredness and homotopy clauses; its common refinements and prism identity justify the colimit and independence of choices. The K-injective-resolution node states functoriality up to chain homotopy. I accepted the four cross-unit citations in `tool_uses` as generic injective, spectral-sequence, and module-forgetful tools; none replaces the unit's hypercover route. The module forgetful node and the site epimorphism node provide the local lifting used there. I found no missing hypothesis or cycle. The worker's first draft already had the needed cited statements and degree-zero cases, so no correction was sent; delivery-errors A-F were checked on the item and report.
