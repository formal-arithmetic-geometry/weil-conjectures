# Worker report: lem-trf-absolute-frobenius-coefficient-naturality

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-absolute-frobenius-coefficient-naturality.json`: item split into three proof steps; no new nodes.
- `citations.json`: 11 verbatim statement quotes covering every cited node in every step.

## Attachments

None. I searched the slopmaster2 source for the item id, its Frobenius and coefficient terminology, and the relevant declarations; no sorry-free project declaration states this item exactly.

## WANTED

None. The item follows the current blueprint and all cited supporting nodes are present in the DAG.

## What was checked and corrected

The item statement was retained verbatim. Its hypotheses are a characteristic- $p$ scheme, finite commutative coefficient rings, an arbitrary unital coefficient map, ordinary unbounded pro-etale derived categories, and no flatness or Tor-amplitude assumption. The existing blueprint ancestry is `thm-trf-finite-coefficient-map`; the proof realizes its final coefficient-naturality sentence through the relative-Frobenius site construction and the iterate clause of `lem-trf-absolute-frobenius-site`.

No dependency node was created: the absolute-Frobenius site trivialization, its coefficient/module version and iterate law, derived change of rings, scalar pullback comparison, and the two finite-discrete constant-coefficient identifications already exist. The Mathlib searches for the item were run with `msearch.py` and are recorded in `searches.jsonl`; they found no Mathlib theorem about pro-etale Frobenius scalar naturality.

## Review by NO

I read the item source and proof paragraph in `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-sf-rf-shriek-preservation/lem-trf-absolute-frobenius-site.proof.md`, the unit record `dag/units/sk-p-trace-coeff.json`, and the complete statements of every cited DAG node. Step 1 uses the identity/composition clause of `det-prop-scalar-six-pullback`; with $b=0$, both pullbacks and both trivializations are identities. Step 2 uses the relative-Frobenius site isomorphisms and the termwise exact module construction from `lem-trf-absolute-frobenius-site` and `lem-pur-frobenius-trivialization-pullback`; it uses `lem-pur-derived-change-of-rings` for a K-flat resolution, `det-prop-scalar-six-pullback` for the coefficient comparison, and the two finite-discrete nodes to transport that comparison to the ordinary constant coefficient categories in the statement. The displayed pure-tensor calculation explicitly checks that both composites restrict along the same $r_V$ and then tensor the coefficient. Step 3 uses the iterate laws stated by the two Frobenius-trivialization nodes and the composition compatibility of the scalar comparison, then performs induction on $b$; the derived change-of-rings node explains why no flatness or finite Tor-amplitude hypothesis is introduced.

I checked the characteristic-$p$ and finite-commutative-ring hypotheses against the cited trivialization and finite-discrete statements, and checked the edge cases $b=0$, $u=\operatorname{id}$, $K=0$, empty $X$, the zero coefficient ring, and a non-flat quotient such as $\mathbb Z/\ell^2\to\mathbb F_\ell$. The split has no new nodes, so there are no duplicate-node or new-node blueprint issues. The proof steps are below the 2000-character review threshold and contain the coefficient calculation rather than hiding it behind a new restatement.

No Lean files were written and no compiler or build tool was run, as required for stage 1.

## Second reading by NO

- Item statement: checked against the blueprint final coefficient-naturality sentence, the finite-discrete coefficient identifications, the pro-etale module definition, and Stacks Tag 0F6W (`lemma-relative-frobenius-weakly-etale`); the characteristic- p, arbitrary finite commutative rings, unbounded derived categories, arbitrary unital map, all b≥0, and no-flatness clauses are retained. I added the coefficient-specific Frobenius-trivialization node to `stmt_deps` because it supplies the constant-module identification used by `tau_R`.
- Step 1: checked the b=0 identity against the iterate convention in `lem-pur-frobenius-trivialization-pullback` and clause (1) of `det-prop-scalar-six-pullback`; the identity comparison and both trivializations are identities, so the elementary verdict is correct.
- Step 2: checked the relative Frobenius object and its exact termwise module construction against `lem-trf-absolute-frobenius-site` and `lem-pur-frobenius-trivialization-pullback`, K-flat computation against `lem-pur-derived-change-of-rings`, and coefficient transport against clause (1) of `det-prop-scalar-six-pullback` plus both finite-discrete nodes; the pure-tensor calculation gives the stated square and handles arbitrary non-flat B.
- Step 3: checked the induction against the iterate clauses of both Frobenius-trivialization nodes and the composition clause of `det-prop-scalar-six-pullback`; the pasted one-step square has the displayed orientation and yields the b+1 rectangle. No hidden Tor-amplitude assumption is used.
- New nodes: none; duplicate and Mathlib searches were rechecked for the item’s Frobenius/coefficient naturality, with no match. The Stacks input is only the geometric Tag 0F6W lemma, not a coefficient-coherence theorem.
- Edge cases checked: b=0 and b=1, identity coefficient map, zero coefficient ring, empty scheme, zero complex, and the non-flat map Z/l^2→F_l; each is covered by the stated hypotheses and proof.
- Changes made: corrected the copied `created.item` and group metadata, reset the blueprint `via` list to the item’s actual ancestry, added the missing statement dependency, and declared the six generic off-route supporting nodes in `split_report.tool_uses` with their roles. No mathematical weakening or new node was introduced.
