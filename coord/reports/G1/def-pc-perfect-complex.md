Files written:

- `dag/nodes/sec-picard-framework/def-pc-perfect-complex.json`: corrected definition dependencies and metadata; split definition, no new nodes or Mathlib leaves.
- `citations.json`: empty because definitions have no proof steps.

Attachments: none. No sorry-free Lean declaration states the scheme-level definition exactly. The source contains only point-complex and pro-etale variants, with the latter explicitly noting that equivalence with the local bounded finite-projective formulation is not formalized.

WANTED: none.

The imported node incorrectly listed `def-sc-invertible-module`, which is not used by the statement. I replaced it with the existing `def-pc-scheme` dependency, retained `def-pc-derived-category`, and made the finite-projective meaning explicit as a direct summand of a finite free module. The blueprint's `blueprint_uses` history is retained unchanged. Searches of the DAG and blueprint found related but materially different pro-etale and point-complex definitions, so no duplicate node was created.

## Not duplicates

`def-pc-perfect-complex` vs `def-pod-perfect-complex-on-x`: the latter is a pro-etale coefficient-site notion for bounded constructible objects, while this item is the scheme-level derived category definition on affine open covers.

`def-pc-perfect-complex` vs `def-weil-site-perfect-complex`: the latter is a coefficient-site definition with finite, integral, rational, and algebraically closed coefficient stages; this item concerns arbitrary schemes and `D(O_X)`.

## Review by G1

I read the item, its unit record, and the Stacks citation recorded as Tag 0BDH (Section 36.31). I checked the Lean source under `WeilConjectures/CategoryTheory/DerivedCategory/Perfect.lean` and `WeilConjectures/SixFunctors/ProEtale/Derived/Perfect.lean`: these define `DerivedCategory.IsPerfect` for complexes over a ring and dualizability-based pro-etale perfectness, but neither states the scheme-level declaration in this item, and the pro-etale source says the local finite-projective equivalence is not formalized. Since this is a definition, there are no proof steps or node citations, so `citations.json` is correctly empty. I verified that the corrected `stmt_deps` names existing nodes and that the statement itself introduces the scheme, derived object, affine cover, and finite-projective convention. I checked related DAG nodes and blueprint records for duplicates; the two closest definitions differ in site and coefficient hypotheses as recorded above. The mandated LeanFinder, Loogle, and Mathlib grep searches were run and found no exact scheme-level match. I tested the definition on the zero complex and on a bounded complex of finite free modules: both satisfy the stated local condition, while an unbounded complex does not.

What could not be finished: no Lean implementation exists for this scheme-level definition, so there is no attachment.

## Second reading by G1

- Item statement: checked against Stacks Tag 0BDH (perfect-section-perfect-complexes) and the imported blueprint definition, hypothesis by hypothesis; verdict: agrees, with the finite-projective convention made explicit.
- New nodes: none; the DAG and blueprint search found no new supporting node to inspect.
- Proof steps: none; this is a definition split, so `citations.json` is correctly empty.
- Small cases: checked the zero complex, a bounded finite-free complex, and an unbounded complex; verdict: the local condition has the expected behavior.

Changes made: confirmed that `blueprint.from` must remain null for this imported blueprint item, as required by the delivery preflight; no mathematical statement, dependency, search record, or citation was changed.
