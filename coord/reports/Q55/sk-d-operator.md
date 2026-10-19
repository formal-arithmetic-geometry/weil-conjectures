# Worker report

## Files written

- `dag/nodes/sec-trace-formula/sk-d-operator.json`: item, definition-only split with each map explicitly specified, no new nodes or Mathlib leaves.
- `dag/units/sk-d-operator.json`: realized statement set to `sk-d-operator`; no numbered proof steps.
- `citations.json`: empty because the item has no proof steps.

## Attachments

None. The declaration `AlgebraicGeometry.ProEtale.Correspondence.globalOperator` in `WeilConjectures/SixFunctors/ProEtale/TraceFormula/Correspondence.lean:861-866` is sorry-free, but it is not an exact attachment: it requires `hK : G.ctf X K` together with `[IsGeometric aX]`, `[IsGeometric c.str]`, `[HasCompactification aX]`, `[IsProper c.snd]`, and `[HasCompactification c.str]`, while this unit sketch only states the endocorrespondence with proper ordinary leg and the displayed operator formula. The existing detailed DAG node `def-trf-global-operator` states the expanded construction and is reused; it is not a new node.

## WANTED:

None.

## What was wrong or incomplete

The imported unit is intentionally a sketch and has no proof list. Its statement is mathematically the compact-support global-operator composite: unit for `c₂^* ⊣ Rc₂*`, proper identification `Rc₂* ≅ Rc₂!`, the coefficient map `u`, composition of compact-support direct images along `c₁`, and the exceptional counit. The current main-20261015 blueprint has the same displayed formula in `sk-d-operator/_section.md`; the more detailed construction is already present as `def-trf-global-operator`, so creating another helper would duplicate that node. The source Lean declaration has a stronger typed setting and therefore cannot be attached to this broader sketch item.

I searched the whole DAG and blueprint for the global-operator formula and declaration name. `def-trf-global-operator` is the existing same-unit detailed node; no other node states the unit sketch exactly. The required Mathlib searches were run for the item, with no relevant Mathlib declaration: LeanFinder returned unrelated continuous-cohomology and compact-support function declarations; Loogle returned 0 hits and reported `globalOperator` unknown; grep over `Mathlib` returned 0 hits; LeanSearch returned only ordinary topological compact-support and adjunction declarations. These searches do not match the derived six-functor construction.

## What I could not finish, and why

Nothing remains for this definition-only split. The mathematical statement was expanded, preserving all hypotheses: the structural maps, both adjunction components, the inverse proper comparison and the two composition comparisons are explicit. No new theorem or perfectness assertion is included. No Lean code, compiler, Lake, or build tool was run.

## Review by Q55

I read the current stage-1 brief, `stages/1-dag.md`, `SETUP.md`, `coord/dag-sync.md`, `GOAL.md`, and delivery-errors sections B-E. I read the unit and chapter records, the current main-20261015 section and detailed `def-trf-global-operator` blueprint, and the existing DAG node statement. The item has no numbered steps, so there are no step citations or citation quotes to verify; `citations.json` is therefore empty. The existing detailed node supplies the unit formula's five arrows and cites the correspondence and six-operation package, so I did not create a duplicate node or restate a clause as a new node.

For the source check, I read `Correspondence.lean` around lines 809-866. `globalOperatorUnit` supplies the unit/proper comparison/composition, `globalOperatorCounit` supplies the compact-support composition and exceptional counit, and `globalOperator` composes these with the coefficient map. I verified the Lean declaration's extra `ctf`, geometric, compactification and properness hypotheses and recorded why they prevent attachment. I checked edge cases in the statement: when the correspondence is the identity, the composite has the expected identity-adjunction shape; when `u` is zero, the middle map makes the operator zero; and properness is used only for the `Rc₂* ≅ Rc₂!` identification. The detailed existing node has the same construction only in its narrower finite-field ctf setting, so it is not added as a dependency or exact same_as. Instead every component is explicitly constructed from the original sketch dependencies: sk-d-corr states the arbitrary-K coefficient map and the c₁ exceptional adjunction, and sk-d-six states the two adjunctions, proper comparison, composition comparison and RΓc notation. These are supplied data, not theorems assumed from the proof of a definition. The added display uses P₂ inverse at c₂* K and μ₁ inverse at c₁! K, so the sources and targets match without assuming ctf stability.

I checked B1-B9, C1-C5, D1-D5, and E1-E6: no new unsplit node, no uncited proof fact, no duplicate, no cycle, no Mathlib leaf, no SGA citation, and no statement weakening. The unit's realized fields now point to this item and record that it has no numbered proof steps. The blueprint fields retain `is: sk-d-operator` and set `same_as` to the empty list; the split report identifies the exact section and formula realized.

Mathlib scope correction: the initial grep subdirectory arguments Mathlib and WeilConjectures were invalid as scopes beneath Mathlib; their no-hit results are recorded but not used as evidence. I reran grep over AlgebraicGeometry and over all Mathlib, obtaining zero hits for globalOperator/lowerShriek/UpperShriek/LowerShriek. All actual queries, including the invalid initial Loogle identifier, are recorded with their original text in the item and searches.jsonl.


## Second reading by Q55

- Item statement: checked against main-20261015 `sec-trace-formula/sk-d-operator/_section.md`, its complete displayed composite, and the exact statements of `sk-d-corr` and `sk-d-six`; all six arrows have the required domains and codomains. The definition uses the ambient derived category, not a claim that compact cohomology is perfect.
- Proof steps: there are no numbered proof steps, since this is a definition. The unit at K is supplied by `sk-d-six`; applying Ra_X! gives the first arrow, with target Ra_X! Rc_2* c_2* K.
- Proper-comparison component: `sk-d-six` gives P_2: Rc_2! ≅ Rc_2* for the assumed proper c_2; its inverse at c_2* K has exactly the direction used in the second arrow.
- Composition component for c_2: `sk-d-six` gives Ra_X! Rc_2! ≅ R(a_X c_2)!; the structural equality a_X c_2 = a_C identifies its target with Ra_C!, as displayed.
- Coefficient component: `sk-d-corr` supplies u: c_2^* K → c_1^! K for the endocorrespondence; applying Ra_C! gives the fourth arrow.
- Composition component for c_1: the inverse of the same comparison from `sk-d-six`, evaluated at c_1^! K, gives precisely Ra_C! c_1^! K → Ra_X! Rc_1! c_1^! K.
- Counit component: the compactifiability and exceptional adjunction in `sk-d-corr`, also stated in `sk-d-six`, give Rc_1! c_1^! K → K; its Ra_X! image closes the endomorphism. No constructibility-stability assertion or theorem about the proof of another node is used.
- New nodes: none; no new Mathlib leaves. Searched the existing DAG and current blueprint for the operator formula and read `def-trf-global-operator`, including its `blueprint_update`; its finite-field ctf setting is narrower, so it is comparison material rather than an exact duplicate or dependency of this arbitrary-K definition.
- Existing notation dependencies: read `sk-d-setup` for A and D(Z,A), `def-nagata-compactifiable` for existence of a compactification, and `def-weil-proper-morphism` for properness; added direct citations so those notions are explicitly bound. These are existing definitions, not new claims or route replacements.
- Source Lean attachment: read `Correspondence.lean:133–153, 809–866`; `globalOperatorUnit`, `globalOperatorCounit`, and `globalOperator` use the same components, but their ctf, geometric and compactification assumptions prevent an exact attachment to this sketch. The existing audit for the detailed node also records `rests_on_sorry`, so a sorry-free body alone does not finish this item.
- Small cases: K = 0 and u = 0 leave well-typed composites through the zero coefficient map; X = C = empty and X = C = Spec(k) with identity legs have all six correctly typed arrows; n = 1 changes no component or hypothesis. Properness is needed for P_2 only; the exceptional adjunction is explicitly given, not inferred for an arbitrary morphism.
- Independent Mathlib search: ran Loogle `"shriek"` (zero hits) and grep `correspondence|cohomologicalCorrespondence` in AlgebraicGeometry (two unrelated comments); recorded the actual searches in the item and retained their automatically generated log entries.
- Citation file: `citations.json` remains empty, correctly, because there are no proof-step citations. B1–B7 and C/D/E apply without any new unsplit node, theorem, hidden proof or statement dispute; source is the blueprint formula rather than a Stacks-tagged result.

Changes: added the three direct definition citations above; corrected three failed/invalid initial search verdicts from “no match” to “invalid query; not evidence of absence”; added the two independent searches and this review. The mathematical composite, hypotheses, first worker's review, and unit realization are retained. The first worker's phrase “reused” for `def-trf-global-operator` means it was read as comparison material: it is not cited by this item's statement or proof.
