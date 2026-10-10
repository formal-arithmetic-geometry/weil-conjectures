Files written:

- `dag/nodes/sec-picard-framework/thm-pc-picard-representable.json`: statement node, split; no new nodes.
- `citations.json`: 21 step-to-node citations with verbatim statement excerpts.

Attachments: none.

WANTED: none.

The imported Lean declaration `AlgebraicGeometry.isRepresentable_picardFunctor` (Scheme.lean:235-246) has a five-line proof but is transitively rests_on_sorry, so it cannot attach this item. I retained the imported statement and route. The source declaration uses the Lean hypotheses `IsSepClosed`, smooth relative dimension one, properness, and geometric integrality; these are the formal counterparts of the separably closed smooth projective curve assumptions. The blueprint's proof has seven numbered paragraphs: the rational-point reduction, criterion setup, conditions (1), (2)(a), (2)(b), (2)(c), and the criterion conclusion. Each paragraph's cited node was opened and checked: the rational-point node supplies existence, the sigma-isomorphism node supplies transfer to the normalized functor, the criterion node supplies the representability test, the sheaf nodes supply fppf/Zariski descent, the Hilbert/F-open nodes supply (2)(a,b), and the twisting, normalized-points, and cohomology-vanishing nodes supply (2)(c). The genus and geometric-integrality hypotheses needed by the Hilbert representability node are explicitly cited. I also checked that the group-scheme conclusion is exactly the conclusion of the criterion and is transferred by the normalized/full Picard isomorphism.

## Review by E1

I read the item source and the project declaration in `WeilConjectures/AlgebraicGeometry/Picard/Scheme.lean`, including the declaration's transitive sorry audit. I checked every proof step against each cited node's statement and recorded a verbatim quote in `citations.json`; in particular, the criterion is cited for the setup and final conclusion, the sheaf and Zariski-covering nodes are cited only for condition (1), and the twist plus vanishing node are cited only for condition (2)(c). I verified the rational-point hypothesis from smoothness and nonemptiness of a curve, the finite genus/geometric-integrality prerequisites for `thm-pc-f-representable`, and the field-extension hypotheses in `lem-pc-twist`. The off-unit citations are declared as tool uses in the node because the unit's one-line route abstracts over these generic Picard, topology, curve, and cohomology lemmas. No new node is needed because every non-elementary fact in the imported route already has a DAG node. Mathlib searches were run for the item: LeanFinder returned only unrelated class-group/elliptic-curve declarations, grep found no match, and Loogle and LeanSearch were unavailable; these results are recorded in the node.

## Not duplicates

No new nodes were created, so there are no duplicate pairs to report.

What could not be finished: nothing. The source declaration is not an attachment solely because of its transitive sorry dependencies; the natural-language split is complete.

## Second reading by E1

- Source statement: checked against Stacks Tag 0B9Z, Proposition 44.6.6, and the imported Lean declaration; the separably closed field and smooth projective curve hypotheses agree, and the group-scheme conclusion is the group-valued representability conclusion used by the project route.
- Step 1: checked against `lem-pc-rational-points-dense`, `cor-pc-sigma-pic-iso`, and `thm-pc-criterion`; the nonempty smooth curve supplies a rational point, and the normalized-to-full transfer and criterion conclusion are used with the stated hypotheses.
- Step 2: checked against the criterion and `lem-pc-f-open-subfunctor`; it explicitly instantiates $G$ and $F$ and only sets up the four criterion conditions.
- Step 3: checked against `lem-pc-rational-hyp`, `thm-pc-pic-split`, `lem-pc-k-sheaf`, `lem-pc-zariski-coverings-are-fppf`, and `cor-pc-sigma-pic-iso`; the section and structure-sheaf hypotheses are supplied before invoking the split/sheaf results, and the Zariski-to-fppf implication is stated.
- Step 4: checked against `thm-pc-f-representable`, `prop-pc-xk-integral`, and `def-pc-genus`; geometric integrality and finite genus are established before applying Hilbert representability.
- Step 5: checked against `lem-pc-f-open-subfunctor`; the exact open-immersion condition required by (2)(b) is cited.
- Step 6: checked against `lem-pc-twist`, `def-pc-pic-sigma-functor`, `lem-pc-sigma-k-points`, and `lem-pc-vanishing-above-dim`; the twist gives dimensions 1 and 0, the normalization identifies the $k$-point, and vanishing above dimension one gives all higher cohomology vanishing.
- Step 7: checked against `thm-pc-criterion` and `cor-pc-sigma-pic-iso`; the criterion yields a group scheme for the normalized functor and the natural isomorphism transfers representability to the full Picard functor.
- New nodes: none; the existing DAG nodes were searched and every non-elementary dependency is cited by its node statement.
- Small cases: the criterion was checked for the zero/trivial functor and for a field-valued test scheme; the normalized functor is the expected kernel at $k$-points. The empty scheme is excluded by the curve hypothesis, and the curve dimension is one, so the $i\ge2$ vanishing clause applies.
- Changes: replaced short label-only citation quotes with substantive verbatim excerpts from the cited node statements, so each citation records the fact used rather than only its Stacks tag. No mathematical statement or proof step was changed.
