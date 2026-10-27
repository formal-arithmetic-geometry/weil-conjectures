# Stage-1 report: lem-trf-automorphism-tensor-reduction-comparison

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-automorphism-tensor-reduction-comparison.json`: statement, split into seven proof steps; no full Mathlib match.
- `citations.json`: exact statement excerpts for all 15 step/node citations.
- `searches.jsonl`: the five searches actually run by msearch.py for this item.
- `report.md`: this report.

No new DAG nodes, Mathlib leaves, unit changes, Lean writing or compiler invocations. The sandbox helper `write_split.py` only generated these sandbox artifacts and is not a project file.

## Attachments

None. Searches in `lean/WeilConjectures/` for the blueprint tag, quotient-semilinear systems, strict systems, inverse image and tensor/scalar transport did not find a declaration stating every clause. Existing generic scalar-extension results do not themselves state the quotient-system and completed-coefficient compatibilities of this item.

## WANTED

None. The needed construction sources are present locally.

## Findings and changes

The imported statement is retained verbatim, including arbitrary unbounded complexes, arbitrary quotient-linear transitions, both actual coefficient squares, and the absence of flatness, cartesianness and finite Tor-amplitude assumptions. The imported node had no proof. Its seven earlier Mathlib search records and all blueprint/creation metadata are retained; five real, logged searches supplement them. LeanFinder was tried with a second, more general scalar-extension phrasing. Its scalar-restriction and free-sheaf hits do not cover the statement. I read the relevant Mathlib PullbackContinuous, PullbackFree and ChangeOfRings source; neither unit/free pullbacks nor their sheafification comparisons are the full arbitrary-system assertion.

The principal reuse is `lem-weil-sheaf-scalar-extension-ring-iso`, which already supplies the normalized tensor inverse and its naturality on any small site. Rather than restating a clause as a new node, the split constructs the quotient tensor transitions by conjugation with that existing isomorphism, and calculates their generator formula. There is no claim that arbitrary sections of a sheafified tensor product are globally pure tensors.

Blueprint searches: `blueprint_refs.py ancestor` gives `thm-trf-l-function-euler-product`, as the imported ancestry already records. Searches for `tensor isomorphism`, `scalar extension`, `quotient semilinear`, and `inverse image pullback`, and whole-DAG searches for scalar-extension ring isomorphisms and quotient-linear transitions, identified no blueprint node stating the whole item. The general scalar-extension lemma is reused, not copied. The nearest related trace nodes are consumers or larger coherent-system statements; citing them would not be this proof.

This is an agent-written expansion of the coefficient-transition assertion in the current blueprint's `prop-trf-rational-frobenius-integral-model.proof.md`, clauses (2)-(3), supporting the recorded Global powers step. It does not replace a unit route. The three statement tools from other units are declared in `split_report.tool_uses` with their exact roles. The chapter and unit records are unchanged.

## Not duplicates

No new nodes are proposed. The generic ring-isomorphism tensor comparison, automorphism inverse-image properties, and componentwise system exactness are all cited as existing nodes.

## Review by Q84

I read the current item source `literature/blueprint/main-20261015/blueprint/sec-trace-formula/sk-d-weil/prop-trf-rational-frobenius-integral-model.proof.md`, particularly the assertion that the automorphism fixes coefficient sheaves and commutes with reductions. That text does not contain the detailed strict-system calculation, so the proof is explicitly marked agent-written. I also read Stacks `sites-modules.tex` at Tag 03CZ (`sites-modules-lemma-adjointness-tensor-restrict`, including the preceding change-of-rings construction) and Tag 03EK (`sites-modules-section-tensor-product`), and `proetale.tex` at Tag 09A5 (`proetale-section-morphism`), checking tags against `tags/tags`. The latter is background for the inverse image, not a citation pretending that Stacks states this complete lemma. No SGA source is used. There are no new-node sources to audit.

For Step 1 I checked the statement of `lem-weil-proetale-isomorphism-inverse-image`: clause (3) explicitly gives naturality for every coefficient ring homomorphism, hence the actual quotient square. The structure-isomorphism paragraph of `def-weil-inverse-image-pullback-comparison` explicitly defines the completed map by its components and states its projection square. The completed-coefficient definition supplies the inverse-limit cone with the displayed projections. Thus both equations are available as statements, without using an unstated monoidality claim or assuming an inverse image preserves limits for an arbitrary morphism.

For Step 2 I checked the module-action construction in `def-weil-proetale-inverse-image` and the entire statement of `lem-weil-sheaf-scalar-extension-ring-iso`. The latter has exactly the required arbitrary module hypothesis, explicit forward/inverse section formulas, sheafification unit and naturality. Its small-site hypothesis is met by the chosen small pro-etale site conventions already in the item. Applying it to each term and differential gives a complex isomorphism directly; no K-flat resolution or derived tensor is introduced.

For Step 3 the inverse-image definition says to apply the inverse-image functor to the action map; applying it to the action-compatibility equation of v gives the displayed semilinearity equation. I wrote the substitution through the inverted quotient coefficient square. `def-pc-sheaf-restrict-scalars` defines exactly the target action used. This checks the ring-map direction: B_{n+1} acts on the target through rho_n, never its nonexistent inverse.

For Step 4 the existing scalar-extension lemma gives theta on a sheafified local tensor. Conjugation with j and theta defines an actual sheaf map before the formula is computed. Its three-line computation proves the formula and the square tau_n j_{n+1} = j_n F(v_n). No missing balancing lemma is hidden here, since the composite is already a linear sheaf map. I checked rho_n(1)=1 and that the inverse action c^{-1}, rather than c, is used throughout.

For Step 5 I checked `def-weil-abstract-derived-category` for the ordinary complex and chain-map conventions. The displayed three-composite equality explicitly uses the strict system chain-map equation; differential compatibility follows from the already proved chain-map identities. It does not infer equality of derived morphisms from evaluation, and does not assume strictification of a derived tower.

For Step 6 I rechecked the actual completed projection square in the comparison definition, and computed the inverse-square action on a local completed scalar b. Restriction along pi_n is precisely `def-pc-sheaf-restrict-scalars`. The cone equation from the completed-coefficient definition gives the transition linearity formula on both sides. The completed coefficient is the inverse limit, not the discrete constant ring sheaf R.

For Step 7 I used only clause (2) of the automorphism inverse-image node for exactness, the kernel/cokernel sentence in `def-weil-sheaf-of-modules-category` for passing to transported module structures, and the first paragraph of `lem-coef-semilinear-derived-sections`, which explicitly asserts componentwise exactness of the strict system category. I deliberately use none of the latter's stronger derived-operation assertions. The automorphism hypothesis is essential to the cited equivalence and is present.

Small-case checks: when g is the identity every formula reduces to x -> x tensor 1 and coefficient reduction. Zero modules and zero transitions give zero maps with the same identities. At n=1 the quotient still maps units to units, with no division by the uniformizer. A system with zero transitions is generally noncartesian but the conjugation construction and exactness still apply. Nonflat torsion modules over R/varpi^n are allowed because c_n is a ring isomorphism and no tensor-exactness assertion for a quotient map is used. Doubly unbounded complexes introduce no sums or totalizations: all formulas are degreewise. The empty scheme gives zero sheaves, for which the maps remain isomorphisms. These checks found no false or missing hypothesis.

Against delivery-errors B-E, I verified no elementary fact or item clause was promoted to a node, all cited statements are actually read, every non-elementary input is cited, and every quotation is an exact substring. All seven steps are below 2000 characters and hide no further comparison lemma: the sole tensor comparison is the existing generic lemma. The dependency graph and route checks are delegated to the required server checks. The final delivery dry run will record their acceptance.

## Unfinished work

None in the mathematical split. Delivery proceeds only after the required server dry run passes.
