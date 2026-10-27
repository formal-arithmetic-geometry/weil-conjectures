# Q156: lem-sfb-scalar-geometric-exchange-rectangle

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-scalar-geometric-exchange-rectangle.json`: statement, split into six steps; not a Mathlib leaf. Existing statement, source, ancestry, and prior searches retained. The six steps give the pullback/scalar coherence equation and the two explicit counit transposes, with the normalized section realization. No new nodes; zero new Mathlib leaves.
- `citations.json`: one verbatim statement quotation for each cited node in each numbered proof step.
- `searches.jsonl`: actual search-command results for this attempt; inherited searches in the item were retained.

## Attachments

None. I searched the project source both for the blueprint tag and for scalar/exchange/mate terminology. `CategoryTheory.conjugateEquiv_paste` in `WeilConjectures/CategoryTheory/Adjunction/ConjugatePaste.lean` proves generic pasting between left-adjoint composites, rather than this internal-module derived rectangle with its prescribed comparisons. `AlgebraicGeometry.Etale.derivedBaseChange_restrictScalars_exchange` in `WeilConjectures/AlgebraicGeometry/EtaleRestrictScalarsExchange.lean:155` concerns restriction of constant coefficients on bounded-below etale categories; it is not the arbitrary nonflat condensed scalar-extension assertion on unbounded internal pro-etale categories. Neither is an attachment.

## WANTED

None. The split is agent-written, not attributed as a proof supplied by Stacks. All source documents used are available locally.

## Findings and repairs

The item had no proof and no sandbox item from an earlier attempt. No statement correction was necessary. The proof realizes the scalar compatibility missing from the coefficient devissage of refinement isomorphism (2), without changing the compactification route. I read the chapter, unit, item, scalar/pullback normalization, and the main-20261015 refinement and scalar-six pullback proofs. The current unit record is the historical smooth-purity compactification unit, whereas the item and current source are filed under six-functors-basics; I retained those inherited fields and declared the generic off-unit normalization tools in `split_report.tool_uses`.

I read Stacks `sites-cohomology.tex`, Tag 07A7, `remark-base-change`, which defines exchange by transposing the square map followed by the counit, and Tag 0E47, `remark-compose-base-change-horizontal`, which says the horizontal base-change paste is the outer rectangle but omits its verification. Our proof supplies the verification with all scalar factors present. I also read Tag 07A6, `lemma-adjoint`, for the unbounded ringed derived adjunction, and `sites-modules.tex` Tags 03EK, `section-tensor-product`, and 0GMW, `lemma-sheafification-tensor`, for the sheafified balanced-tensor conventions underlying the existing realization lemmas. No SGA route is used.

The Mathlib searches used LeanSearch, Loogle, LeanFinder with two different phrasings, and the required logged grep. They returned generic mate/counit identities, sheaf-module geometric compositors and module scalar counits, but not the item. I read `Mathlib/CategoryTheory/Adjunction/Mates.lean:84` (the mate equivalence), `:123` (counit transpose identity), `:170` and `:209` (the two pasting laws). These are available tools already represented in the DAG; deriving this item still requires the scalar/pullback composition comparison and the independently normalized geometric/scalar realization theorems. It is not a one-line specialization of any of those declarations. Searches of the whole DAG and blueprint (`scalar geometric exchange`, `mate`, `pasting`, `coefficient comparisons`) revealed no blueprint duplicate of the item. I reused the general normalization nodes instead of extracting the rectangle itself or its clauses as new nodes.

## Not duplicates

No new nodes were created. In particular neither the pullback square compatibility nor either counit calculation was made into a node: each follows by explicit composition/naturality from the cited statements. Existing narrower restriction-of-scalars and integral-quotient exchange results were not mistaken for this arbitrary scalar-extension assertion.

## Review by Q156

I checked all cited node files by reading their statements, not their proofs. For the item I read the main-20261015 refinement proof, part (2), where coefficient devissage of the closed-complement argument needs this compatibility, and the scalar-six pullback proof, part (1), which computes the balanced pullback comparison on K-flat complexes and asserts geometric composition compatibility. The formal calculation is my expansion of Stacks 07A7/0E47, whose proof is omitted, so `proof_origin.by` is `agent`.

Step 1 uses `def-weil-pbc-ambient-ringed-exchange` for precisely the mate of the pullback square; it does not cite a definition as an existence theorem. `lem-sfb-internal-section-scalar-adjunction` explicitly identifies the independently specified derived scalar adjunctions with no flatness assumption. `lem-pd-section-derived-pushpull-normalization` explicitly identifies the independently derived geometric adjunctions, their units and counits, and the geometric compositors, for an arbitrary scheme morphism. `lem-sfb-internal-scalar-pullback-normalization` explicitly identifies the actual internal balancing map with its section K-flat construction for any condensed coefficient homomorphism. Its symmetric convention for writing scalar tensor factors is identified by its own balanced-generator comparison; it is not a new choice of map. These are the exact ingredients needed to calculate in section modules. I avoided the more restrictive finite-type/positive-characteristic comparison lemma `lem-pd-module-ringed-topos-derived-comparison`.

Step 2 uses `lem-sfb-kflat-scalar-comparison-normalization`, whose statement gives both lambda as inverse of the scalar-adjunction mate and the canonical geometric composition law. Inverting that law for the two paths and inserting the two geometric compositors gives equation (*). `def-weil-pbc-ambient-ringed-exchange` specifies these square compositors. The two paths are identified by the chosen square; all rings and the coefficient homomorphism are pulled from the same point, so their path identifications agree. I checked that (*) starts at L_f'^B L_c^B T_Y and ends at T_X' L_a^A L_f^A. The order of the lambda factors is the inverse of the theta composition law, not that law with arrows left uninverted.

Step 3 uses `def-weil-pbc-adjunction-mate`, whose statement includes the actual counit transpose formula and its bijectivity, and the ambient exchange definition, which includes exactly its displayed counit transpose. Both formulas are definitions, and this step does not import a base-change isomorphism theorem. The target of both rectangle arrows is P_f'^B T_X' L_a^A J, so transposition along L_f'^B is defined. This and steps 4–5 are marked elementary because they are written-out substitutions of these formulas and naturality equations, with no separate geometric or homological fact hidden inside them.

Step 4 calculates the first inverse transpose. I checked separately the naturality equation for the f' counit at lambda_a, the square naturality at rho_f, the defining counit equation for rho_f, and lambda_a naturality at the A-coefficient f counit. This produces (L). The f-counit has domain L_f^A P_f^A J, not L_f^A J, which is why M is fixed as P_f^A J. The two cited definitions state the exact mate formulas consumed in this calculation.

Step 5 calculates the second inverse transpose. The f' scalar-mate equation contracts its B counit, lambda_f' naturality at Ex^A moves T_C(Ex^A), and the A exchange counit equation produces (R). Equation (*) then identifies (L) and (R). This is the complete comparison argument, not an unsupported assertion that the maps transport or commute. The mate definition supplies injectivity of the Hom bijection. No rho or exchange is inverted.

Step 6 checks the realization clause rather than forgetting it. The same three existing normalization statements from step 1 identify scalar extension, lambda, geometric adjunctions and all pullback compositors. Substitution into the mate counit word, followed by uniqueness of its adjunct (the cited mate statement), identifies the actual rho. Substitution into the unit-square-counit word (the cited ambient exchange statement) identifies the actual exchange. Faithfulness of an equivalence follows immediately by applying its quasi-inverse and conjugating with its unit, so the section equality gives the internal equality. No additional realization theorem is implicitly assumed.

All source and target categories are ordinary unbounded derived categories on sites small relative to modules. The scalar normalization and internal/section scalar comparison apply to arbitrary ring maps, including zero rings and nonflat quotient maps. The geometric comparison applies to arbitrary scheme morphisms. I tested the identity coefficient map, identity square, zero complex, zero ring and empty-site cases: the same identities hold and no faithfulness of a zero tensor functor is invoked. Nonflat A to A/I does not affect the argument, since scalar extension remains derived. Properness, finiteness, completeness and constructibility do not enter any step. The proof never relies on K-injectives being preserved by scalar extension. Each proof step is below 2000 characters; none hides a new standard lemma. The statement and its hypotheses are unchanged.

Against delivery-errors B–E: there are no new statement-only nodes to audit, no duplicated clause nodes or omitted searches; all proof citations have exact statement quotes in `citations.json`; all non-elementary inputs are named; no derived object is replaced by a per-degree claim; the calculation supplies the omitted mate verification; and no hypothesis from an unrelated coefficient layer or bounded category is used.

## Unfinished work

None within the one-level stage-1 split. The existing dependencies retain their independent proof status.
