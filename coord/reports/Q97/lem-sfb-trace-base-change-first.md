# Worker report: lem-sfb-trace-base-change-first

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-trace-base-change-first.json`: statement node, now split into seven steps; no exact Mathlib match. Its statement and statement dependencies are unchanged.
- No new DAG nodes, Mathlib leaves, unit records, Lean files, or live files.
- Sandbox evidence: `citations.json` contains exact excerpts for every proof citation; `searches.jsonl` is the search command's log.

## Attachments

None. I searched the project source under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the exact item id, trace/base-change combinations, first-triangle names, and projection/trace combinations. The hits concern the general trace-formula pairing or an adic TODO, not this identity with both projections and its prescribed canonical maps. There is no attachment candidate supplying the complete item.

## WANTED

None. All sources used are available in the shared repository.

## Findings and corrections

The item was unsplit and had no proof or local prior attempt. I retained the statement, source, blueprint ancestry and earlier search records. I supplied the formal calculation hidden in the blueprint's instruction to reassociate direct images and move the coefficient outside. The proof is marked agent-written because the blueprint recalls only the shape of this calculation; the explicit two transpose computations are written here from the cited adjunction formulas.

No statement dispute or hypothesis repair was necessary. The first identity only needs the stipulated trace relation for p_1; the symmetric p_2 trace relation is harmless additional context already in the item. The proof never assumes the adjunction Rf_* left adjoint to f^*(-) tensor T that the parent is constructing. It uses only the pre-existing inverse-image/direct-image adjunctions.

I initially searched broad DAG titles for projection/trace compatibility and found the existing general ringed-topos normalization nodes. They give the right coefficient category. In particular, I did not use `prop-sf-pf-coherence`, which is formulated for a full six-functor datum, or finite-coefficient/tower-only exchange theorems as if they were statements about the ordinary derived category of pulled-back condensed modules.

## Not duplicates

No new nodes. Existing `lem-sfb-ringed-derived-monoidal-comparisons`, `lem-weil-pbc-adjunct-counit-identity`, `lem-sfb-ringed-projection-tensor-composition`, and `lem-weil-pbc-ringed-projection-mate-exact` are cited directly. The two explicit transpose calculations are steps, not fresh nodes restating clauses of this item. Whole-blueprint searches for `projection`, `counit`, `trace-base-change`, and `first triangle`, together with whole-DAG title and statement searches, found no blueprint statement of this exact trace rearrangement. `blueprint.same_as` remains empty; the ancestor check gives `det-thm-int-restriction-line`.

## Mathlib searches

All five new searches were run through `msearch.py Q97 lem-sfb-trace-base-change-first` and their exact tool/query text and results are appended to the item. Loogle's projection/counit query and the CategoryTheory grep returned no hits. The first LeanFinder wording returned probability-integral facts. A second wording about symmetric monoidal external products and Beck--Chevalley mates returned rigid dual-mate formulas and `CategoryTheory.frobeniusMorphism_mate` for Cartesian monoidal categories, whose types do not state this ordinary derived module identity. LeanSearch returned ordinary counit naturality and generic derived/localized-adjunction constructions. These are building blocks, not an exact statement or one-line specialization of the whole item. No unavailable service was recorded as a negative result.

## Review by Q97

I read the chapter record `sec-six-functors-basics`, the unit record `sk-thm-int-restriction`, the current main-20261015 `sk-thm-int-restriction-line.proof.md` (1), and `sk-prop-p1-adjunction-rational-triangle.proof.md`, first identity. The former explicitly reuses the latter's projection/base-change/direct-image calculation over O_E; the delivered argument expands that first-identity rearrangement without changing the route or using a purity or SGA trace theorem.

For the actual formulas I read Stacks `sites-cohomology.tex`: 07A7 (`remark-base-change`), 0B56 (`equation-projection-formula-map`), 07A4 (`lemma-pullback-tensor-product`), 07A6 (`lemma-adjoint`), 0D6E (`lemma-derived-pushforward-composition`), and the comparison discussion including 0FPI (`lemma-adjoints-push-pull-compatibility`). I also read `categories.tex`, 0037 (`definition-adjoint` and the following three equivalent transpose formulas) and 0DV0 (`lemma-compose-counits`). The comparisons' full tensor and adjunction normalization is taken from the existing cited DAG statements, not claimed to be an extra assertion of 0FPI alone. I read those statements in full.

Step 1 uses `sk-def-sfb-module-derived-pushpull` for deriving the whole module functors, `def-sfb-module-derived-pushpull-adjunction` for their adjunction, and `sk-prop-sfb-cartesian-coefficients` for the actual coefficient-ring isomorphism and exactness. These state precisely the identifications required: the coefficient sheaf is O_{E,Z}, not a discrete constant O_E and not a tower category. `lem-sfb-ringed-derived-monoidal-comparisons` explicitly says pullback is symmetric strong monoidal, composition comparisons preserve adjunctions, and an isomorphism of ringed morphisms induces the corresponding normalized comparison. It therefore identifies PQ_1 and PQ_2 and their transpose bijections through h=fp_1=fp_2. The small site representatives are within the standing size convention; its theorem permits arbitrary commutative sheaves of rings and unbounded complexes, so adds no flatness or boundedness hypothesis here.

Step 2 only introduces two composites using the defined projection maps and the assumed base-change maps. Its citation to `lem-sfb-ringed-derived-monoidal-comparisons` supplies symmetry compatibility when reversing the projection-map factor order. I checked every intermediate object in both lines. The equality P(B_N)D_2=pi_{f,A,T} is cancellation of the displayed definition of B_N. D_2 is invertible using exactly the item's assumed invertibility of B_N and pi_{f,A,T}. In particular lambda_{f;N,C}, introduced for comparison, need not be invertible. No stronger projection-formula assumption has slipped into the proof.

Step 3 uses the composite-adjunction clause of `lem-sfb-ringed-derived-monoidal-comparisons` and the equation c L(psi)=phi in `lem-weil-pbc-adjunct-counit-identity`. I computed the transpose of D_2 explicitly, in the order F then U_2. `def-weil-pbc-adjunction-mate` states the transpose of the square mate is the pulled-back original counit. Here it gives c_{p_2,U_1N} U_2(b_{2,N})=U_1(c_{f,N}). Substituting leaves U_1(c_{f,N}) tensor U_2(c_{f,T}), with target U_1N tensor U_2T. This uses the cited node's statement, not something in its proof.

Step 4 applies exactly those same three cited statements with the other factorization. The explicit expression now contains c_{p_1,T_W} U_1(b_{1,T}), which the mate statement identifies with U_2(c_{f,T}). The remaining factor is U_1(c_{f,N}). Both transposes have the same source h^*(A tensor C) under the monoidal composite comparisons. The common hom bijection is injective, giving D_1=D_2. The tensor bifunctor interchange at the end of each computation is an elementary composition rule; no separate Fubini theorem or unstated Kunneth comparison is assumed.

Step 5 is the literal cancellation of pi^{-1} in e_A after step 2; it cites no theorem. Step 6 first cancels the displayed p_1 projection inverse and substitutes precisely the hypothesis t_1 b_{1,T}=F(t). `lem-sfb-ringed-projection-tensor-composition` states naturality in both inputs, so it moves the scalar morphism t:C to R_Y across lambda_{f;N,C}. `lem-weil-pbc-ringed-projection-mate-exact` explicitly normalizes that projection at the tensor unit to the identity. Both theorems are for ordinary unbounded ringed-topos module derived categories; they apply without identifying different coefficient layers. Step 7 is cancellation of the already proved isomorphism D_2. Each citation has a verbatim statement excerpt in `citations.json`.

I checked the B--E return checklist against these files. There are no new unsplit statements, unintroduced new notions, fabricated search records, changed sources, duplicate ids, hidden clause nodes, or new source hypotheses. I checked that the proof dependency list is exactly the union of the step citations. The four generic tool statements used outside the unit are declared individually in `split_report.tool_uses`; they supply formal adjunction/tensor rules, not a replacement for a unit step. The largest proof step is 1083 characters; none exceeds 2000 or hides an independent comparison theorem. The only comparison computed here has its two transposes fully displayed in steps 3 and 4.

For edge cases I checked f=id: the b_i and comparison maps become identities, and both asserted maps become 1_N tensor t. For N=0 and for X empty every relevant map is the unique zero map; the proof uses no nonemptiness or nonzero-object assumption. On a finite disjoint union of copies of Y, D_1 and D_2 both place an N component from the first factor and a T component from the second in the same (x_1,x_2) summand; this checks that the indices of b_1, b_2 and t_1 were not swapped. With t=0 the two sides vanish, including in the shifted Tate setting. For complexes in arbitrary degrees the cited symmetric monoidal comparisons retain the Koszul symmetry; both transpose expressions keep the final N,T factor order, so no sign is discarded. Nothing requires N to be bounded, flat, perfect, or supported on the diagonal. I made no statement change and did not edit a target, chapter or unit.

The preliminary server `review_split` check returned PASS with zero new nodes. The first full dry run required longer citation excerpts for the derived adjunction and adjunct-counit formula. I replaced those three excerpts with the complete cited statements, retaining the same proof and dependency list. A subsequent preflight rejected the possessive wording in step 2 as an external-setting reference; I replaced it by an explicit reference to the projection map defined in this statement. No mathematical content changed. The final dry run and direct delivery are performed by the required delivery command after these repairs.

## Unfinished work

None within this one-level split. Existing dependency nodes retain their own independent proof obligations. The maintainer's independent review is still required by the delivery workflow.
