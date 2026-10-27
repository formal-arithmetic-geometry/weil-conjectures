# Stage-1 delivery: lem-sp-p1-ordered-projection-scalar-square

## Files written

- dag/nodes/sec-smooth-purity/lem-sp-p1-ordered-projection-scalar-square.json: existing statement, split in five steps; no exact Mathlib match.
- citations.json: 16 exact statement quotations, covering every step/node citation.
- report.md: this report. searches.jsonl records the actual searches; no new DAG nodes, no Mathlib leaves.

## Attachments

None. I searched lean/WeilConjectures by the item tag, ordered projection/scalar terminology and projection-map mate names. CategoryTheory.Adjunction.map_rightAdjointProjectionMap_comp_mateEquiv (ProjectionMapMate.lean:81) proves a general conditional categorical square, not this geometric statement with its specified scalar, inverse-image and twist comparisons. The pro-etale finite-free coefficient results in ProjectionExtendScalars.lean have different coefficient categories and extra hypotheses. They are not attachments for this item.

## WANTED

None. The current blueprint and required Stacks source are present.

## Problems and changes

The original statement is unchanged. Its proof was empty. The missing argument is the normalization of an existing general ringed-topos projection/exchange square, followed by the two explicit symmetries and the specified twist map. No claim that a same-source-and-target isomorphism suffices is used. The coefficient map is identified by equality of its adjunct with the general exchange adjunct.

No chapter or unit route changed: this is the Charts paragraph of det-sp-reduction-exceptional and step 2 of sk-lem-sp-reduction. This item is not the unit's key statement, so I did not alter the unit's realization fields. All maintainer-owned fields were retained. There is no statement dispute and no source error.

## Not duplicates

No new nodes were created. I searched the whole DAG and blueprint by ordered projection, projection scalar, tensor coherence, Tag 0E48 and the projection/coefficient keywords. The existing lem-weil-pbc-ringed-exchange-tensor-coherence supplies the unordered ringed square, and lem-sp-categorical-projection-mate-square supplies the general conditional categorical calculation. I reused the former. The latter does not itself discharge its tensor-normalization hypothesis. lem-kun-proj-formula-natural concerns constant coefficients and a cartesian scheme square; coefficient change is a square of ringed topoi instead. det-sp-p1-adjunction uses the ordered projection map in its adjunction formula but does not state its scalar square. The item therefore has no identical blueprint counterpart, and blueprint.same_as remains empty.

## Review by NG

I read the chapter and unit records, the three levels in SETUP.md, GOAL.md and delivery-errors.md B through E. For the source I read main-20261015 sk-lem-sp-reduction-exceptional.proof.md, especially Charts, and sites-cohomology.tex at equation-projection-formula-map (Tag 0B56) and remark-compatible-with-diagram (Tag 0E48). The latter omits verification: I did not treat that omission as a proof. I use the existing DAG theorem that states its general ringed-topos equality. The extra ordering and fixed twist substitutions below are written out by this worker, so proof_origin is agent.

For step 1 I opened the statements of def-weil-pbc-ringed-topos-morphism, lem-pur-derived-change-of-rings, lem-sfb-ringed-derived-monoidal-comparisons, def-weil-pbc-adjunction-mate and lem-sp-et-proet-coefficient-compatibility. The identity geometric morphisms with structural maps A_T to B_T satisfy the definition of ringed morphism. Both coefficient composites have the same structural homomorphism, since inverse image preserves the constant coefficient map. Horizontal derived pullback is K-flat scalar extension, not restriction of scalars. The monoidal-comparison statement includes composition and compatible 2-isomorphisms; these give the canonical comparison c in the needed direction. I compared the adjunct formula from the mate definition with the actual proper coefficient map's defining clause: both are T_P of the A-counit after c. Adjunction injectivity identifies beta itself. I use only that defining clause, not the coefficient theorem's compact-support isomorphism assertion or its pro-etale realization. Thus there is no unverified boundedness hypothesis introduced here.

For step 2 I opened the complete statement of lem-weil-pbc-ringed-exchange-tensor-coherence. It explicitly allows commutative ringed-topos squares without cartesianness, uses the canonical pullbacks/tensor maps and counit adjunctions, and equates the two displayed composites. Its generality includes constant-ring coefficient change. I read def-kun-projection-formula-map: its specified map has exactly counit-tensor-identity adjunct, identifying the theorem's vertical maps. I read def-pur-exceptional-coefficient-normalizations: it uniquely normalizes scalar tensor maps by ordinary balancing, so the horizontal maps are the item's m, with no arbitrary tensor comparison chosen. The new equality is the direct specialization with E and K, with d spelling out the target comparison. No new lemma is hidden in this step.

For step 3 the monoidal-comparison statement explicitly includes symmetry and its Koszul sign. I checked both displayed symmetry equations with their source and target objects, and the direction c inverse. Precomposition on the source and postcomposition on the target, followed by naturality of the beta transformation and tensor symmetry, gives the ordered equality written there. I added the coefficient node to this step's uses to cover its naturality clause. This step is elementary substitution from cited identities: it asserts no new monoidal compatibility theorem. The notation o_R is separately defined at each coefficient ring.

For step 4 I expanded the ordered map using def-kun-projection-formula-map. Naturality in its first argument follows directly from counit naturality and naturality of its tensor comparison, then the two tensor symmetries of the monoidal-comparison node. I wrote the resulting formula for an arbitrary u, and inserted the actual u=lambda. The left composite is exactly the specified a_K and the right composite is exactly b, so functoriality gives the item. I do not replace lambda by an unspecified rank-one trivialization. I read lem-asd-finite-etale-twist-line as well: N is invertible because ell differs from the field characteristic, and its conclusion gives local rank-one flatness for the ordinary twist. The step only uses the fixed shifted lambda already in the item's statement; the same argument works for any given morphism of this type and hence adds no twist-existence theorem.

For step 5 I checked the naturality statements in the projection definition, coefficient node and monoidal-comparison node. The proof is in ambient unbounded ordinary etale module categories, so restriction to the stipulated bounded constructible finite-Tor K does not require a new preservation or isomorphism claim. In particular I did not apply a bounded-below restriction comparison or forget a B-action. No finite free resolution of B is truncated, and no flatness or finite projective dimension of B is needed.

I checked small cases: K=0 and B=0 give zero maps; A=B with the identity homomorphism reduces to ordinary functoriality and the two inverse symmetries; N=1 forces the allowed coefficient rings to be zero; the empty base gives the trivial category. A nonflat map Z/ell^2 to Z/ell uses the same K-flat extension functors and the same mate formula, with no step requiring it to be flat. The even shift [2] is already part of L_R; all swaps use the full derived symmetry, so no degree sign is discarded.

Against B1-B10: there are no new nodes, no unstated new notions, no invented Mathlib leaf or attachment; searches are the actual logged commands, with inherited searches preserved. The relevant Mathlib hits concern abstract monoidal adjunctions, ordinary scalar extension or cartesian-closed Frobenius maps. I inspected the Frobenius candidate in Mathlib/CategoryTheory/Monoidal/Closed/Functor.lean:139; it concerns cartesian-closed categories and is not the stated etale coefficient square. A second LeanFinder phrasing and grep were recorded. Against C1-C8: each non-elementary input is an existing cited statement, every citation was opened, off-unit generic tools are declared in split_report.tool_uses, and the transitive dependency search found no path back to this item. citations.json uses verbatim substrings, including the composition/2-isomorphism clause actually used in step 1. Against D1-D5: the split creates no restatement node and explicitly supplies the ordered/twist part of the calculation after applying the existing general theorem. Against E1-E7: I checked coefficient actions, comparison directions, arbitrary square versus cartesian-square requirements, twist shift and the nonflat case; no hypothesis was added or dropped. No step exceeds 2000 characters (each is under 1300), and none contains an independent undeclared lemma.

## Unfinished work

None in stage 1. This delivery contains no Lean edits and runs no compiler or build tool.

## Validation

The server review_split check passed with zero new nodes. The required full delivery dry run and push are the next validation steps.
