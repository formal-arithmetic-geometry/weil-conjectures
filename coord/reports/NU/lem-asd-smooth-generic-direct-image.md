# Worker report: lem-asd-smooth-generic-direct-image

## Files written

- dag/nodes/sec-smooth-purity/lem-asd-smooth-generic-direct-image.json — statement, split; no whole-item Mathlib match.
- citations.json — verbatim cited statements for every step citation.
- report.md — this report. No new nodes and no Mathlib leaves.

## Attachments

None. Searches by the exact blueprint id and by smooth/generic/direct-image notions under WeilConjectures in slopmaster2 found no project declaration giving both clauses with the item's hypotheses. Upstream master was reference material only; no sorry declaration was treated as a proof.

## Wanted literature

None for this split. The item's actual proof source is the agent-written master blueprint at literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-cbc/lem-asd-smooth-generic-direct-image.md, not an attributed Stacks proof. The relative-dimension input is Stacks Tag 02G1, morphisms-lemma-smooth-omega-finite-locally-free, read in morphisms.tex. The general Noetherian input is the existing 01T6 node. The tensor/Hom constructions use the general ringed-site internal Hom node (08J7, 0A95), not the now pro-etale-only def-weil-derived-pullback-tensor-hom.

## Corrections to the imported proof

The statement is unchanged. The relative dimension is locally constant on X; its finite open-and-closed decomposition is on X, not S. Step 1 explicitly uses this source decomposition, and step 6 proves recombination by finite products. The original proof's final step cited only the dual lemma while also taking smooth and compact-support base change and internal adjunction: all these citations now occur at their use. The final morphism identification is expanded as an equality of ordinary-adjunction transposes. No claim is made that finite type over k is preserved for the arbitrary Noetherian test base T. Compactifiability of the base change follows from base changing the chosen compactification.

No new unsplit lemma packages a clause of the item. No proof depends on the six-functor constructible package, so the argument does not presume ordinary direct-image finiteness. The ordinary etale coefficient category is kept throughout; the pro-etale/adic definition node with a similar name is deliberately not used as an etale operations theorem. Generic lissity is derived from the definition of a finite constructible stratification, rather than introduced as a restatement node.

## Not duplicates

No new nodes. Whole-DAG searches for evaluation/duality and whole-blueprint searches for smooth generic and locally constant cohomology found the already cited lem-fin-lisse-field-dual; it is a tool for internal duals, not the generic direct-image lemma itself.

## Review by NU

I read the entire item's master blueprint proof, its unit sk-prop-sf-cbc and chapter sec-smooth-purity. The unit's finite-stage etale typing permits this F_ell argument; its other adic stages are not invoked. This item is not the unit's key statement, so no unit record was changed. I read the complete statements of each cited node and included those statements verbatim in citations.json. The mathematical checks were as follows.

Step 1 uses pqf-lem-locnoeth-lft precisely for locally Noetherian bases and locally finite type morphisms, successively from Spec k to S to X, with quasi-compactness to obtain Noetherian schemes. The 02G1 node states local constancy on X, exactly where the level sets are formed; I checked the original Stacks formula rank Omega = fibre dimension. Nagata's existing statement applies because S is quasi-compact and quasi-separated. Finiteness of the dimension image follows from its open-level-set cover and quasi-compactness, not from a nonexistent dimension bound on S. Restricting to a clopen source piece preserves the hypotheses for the ambient smooth theorem.

Step 2 uses thm-asd-smooth-tensor only for its rank-one shifted sheaf conclusion, with compactifiability supplied in step 1 and Noetherian base checked there. I checked the shift sign: omega is P[2d], in cohomological degree -2d; the shifts cancel in RHom(N,omega). The finite-free calculation gives L = L double dual in degree zero without a global Ext-vanishing assertion. The geometric-stalk criterion cited is a sheaf criterion; it is applied to cohomology sheaves, not asserted as a derived theorem. The constructibility definition supplies bounded constructible terminology. The internal-Hom definition is general for a small ringed site, so it applies to ordinary etale lambda_X; no inference from pro-etale categories is made.

Step 3 uses internal ambient adjunction with precisely N and lambda_S, and compact finiteness with X and S finite type over k and ell invertible. The finite stratification definition really supplies locally closed strata with finite locally constant restrictions. On an integral scheme the closed part of the stratum containing the generic point is all S, which proves the required open neighborhood. There are only finitely many degrees; the intersection contains the generic point. Compact exchange includes restriction to an open, so the argument uses the actual compact image for f_U. The lisse-field-dual statement gives the displayed cohomology formula and pullback comparison; vanishing outside finitely many degrees follows from that formula.

Step 4 uses prop-asd-smooth-base-change at K=lambda to identify omega and its tensor structure, compact exchange for a Noetherian T, the lisse dual pullback comparison, and ambient internal adjunction for f_T. I checked that T need not be finite type over k: it is not used to apply the finiteness part of the compact lemma anew. Only its already stated arbitrary-Noetherian exchange clause is used. X_T is Noetherian since f_T is finite type over Noetherian T. The base-changed compactification supplies a proper map and an open immersion, so ambient adjunction's compactifiability hypothesis holds. Finite free sheaves remain finite free under inverse image.

Step 5 compares the maps rather than their isomorphism classes. I expanded the test to the ordinary-adjunction transpose f_T^*v^*Rf_*L -> v_X^*L. The internal pairing is evaluation after the ordinary counit; compact exchange substitutes the compact image and the smooth exceptional comparison is defined by transposing the pulled-back exceptional counit. These substitutions leave the pulled-back ordinary counit v_X^*e. The base-change definition's inverse-image transpose is exactly that formula on the exchanged square, so uniqueness in adjunction identifies the resulting morphism. This is a calculation of the canonical constructions, not an appeal to a node's unrecorded constructible-preservation theorem. Every non-elementary isomorphism used in it has the corresponding node cited again.

Step 6 is elementary recombination: the sheaf condition on a finite clopen cover gives tuples, hence a finite product of section functors. Finite products in an abelian category are exact finite sums, and common finite cohomological bounds and trivializing covers yield the result. This step does not introduce a general disjoint-union theorem as a new node. I checked the empty source (zero complex, U=S), relative dimension zero, L=0, varying dimensions on disjoint source components, the case S is a point, and test bases with nonreduced structure. No new statement needed small-case testing; the original statement passed these checks.

I checked B through E: all node notions used by the statement are named; no new node exists to violate statement-only or duplicate rules; all step uses have matching statements; no imported tag is left standing for an uncited theorem; dependencies are the union of actual uses; the argument follows the source route with the above corrections. Off-unit citations are recorded as generic tools in split_report.tool_uses, not as replacements for a unit step. No Lean file or compiler was used. Nothing remains mathematically unfinished at this one-level split; cited unsplit nodes retain their independent work.

## Dry run

Second-reader dry run: deliver.py --no-push printed OK at 7268481431; preflight passed. No compiler or Lake was run.

## Second reading by NU

- Item statement: compared every hypothesis and both conclusions with master blueprint lem-asd-smooth-generic-direct-image, order 1632; agrees. Integral means nonempty; coefficients are ordinary etale F_ell, and L is on X. No statement dispute.
- Step 1: read Morphisms Tag 01T6, lemma-finite-type-noetherian, and Tag 02G1, lemma-smooth-omega-finite-locally-free, against the two cited nodes; Noetherianity and dimension level sets are valid. Nagata applies to the Noetherian base. Finite-type composition over k follows affine-locally by adjoining the two finite sets of algebra generators.
- Step 2: checked thm-asd-smooth-tensor and def-pur-derived-internal-hom statements; shift cancellation and finite-free biduality are valid. The stalk criterion applies to cohomology sheaves. Zero L, d=0 and d=1 give the claimed evaluation.
- Step 3: checked prop-asd-internal-adjunction, lem-fin-compact-bounded-and-base-change, constructibility definition and lem-fin-lisse-field-dual statements; all hypotheses hold. On reduced integral S the generic locally closed stratum is an open subscheme, so the sheaf restriction, not just its underlying set, is lisse. If C=0 choose U=S.
- Step 4: checked prop-asd-smooth-base-change at lambda, compact exchange on the finite-type original base and lisse-dual exchange for any morphism. Added explicit citations for separated finite-type base change, Noetherianity of X_T and compactification base change. Checked that ell is invertible on arbitrary T, including nonreduced T; no finite-type-over-k assumption on T is used.
- Step 5: checked the canonical morphisms in the internal-adjunction and smooth-comparison statements and sbc-def-base-change-map's inverse-image transpose. Wrote the exceptional-counit mate equation and compact-exchange naturality equation; substitution proves the equality of pairings, hence the ordinary-counit transpose. This uses defining canonical maps, not an extra theorem hidden in a cited proof.
- Step 6: checked the finite clopen sheaf cover, exactness of finite products and common cohomological bounds. The component equivalence of sheaf categories takes injectives to componentwise injectives, so deriving gives the stated finite product of direct images. Empty X gives zero and U=S; S a field and components of different dimensions cause no exception.
- New nodes: none. B1-B7 and duplicate/new-node Mathlib checks are vacuous. Independently searched Mathlib with msearch.py grep for higherDirectImage, higher_direct_image, genericBaseChange and generic_base_change: zero hits. Read-only slopmaster2 searches by the item id and smooth/generic/direct-image terminology gave no attachment; upstream master is not a proof.

Changes: step 4 now cites the existing Mathlib leaf lem-pod-separated-finite-type-base-change and existing closed node lemma-nagata-compactification-base-change, and re-cites pqf-lem-locnoeth-lft where used. Step 5 now states the defining counit and exchange equations explicitly, removing an implicit compatibility argument. Rebuilt citations.json from the actual cited statements; no new node or coefficient-category identification was introduced. The first worker's Review by NU is preserved.

Additional source check: step 4's existing base-change leaf agrees with Morphisms Tag 01T4, lemma-base-change-finite-type, and Schemes Tag 01KU, lemma-separated-permanence, clause (3). The compactification construction was read in def-nagata-compactification-base-change; slopmaster2 Compactification/BaseChange.lean lines 198-204 explicitly constructs HasCompactification.of_isPullback from the base-changed compactification. These are existing dependencies, not new leaves or attachments.
