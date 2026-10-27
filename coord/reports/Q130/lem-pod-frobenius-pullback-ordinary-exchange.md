# Q130: lem-pod-frobenius-pullback-ordinary-exchange

## Files written

- dag/nodes/sec-poincare-duality/lem-pod-frobenius-pullback-ordinary-exchange.json: statement, now split; no Mathlib match for the completed integral, raw rational and common-stage normalized assertion.
- citations.json: one verbatim statement passage for each of the 13 step citations.
- searches.jsonl: actual Mathlib searches performed through the required msearch command.
- report.md: this review.

New nodes: 0. New Mathlib leaves: 0. Existing statement and statement dependencies retained. The scratch generator write_split.py is sandbox-only and is not a delivery file.

## Attachments

None. I searched the project source both by the blueprint tag and by Frobenius pullback/exchange terminology. The definitions in WeilConjectures/SixFunctors/ProEtale/FieldCoefficient/GeometricFrobenius.lean, notably fieldUpperStarGeometricFiberMapCompFrobeniusIso and fieldLowerStarGeometricFiberMapCompFrobeniusIso, concern the underived field-sheaf operations and special geometric-fiber Frobenius squares. They do not supply this item's completed integral composition normalization and scalar-extension identities on the raw rational/common-stage constructible derived categories, for arbitrary commuting scheme automorphisms. They therefore do not attach the item.

## Literature and searches

WANTED: none.

I read prop-weil-operations.proof.md in the current main-20261015 blueprint and its cited lem-fix-weil-operations.proof.md in sec-six-functors/sk-rem-sf-pf-done. The first paragraph prescribes pullback commutation and ordinary automorphism-square exchange. I read Stacks sites-cohomology.tex, Tag 0D6D, lemma-derived-pullback-composition, including its K-flat proof, and proetale.tex, Tag 099N, lemma-pushforward-Noetherian-case, including completed pullback as derived inverse limit. The integral and scalar normalization statements already have DAG nodes; I use their statements, not a purported faithfulness of separate finite reductions. The detailed coefficient descent argument is marked agent-written rather than attributed verbatim to Stacks or the blueprint. No SGA source is used.

Actual searches are logged. Loogle SheafOfModules.pullbackComp and LeanSearch on completed constructible composition found ordinary module pullbacks; two LeanFinder phrasings also returned scheme module composition and unrelated ring/Galois maps. The grep found AlgebraicGeometry.Scheme.Modules.pullbackComp at Mathlib/AlgebraicGeometry/Modules/Sheaf.lean:241 and conjugateEquiv_pullbackComp_inv at line 265. I opened those declarations and the general SheafOfModules.pullbackComp at Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean:167 and its conjugation lemma at line 177. These are underived module categories and lack the completed constructible/common-stage normalization. They do not make this item a Mathlib leaf. Searches inherited in the live item are preserved as inherited; appended searches are exactly this worker's logged requests.

## What was wrong or incomplete

The item was statement-only, with no saved sandbox proof or report at continuation. The statement itself is consistent with the source's automorphism-square intent and has not been changed. The scalar equation needs the composition coherence of the specified integral maps; it cannot be justified by equality of separately evaluated finite reductions. Naturality at field stages needs arbitrary sums of pure tensors and arrows over larger common coefficient fields, not just integral lattice maps. Finally an invertible square transformation alone does not make its mate invertible; the horizontal equivalence hypotheses are used explicitly.

## Not duplicates

No new nodes were created. I searched the DAG and whole imported blueprint for pullback, mate and automorphism-square terminology, and read existing candidate statements. The proof reuses lem-pod-integral-pullback-composition, lem-pod-pullback-identities-scalar-extension, lem-pod-isomorphism-field-transport and the generic lem-weil-mate-iso-along-equivalences. No item clause has been repackaged as a new node. The scalar cancellation and common-stage representative computations are explicit elementary assembly steps from the cited comparisons and definitions.

## Review by Q130

I checked the node against the current blueprint source named above, the unit sk-lem-finite and the fixed chapter sec-poincare-duality. This node implements only the operation-lift sentence within that unit; it is not the unit key node, so I did not alter the unit's realization. The proof keeps the prescribed composition and automorphism-square route. No additional coefficient category or separatedness hypothesis on X and Y is introduced.

Step 1 uses the full statement of lem-pod-integral-pullback-composition for its actual natural compositor and its reduction formula, and lem-weil-pbc-proetale-derived-pullback-composition for the identified finite maps. I checked that both apply to morphisms of schemes rather than only k-morphisms. Since ell differs from the characteristic, their invertibility-of-ell hypothesis holds. The two compositor sources agree by fg_X=g_Yf. Their directions give a=D C^{-1}, from P_X Lf* to Lf* P_Y. This avoids reading more into a finite reduction than the cited statements assert.

Step 2 uses lem-pur-integral-operations-scalar-extension for the natural pullback scalar comparisons and their identity/tower coherence, and part (1) of lem-pod-pullback-identities-scalar-extension for the two precise composition equations. I read the whole normalization proviso in the latter: its maps are the specified whole-system maps, not arbitrary isomorphisms. The displayed cancellation gives B T(a)=a_L A in the stated direction. This is a short argument from those equations, so making another node for the scalar square would duplicate a clause of the item rather than help split it.

Step 3 uses def-weil-rationalization-karoubi only for its Hom tensor and scalar-extension definitions, and def-weil-derived-pullback-tensor-hom for the explicitly additive action on pure tensors. The proof writes the naturality equation term by term and sums it. I checked that it covers every localized arrow and respects balancing; it does not assume a single integral representative or use a rational reduction to torsion coefficients.

Step 4 uses def-weil-algebraically-closed-coefficients for the actual Hom-colimit equivalence relation and common-field composition, and def-weil-derived-pullback-tensor-hom for the conjugation formula on arrows. These nodes really state those formulas. The comparisons for the composites are exactly A and B from Step 2: substituting the two arrow formulas cancels the intermediate scalar identifications. The written common-field naturality equation uses Step 3 at stage L and Step 2 at both object fields. Extending farther preserves the equation by tower coherence, and equality of representatives means equality after a further extension by the cited definition. This establishes independence without any unsupported faithfulness or descent assertion.

Step 5 uses fix-prop-adjunctions part (1) for the supplied ordinary adjunction and def-exchange-projection for the three-factor formula and its higher-coefficient normalization. I read the definition's other-stage provisos: the item supplies these data and restricts to domains stable under the displayed composites. I do not claim those provisos prove global preservation or constructibility. The Cartesian universal-property calculation uses scheme inverses; it does not treat semilinear automorphisms as k-linear. For such semilinear squares one may twist source structural maps as in the parent node, but the formula itself is a formula on the underlying scheme operations, as the item prescribes.

Step 6 uses lem-pod-isomorphism-field-transport for exact equivalences with the specified inverse pullbacks, lem-weil-mate-iso-along-equivalences for invertibility of the displayed mate, and fix-prop-adjunctions part (1) for the two vertical adjunctions. I checked each substitution in the generic statement: G=P_Y is an equivalence, G'=P_X is fully faithful, and theta=a^{-1} has type L G to G' L. Its mate has precisely the item's type and formula. This generic result avoids the false principle that every mate of an isomorphism is invertible. The transport statement explicitly permits nonseparated finite-type schemes, so no separation of X or Y was silently used.

I tested the assembly at g_X=g_Y=id, f=id, zero inputs and the empty scheme: the formulas reduce to the supplied unit/composition comparisons and identities, never introduce division by an arrow that was not already an isomorphism, and preserve zero objects. At E=L the scalar comparisons specialize to their prescribed identities. For a tower E subset L subset M, the composites A,B use precisely the supplied cocycle, so the representative calculation gives the same equation directly at M. These checks found no statement dispute.

Against delivery-errors B--E, I checked self-contained existing hypotheses and TeX rendering, every cited statement rather than its proof, all non-elementary inputs, absence of any clause-only new node, and absence of circular dependence. A read-only traversal found no path back to this item from the generic mate, scalar identities, ordinary adjunction or field transport nodes. There are no new statements needing separate small-case tests. Every proof step is under 2000 characters; the longest is the explicit common-stage calculation. The off-unit cited results are declared in split_report.tool_uses as generic tools: finite derived pullback composition, integral scalar comparison, ordinary adjunction, and the abstract equivalence-square mate theorem. They do not replace a step of the unit's reference route. I corrected doubled TeX backslashes in the sandbox proof before final delivery checks.

## Unfinished work

None for this one-level split. Existing statement-only dependencies remain independent queued work; this delivery does not purport to prove them. The server review_split check passed before writing this report. The required final dry run and push follow this report.
