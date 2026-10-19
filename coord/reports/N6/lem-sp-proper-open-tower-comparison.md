## Files written

- `dag/nodes/sec-smooth-purity/lem-sp-proper-open-tower-comparison.json`: statement, split in five steps; no Mathlib match. The statement is unchanged.
- `citations.json`: a verbatim statement excerpt for every citation in the five steps.
- No new node files or Mathlib leaves. `searches.jsonl` is the log produced by the required search command. `write_split.py` is sandbox-only scratch work.

## Attachments

None. I searched the item id and its blueprint tag, proper/open/tower terminology, and proper-open/interchange declaration names in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/`. The existing file `SixFunctors/Etale/Derived/OpenImmersionLowerShriekLowerStarExchange.lean` constructs an unbounded *etale Cartesian* comparison and proves its torsion invertibility. It does not state the non-Cartesian constant-A pro-etale strict-tower theorem, its open-restriction definition, or its finite evaluation normalization. It is not an attachment for this item. No master sorry declaration is used as a finished proof.

## WANTED

None. The additional open-adjunction identification is an agent argument with the generic inputs already present as DAG nodes; it is not attributed to a nonexistent strict-tower theorem in Stacks.

## Findings and changes

The imported statement is consistent with the sources' intent, but its strict-diagram enhancement is additional mathematics, as its source field already says. Stacks 0F7B (`lemma-shriek-proper-and-open`) concerns etale sheaves and separated locally quasi-finite horizontal maps, allowing non-Cartesian squares. Its finite-ring case applies here at each etale level. Stacks 0F7F is the base-change compatibility statement; it is not needed anew to construct lambda. Stacks 0941 (`lemma-derived-limit-is-ok`) compares two derived inverse limits; it is not itself a strict proper/open theorem. The split makes no inverse-limit claim and does not misuse that tag.

The whole-DAG search found the existing `lem-cbc-strict-tower-proper-open-calculus` and its normalized operation definitions. That statement is strictly more general on coefficient rings and supplies precisely the finite-origin isomorphism and finite evaluation normalization. Its dependency closure does not reach this item. Rather than create a duplicate or a child restating the conclusion, I reused it and supplied the remaining identification of its proper-adjunction mate with the item's open-adjunction prescription. The decisive formula is

`lambda G_i gamma = R_q J_s epsilon_r . R_q pi_s G_q R_r . eta_q R_r = R_r epsilon_r . eta_r R_r = 1`.

Here the clopen direct-image identification makes `pi_s = eta_s`, so the middle equality is exactly the composite-unit formula. This is equality in the derived tower category before evaluation. The proof does not assert that evaluation is faithful on derived maps.

I searched the whole blueprint with `blueprint_refs.py search` for `proper open interchange tower`, `proper-open`, `clopen`, and `open restriction`, and searched DAG files for the item, proper/open terminology, and Tags 0F7B/0F7F/0941. The blueprint proper/open comparisons are finite etale or special refinement-square statements; none states the present strict-tower open-adjunction normalization. Thus `same_as` remains empty and ancestry is retained at `fix-lem-exchanges`, Proof Steps 3 and 5. The item is not the unit's key statement, and the unit's realized fields are untouched.

The six additional Mathlib searches were all run with the mandated `msearch.py N6 lem-sp-proper-open-tower-comparison ...` command and copied from its log. Both semantic phrasings, Loogle, LeanSearch, and both grep patterns returned no statement of this item. I read the returned signatures and the module-sheaf pullback/restriction source; the hits give ordinary sheaf pullback/direct-image adjunctions, structure sheaves on schemes, condensed colimits, and scalar towers. They do not give derived strict-tower proper/open interchange or the finite normalization. Every service in these six attempts was available. The inherited earlier searches were preserved.

## Not duplicates

No new nodes. Existing generic inputs are cited directly. In particular `lem-weil-pbc-derived-open-restriction` and `lem-weil-pbc-clopen-section-direct-image` were inspected but deliberately not used for the tower argument: their statements only cover finite-ring bounded-below etale complexes. Instead step 3 derives the required unbounded diagram-site restriction from the general ringed-site localization and K-injective statements.

## Review by N6

I read the chapter and unit records, the blueprint `fix-lem-exchanges` proof, Stacks `more-etale.tex` 0F7B and 0F7F, `proetale.tex` 09AE, `sites-modules.tex` extension-by-zero construction and exactness (03DH/03DJ) and ringed localization 04J0, `derived.tex` 08BJ, `sites-cohomology.tex` 0D6E and 0941, and `categories.tex` 0DV0. The item follows the compact-support unit's proper/open route; no chapter or unit route is replaced. There are no new nodes requiring independent source validation.

Step 1 uses the weakly-etale localization statement's constant-ring identification and unique-factorization clause, and the module restriction/extension statement's explicit presheaf and exact adjunction. The normalized tower-open definition says these operations act termwise and descend to the derived categories. Thus the given sheafified presheaf really is that operation. The Noetherian-open statement says any open subscheme of a Noetherian scheme is quasi-compact; applying it to each inverse image of an affine open checks the calculus's quasi-compact-open hypothesis. Finally the calculus statement itself supplies the clopen lift and its specified proper mate. I did not cite an open-section lemma for this general square: the map r need not be an identity.

Step 2 uses only the stated clopen decomposition/projection in the calculus, localized pro-etale sites, the module adjunction, normalized open composition, and exact-functor derived descent. Its extra argument is written out: disjoint-open sheaf gluing identifies modules with pairs, and extension/direct image of the clopen summand are both `(F,0)`. It follows that direct image there is exact and its unit is the projection. This applies simultaneously to all strict transitions, with no finite-ring or boundedness assumption. It does not use a definition node as evidence for an unrelated geometric theorem.

Step 3 uses the diagram-site realization exactly as stated: the index is the small opposite natural-number poset, so its module category is a genuine small-site module category in the chosen universe. K-injective existence therefore applies. The localization statement gives `j_V^* f_* = (f_V)_* j_U^*` with its sectionwise identity, including ring actions. The right-adjoint-preserves-K-injectives statement applies because restriction is right adjoint to *exact* extension by zero, not merely because restriction is exact. K-injective computation then gives the two sides of chi on the same representative. The composition theorem is unbounded and for ringed topoi, so it legitimately gives Rq Rs = Rr on the diagram sites. The mate definition fixes its base-change direction. This repairs the possible temptation to cite the etale bounded-below open-restriction lemma beyond its hypotheses.

Step 4 is an explicit adjunction calculation from the cited formulas. The calculus states both the open-unit definition of beta and the proper-mate formula for gamma. The general mate node provides that formula as a bijection; the composite-adjunction node provides the composite unit. The localization node's sectionwise identity ensures the restricted unit has the q-adjunction normalization, not an unspecified isomorphism. The clopen projection from step 2 is eta_s, so the displayed composite is the r triangle identity. This proves equality of the specified maps before any evaluation. The step is marked non-elementary because it uses the full mate and composite-adjunction calculation, even though each displayed cancellation is formal.

Step 5 uses the calculus statement's clauses on scalar etale-origin inputs, no uniform lower bound, and equality of each evaluated map with the normalized finite comparison. I opened the finite proper/open coherence node: it states exactly the arrow i_! Rr_* -> Rp_* k_!, its K-injective normalization, and that no Cartesian hypothesis is imposed. Here A is commutative, each quotient is finite and commutative, and every L_n is in D^+; these are precisely the hypotheses of those clauses. No transition maps between etale witnesses are needed or manufactured. The original Noetherian coefficient assumption is retained even though the calculus works more generally.

For delivery-errors B, there are no new statements, no hidden new proof sketches, and no new notions left unintroduced. For C, I read the statement of every cited node and copied the actual used part into citations.json; the finite-etale restriction lemmas were excluded where their statements were too narrow. All non-elementary facts in the steps have the cited general inputs, and the calculus is already present, not a new conclusion-shaped child. Generic off-unit tools are declared with their purpose in split_report.tool_uses. For D, the original work here is the lambda construction and its mate-identification calculation; the existing broader theorem is reused rather than re-created. For E, I checked the coefficient categories and scalar restriction, actual fibre product, proper/non-Cartesian hypotheses, quasi-compact opens, smallness, and unboundedness separately.

The small cases checked are the empty upper-left scheme (the clopen summand and both relevant functors are zero), a Cartesian square (s is the identity and pi_s = 1), a square with r = identity (s is a clopen section), identity horizontal maps (ordinary direct image), and a disjoint union S = U disjoint-union S' with nonempty complement (pi_s must project rather than be an isomorphism on all modules). The zero coefficient ring and zero input also give the zero-category/zero-object comparison. These checks do not require a uniform lower bound across n. I found no false statement requiring STATEMENT-DISPUTED, and made no statement change.

## Unfinished work

None for this one-level split. No push or delivery is authorized for this first reader. The independent second reader must review the accepted sandbox and deliver it.

## Second reading by N6

- Step 1: checked against Stacks 0F7B/0F7F and the cited localization, open-extension, Noetherian-open, and strict-tower calculus statements; all coefficient, openness, properness, and quasi-compactness hypotheses match, and the constructed $S,b,q,s$ and mate are stated by the cited calculus.
- Step 2: checked against the clopen clause of `lem-cbc-strict-tower-proper-open-calculus`, localized-site module adjunction, and exact-functor descent; the product decomposition gives the projection and exact direct image on every tower, including the empty complement case.
- Step 3: checked against the diagram-site realization, K-injective existence/preservation, ringed-site localization identity, and derived composition statements; both sides use the same restricted K-injective representative, so the displayed $\lambda_Q$ is an actual unbounded derived transformation.
- Step 4: checked the mate formula, localization normalization, composite-unit formula, and triangle identity line by line; the calculation is valid before evaluation and is marked non-elementary because it is a multi-stage mate computation.
- Step 5: checked against the strict-tower finite-origin/evaluation clause and finite proper/open coherence node; each $P_n$ is finite commutative, each $L_n$ is bounded below with no uniform bound required, and the direction and normalization of evaluation agree.
- New nodes: none; there are no new statements or Mathlib leaves to review.

Changes made in this second reading: changed step 4's `elementary` flag to `false`, because its full mate calculation exceeds the two- or three-line elementary criterion; corrected the corresponding review prose and expanded the typed localization-unit equation and beta cancellation. No statement, hypothesis, dependency, citation, or source field required repair. Rechecked all 24 citation pairs as verbatim excerpts, all cited nodes as existing and semantically sufficient, and the small cases (zero/empty schemes, field coefficients, identity/cartesian square, and nontrivial clopen complement). Final dry-run and delivery results are recorded in second-reading-dry-run.log and second-reading-delivery.log.
