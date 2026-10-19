# Stage-1 worker report: lem-sfb-trace-base-change-second

Group Q115, direct delivery, 2026-10-18.

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-trace-base-change-second.json`: item, statement, split in six steps; no Mathlib match found.
- `citations.json`: thirteen literal statement excerpts, one for every node used by every step.
- `report.md`: this report.

No new nodes; zero Mathlib leaves. `write_split.py` is a sandbox-only reproduction aid, and `searches.jsonl` is the search command's own log; neither is a proposed DAG file.

## Attachments

None. Searched the read-only slopmaster2 `WeilConjectures/` tree for the exact blueprint tag and for trace/base-change and second-triangle terminology. There is no declaration of this identity. Read `SixFunctors/Etale/Derived/LowerStarProjectionBaseChange.lean`, especially `rightDerivedLowerStarProjectionMap_derivedBaseChangeMap`, and `CategoryTheory/Adjunction/ProjectionMapMate.lean`, especially `map_rightAdjointProjectionMap_comp_mateEquiv`. These are general comparison ingredients, rather than this integral module-object trace equality. They do not justify attaching the item. Also checked the exact tag in the read-only upstream master reference; it is absent. No upstream sorry is treated as a finished proof.

## WANTED

None for this split. The current blueprint and the relevant Stacks source are available locally. No SGA source was used.

## What changed and why

The imported item had a complete statement but no proof. The source blueprint's integral line argument refers to the rational second-triangle calculation, which says that the outside factor is moved by the projection formula. I expanded that rearrangement at the level of the canonical maps. Base-change/projection coherence identifies the pulled-back inverse projection map; the supplied trace equation replaces the pulled-back trace; the tensor-action identity compares successive and combined projections; and symmetry naturality finishes the equality.

There is a meaningful sign issue: the two copies of the shifted Tate line must be interchanged. The proof now checks its self-symmetry on an actual one-term K-flat complex. Merely assuming that the tensor factor is invertible would not justify this interchange in a signed derived category.

The statement, its hypotheses, and its existing statement dependencies are unchanged. No statement dispute was found. In particular no proper base-change theorem, projection-formula theorem, or trace-existence theorem is silently added: these are hypotheses here. The equation in step 3 proves that the additional intermediate map lambda is invertible, so the proof does not add a projection-isomorphism hypothesis absent from the item. The hypothesis involving t_1 is stronger than needed for this second rearrangement; it is retained.

## Existing-node and blueprint searches

Read `dag/chapters/sec-six-functors-basics.json` and `dag/units/sk-thm-int-restriction.json`. The item realizes the second-triangle portion of unit step 1. Its blueprint ancestor is `det-thm-int-restriction-line`, as confirmed by `tools/blueprint_refs.py ancestor`. Read that ancestor's current split and the current `main-20261015` statement/proof, and the proof of `det-prop-p1-adjunction-rational-triangle`, especially “Second identity”. The unit and chapter route are retained. The item is not the unit's key node, so no unit record is changed.

Searched the entire DAG by titles and statement keywords for trace/base-change, projection/counit, monoidal projection, tensor-action and tensor-composition laws, self-symmetry and shifted line objects. The general ringed-topos exchange/projection node and the ringed projection tensor-composition node already give the substantial auxiliary facts. Read their statements in full before using them. `lem-sp-compact-projection-base-change` and `lem-pur-finite-projection-action-laws` were also read; their finite-ring and coefficient-tower settings do not directly cover the pulled-back condensed integral sheaf here, so they are not cited as if they did. `lem-sfb-trace-base-change-first` is a different rearrangement and is not used.

Ran whole-blueprint searches for `projection base change`, `trace base`, `projection tensor`, `ringed exchange`, `self symmetry`, and `Tate symmetry`. No blueprint node states this item exactly in another form; `blueprint.same_as` remains empty. The `ringed exchange` hits concern definitions or base-change theorems, not this trace calculation. No new node was created.

## Mathlib searches

All new recorded queries were run through `/home/ubuntu/weil-launcher-nt/msearch.py Q115 lem-sfb-trace-base-change-second ...`; the exact queries and results are preserved in `searches.jsonl` and appended to the item's prior search records. The existing Q159 records were retained verbatim.

The first LeanFinder phrasing about the even shifted Tate line returned homology-sequence and connecting-map facts. The second phrasing about a monoidal adjunction, a Beck–Chevalley mate, and a linear functional returned rigid-category tensor-Hom and evaluation mate lemmas. Their returned types do not assert the required comparison of a square of pushpull adjunctions with projection and trace. LeanSearch returned ordinary algebraic trace/base-change and transvection results; in particular `LinearMap.trace_baseChange` concerns endomorphisms of finite free modules, not this trace morphism in a derived sheaf category. Loogle `"projection", "mate"` and both source grep phrasings returned no hits. None of these results is an exact match or a one-line specialization giving this item. No service was unavailable in these searches, and no unrun query is recorded.

## Not duplicates

No new nodes, so there are no new/existing node pairs to justify. In particular the general Stacks 0E48 and 0B56 coherence facts are cited through their existing nodes rather than recreated.

## Review by Q115

I read the current integral line proof `(1)` and the rational triangle proof's “Second identity” as the source of the item's role and its factor order. For the actual map definitions I read Stacks `sites-cohomology.tex`: Tag 0B56, `equation-projection-formula-map`; Tag 07A7, `remark-base-change`; Tag 0E48, `remark-compatible-with-diagram`; Tag 07A4, `lemma-pullback-tensor-product`; and Tag 0D6D, `lemma-derived-pullback-composition`. I also read Tag 06YQ, `lemma-bounded-flat-K-flat`, for the one-term model. Stacks omits the verification of 0E48, but that verification is already the statement of the existing general coherence node; this item does not cite the omission as a proof. The proof is marked agent-written because its explicit six-step calculation expands what the blueprint only sketches.

Step 1 uses the statement of `sk-def-sfb-module-derived-pushpull` that these are the total derived module functors, the exactness and coefficient-ring identifications in `sk-prop-sfb-cartesian-coefficients`, and the symmetric monoidality and composition comparisons of `lem-sfb-ringed-derived-monoidal-comparisons`. All apply to commutative ring sheaves on small sites in the chosen universe; the coefficient ring is the pulled-back condensed O_E sheaf. Thus this is the same ordinary unbounded module-derived category as in the item, with no rationalization, completion, or switch to a tower category. The canonical equality fp_1=fp_2 induces the monoidal pullback comparison in that lemma. The localizing subcategories are full, and all required preservation is assumed.

Step 2 uses the actual locally-free-rank-one clause of `sk-def-sp-tate-twist`, the site and independent-universe form of `lem-weil-pbc-independent-bounded-flat-kflat`, and the signed representative symmetry in `lem-sf-ringed-derived-closed-symmetric-monoidal`. The characteristic assumptions make ell invertible, as required to define the twist. The shifted sheaf is bounded above and flat; flatness follows directly from its local rank-one trivializations, where tensor is the identity, and local exactness. I explicitly compute the sheaf flip on two multiples of a local generator. Equality is proved for sheaf maps, then chain maps, before passing to the derived category; I did not use the false principle that equality of general derived morphisms can be checked locally. The exponent is (-2)(-2)=4. This is the only parity-specific step.

Step 3 uses the statement, not the proof, of `lem-weil-pbc-ringed-exchange-tensor-coherence`: its two displayed composites are equal, for any commutative square of ringed topoi and arbitrary derived objects. I substituted f'=p_2, g=f, g'=p_1, E=T_X, Q=K, and checked each source and target. Its mate is identified with b_2 using the transpose characterization in `def-weil-pbc-adjunction-mate`; the monoidal/symmetry comparison cited in the step converts the node's right-factor convention to the item's left-factor convention. This conversion is justified by equal adjoint transposes, so no alternate isomorphism is substituted. All inverses initially used are the item's hypotheses. The equality itself shows that lambda is an isomorphism. No smallness, boundedness, or flatness hypothesis beyond those in force is imported from an unrelated coefficient setting.

Step 4 expands the item's definitions of G, e, B and uses the natural monoidal comparison of pullback supplied by `lem-sfb-ringed-derived-monoidal-comparisons`. The only trace substitution is the hypothesis t_2 b_T=f^*t. The displayed domain H is U tensor V tensor V inside R, and D lands in a tensor S tensor T. These are definitions and substitution in step 3, so the step is marked elementary. It neither constructs a trace nor uses the first triangle or any integration identity.

Step 5 uses exactly the first tensor-action identity in the statement of `lem-sfb-ringed-projection-tensor-composition`, with E=V and the base factors a,T, and the symmetry compatibility of `lem-sfb-ringed-derived-monoidal-comparisons`. I checked the two fibre-factor orders: successive right extraction leaves old V then new V, while combined left extraction gives new V then old V. The explicit R(1_U tensor sigma_V,V) accounts for that difference. Step 2 removes it. The remaining equality is inverted using the projection isomorphisms already assumed (and lambda's invertibility proved in step 3). This is a direct substitution in an existing general coherence law, not a new auxiliary comparison left implicit.

Step 6 uses the explicit naturality-in-both-variables clause of `lem-sf-ringed-derived-closed-symmetric-monoidal`, for t_2:S to the tensor unit. The unitors identify the resulting sigma_(R_X,T) with the unit symmetry. It converts the step-4 output ordering to the step-5 ordering and yields the exact required right-hand side. This is an elementary naturality square. I checked both final endpoints and the canonical p_1^*GK=p_2^*GK identification.

For B1–B10 there are no new nodes to check. The item remains self-contained, its TeX is written once, all cited ids already exist, and every proof use has a verbatim statement excerpt in `citations.json`. The existing source for `lem-pc-bounded-above-flat-kflat-site` labels the bounded-flat lemma as 06YS, but the local Stacks tag map identifies that lemma as 06YQ (06YS is the K-flat resolution theorem); I avoided this metadata problem by citing the already existing independent-universe node, whose source has the correct 06YQ tag. No other node was edited.

For C1–C4 I opened every cited statement and matched the specific clauses above; no definition is cited as a theorem about another notion. There are no tags standing in for uncited non-elementary facts. C5 is addressed by the existing-node/blueprint searches. C6: the dependencies are generic monoidal, ringed-topos, Tate-definition and K-flatness tools; none needs this trace rearrangement. The server check will test the actual graph. For C7–C8 the general exchange/projection coherence, signed derived tensor structure and K-flatness criterion are generic tool uses, declared in `split_report.tool_uses` for the maintainer's route decision. They do not replace the integration route of the unit.

For D1–D5 no new node restates the item or one of its clauses: the six steps carry the argument and only cite existing, genuinely more general results. For E1–E6 I checked the ringed-site hypotheses, all square orientations, all coefficient categories, every inverse and both final endpoints. The symmetry calculation would be wrong for an odd shifted line in characteristic different from 2; this edge case explains why the even shift is essential rather than an unspoken arbitrary-invertible-object claim. Empty schemes and K=0 give the unique zero-object morphisms and are included. For f the identity, the formulas reduce to naturality of a functional on the even shifted line. The calculation does not use division by 2 or cancellation of the integer 2, so ell=2 is allowed. Nontrivial monodromy of the Tate sheaf is allowed: changing a local generator multiplies both tensor factors, preserving the computed flip identity. E7: the item's statement agrees with its source intent and needs no correction.

All six proof steps are shorter than 2000 characters. The tensor comparison in step 5 is the displayed specialization of an already-cited tensor-action theorem; it does not conceal an additional lemma. No compiler, Lake command, git command in the shared repository, or shared-project write was run. No second agent was started.

## What could not be finished

Nothing remains in the mathematical split. Server validation and direct delivery are performed with the required delivery tool after this report is written.
