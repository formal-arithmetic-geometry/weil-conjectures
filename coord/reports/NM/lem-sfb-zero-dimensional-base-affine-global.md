## Worker report

Files written:

- `dag/nodes/sec-six-functors-basics/lem-sfb-zero-dimensional-base-affine-global.json`: existing statement, unchanged; split into ten steps, with the union of cited dependencies and an agent proof origin.
- `dag/nodes/sec-six-functors-basics/lem-sfb-spectral-space-cohomology-dimension.json`: new statement-only lemma, unsplit. Mathlib verdict: no match. This is the vanishing assertion of Stacks 0A3G for arbitrary abelian sheaves on spectral spaces, without Noetherianity.
- `citations.json`: a verbatim statement quote for each of the 29 step/node citations.

Attachments: none. Searches for the item tag, affine/global cohomology, spectral-space cohomology, 0A3G and Scheiderer in the live `lean/WeilConjectures/` source found no complete declaration stating the item or the new lemma. Existing source proofs of dimension or étale-only statements do not attach this arbitrary internal-ring-module pro-étale implication.

WANTED: none. The Stacks sources needed for the split are present locally.

The seeded item had no proof. Its statement is correct and is retained exactly. Its source is an agent-formulated consequence, rather than a theorem stated verbatim in Stacks: I have marked the synthesis as agent-written. The inherited blueprint provenance identifies the local heart estimate inside the compactification refinement route; this delivery does not change that route or the unit record.

The main trap was applying the existing Noetherian Zariski cohomology bound to a possibly non-Noetherian base. I instead extracted exactly the spectral-space vanishing theorem that covers the actual hypotheses. During self-review I also added the internal/sectionwise module equivalence explicitly: the arbitrary ring-sheaf comparison must precede using the ringed-site module cohomology lemma. I replaced an implicit sheafification-stalk assertion by the written universal-property argument for a presheaf that vanishes on an affine basis.

What remains: the one new node is intentionally not split, as required for a one-level stage-1 delivery. There is no unfinished argument in the item's split and no statement dispute. No Lean was written and no compiler or build command was run.

## Searches and sources

The item and the new lemma were searched using the prescribed `msearch.py NM lem-sfb-zero-dimensional-base-affine-global` command. The searches are in `searches.jsonl` and the exact tool/query pairs used for the final statements are copied into their `mathlib_searches`. I tried both descriptions of spectral-space cohomological dimension, plus LeanSearch, a qualified Loogle pattern, and source grep. Results were definitions of sheaf cohomology, general spectral sequences, injective-dimension or t-structure vanishing, and affine-scheme facts. None asserts a cohomological bound by spectral Krull dimension. Two exploratory Loogle patterns used unknown identifiers; I read those results and reran the spectral query with `CategoryTheory.Sheaf.H`. The exploratory geometric-fibre searches are retained in the log although no geometric node was ultimately created.

I read the chapter and the compactification-coherence unit, the main-20261015 ancestor proof and the dimension-extension blueprint statement. Before creating the new node I searched the whole DAG by 0A3G and by spectral-space/cohomology concepts, and ran `tools/blueprint_refs.py search` for spectral, spectral space, cohomological dimension, 0A3G, Leray, and dimension bound. No blueprint statement supplies the required non-Noetherian spectral-space vanishing theorem.

For the item I read Stacks `cohomology.tex`, Tag 0A3G, `proposition-cohomological-dimension-spectral`, especially part (1); `sites-cohomology.tex`, Tags 0732 (`lemma-Leray`), 072W (`lemma-higher-direct-images`), 03FD (`lemma-cohomology-modules-abelian-agree`), and 03F3 (`lemma-cohomology-of-open`); `schemes.tex`, Tag 01K1 (`lemma-fibre-topological`); `algebra.tex`, Tag 00P3 (`lemma-dimension-preserved-field-extension`); `morphisms.tex`, Tag 01T4 (`lemma-base-change-finite-type`); and `properties.tex`, Tag 094L (`lemma-quasi-compact-quasi-separated-spectral`). I also read the continuous-site finite-limit criterion and composition setup in `sites.tex`. The new node's source is precisely 0A3G(1), not the restriction-surjectivity clause of that proposition.

## Not duplicates

lem-sfb-spectral-space-cohomology-dimension vs lem-sfb-zero-dimensional-base-affine-global: the new lemma concerns arbitrary abelian sheaves on a spectral topological space and no finer site or affine-local hypothesis; the item deduces a bound for pro-étale internal modules from affine vanishing via a separate spectral sequence.

lem-sfb-spectral-space-cohomology-dimension vs lem-sfb-profinite-geometric-family-heart-cd: the existing lemma is a geometric-family pro-étale coefficient estimate with specific condensed coefficients, not arbitrary abelian Zariski cohomology on a spectral space.

lem-sfb-spectral-space-cohomology-dimension vs lem-weil-pbc-top-degree-abelian-neighborhood-zero: the existing statement is local vanishing after shrinking for a degree-d class on a Noetherian spectral space; the new statement is global vanishing in degrees greater than dimension without Noetherianity.

lem-sfb-spectral-space-cohomology-dimension vs lem-weil-pbc-top-degree-module-restriction-surjective: the existing statement is top-degree restriction surjectivity for locally Noetherian quasi-compact schemes and module cohomology; the new statement is above-dimension abelian vanishing for any spectral space.

lem-sfb-spectral-space-cohomology-dimension vs lem-weil-pbc-top-degree-abelian-open-restriction: the existing statement is surjectivity in degree d for a Noetherian spectral space; the new statement is vanishing above d without Noetherianity.

lem-sfb-spectral-space-cohomology-dimension vs lem-weil-pbc-top-degree-open-restriction-surjective: the existing statement concerns a Noetherian k-scheme and top-degree module restriction, with a scalar structure; the new statement has neither a scheme nor a Noetherian nor a scalar hypothesis and concerns vanishing above the dimension.

lem-sfb-spectral-space-cohomology-dimension vs lem-weil-pbc-top-coherent-cohomology-finite: the existing statement is finiteness of top coherent cohomology for separated finite-type schemes over a field; the new statement is above-dimension vanishing for arbitrary abelian sheaves on general spectral spaces.

lem-sfb-spectral-space-cohomology-dimension vs lem-sc-zariski-dimension-bound: the existing bound has a Noetherian scheme hypothesis, which cannot be discharged for the item. The new lemma allows non-Noetherian spectral spaces and arbitrary abelian sheaves.

lem-sfb-spectral-space-cohomology-dimension vs lem-sc-noetherian-cohomology-above-dimension: the existing node assumes a Noetherian scheme and quasi-coherent structure-sheaf module; the new node has no such hypotheses.

## Review by NM

I checked the split against B–E of `coord/delivery-errors.md`, including the repeated version in its merged section, with the source and every cited node statement open. The item's statement is unchanged. I verified each dependency is used for what its statement says, rather than for an undocumented argument in its proof.

Step 1 uses `lem-weil-pbc-qcqs-over-affine` with exactly affine target, separatedness and finite type. `lem-weil-pbc-qcqs-scheme-spectral` then applies with both qcqs hypotheses. `def-weil-spectral-space` actually includes sobriety, so it supplies the generic points used subsequently. Neither lemma assumes Noetherianity.

Step 2 uses `lem-pod-separated-finite-type-base-change` with the canonical residue-field map, which is an arbitrary allowed base change. The resulting fibre is a finite-type scheme over a field, so the field-extension clause of `lem-kun-dimension-extension` applies to its algebraic closure. I use no dense-open consequence of that lemma. `def-weil-geometric-fibre` explicitly identifies the algebraic-closure base change of the scheme-theoretic fibre with the geometric fibre occurring in the hypothesis. Empty fibres retain dimension minus infinity.

Step 3 is the elementary chain argument written in full. The largest irreducible closed member has a generic point by step 1, and its image is closed because every prime of the affine base is maximal. Continuity therefore places the entire chain in a single fibre. The statement of `def-pc-scheme-fibre` explicitly includes the homeomorphism to the topological fibre; this is not merely an appeal to the definition of a fibre product. `def-kun-topological-krull-dimension` defines the supremum of lengths, including the empty case. Passing to the subspace keeps strict inclusions, closedness and irreducibility. No dimension-additivity theorem or hidden lifting lemma is used.

Step 4 cites `def-weil-pbc-internal-abelian-sheaf-module-equivalence`, whose statement gives an equivalence for arbitrary commutative internal ring objects and preserves underlying sections and restriction maps. The tensor is the sheafified objectwise tensor of `sk-def-sfb-sheaf-tensor`, and the universe restriction is the one already imposed by the item. I explicitly explained preservation of exactness, injectives and evaluated resolutions, so the conversion concerns exactly the internal module category in the item. It adds no constant-ring, flatness, adic, or finiteness restriction.

Step 5 uses `lem-pur-ringed-site-grothendieck-abelian` and `lem-sp-grothendieck-enough-injectives` for the actual arbitrary section-ring sheaves, on the site and all open slices. `lem-pe-ringed-site-derived-evaluation-slice` permits that ring and compares module-derived evaluation with abelian cohomology of the slice. The first clause of `lem-weil-proetale-weakly-etale-localization` identifies the sites, and `lem-weil-pbc-proetale-ringed-open-comparison` identifies the actual restricted ring and modules, not merely a constant ring. Thus the assumed vanishing transfers to the underlying abelian sheaf on every affine open. I did not infer that an injective module remains injective as an abelian sheaf.

Step 6 uses the explicit pro-étale-to-étale geometric morphism of `def-weil-pbc-site-comparison-morphism`, the Zariski-to-étale inclusion morphism theorem, and the general composition theorem. These statements give the composite morphism and its direct image as restriction to the open object. The generic `lem-weil-pbc-site-pullback-abelian-exact` supplies exactness on abelian sheaves; the constant-coefficient clause in the comparison definition is not used.

Step 7 applies `lem-weil-pbc-site-higher-direct-image-sheafified-presheaf` to that actual morphism of sites. Its statement is general, so it is not the more restricted scheme/étale higher-image theorem. `lem-weil-pbc-cohomology-over-object-localization` and pro-étale localization identify object cohomology with the already bounded open cohomology. `lem-weil-pbc-affine-opens-basis` applies to an arbitrary scheme. The final locally-zero argument is proved by testing maps to any sheaf and using separation; `def-weil-pbc-sheafification` supplies exactly this universal property. No unsupported assertion about stalks of sheafification is needed.

Step 8 applies `thm-sp-grothendieck` only after checking its composable-pair and injective-acyclicity requirements. The constant integer specialization of `lem-pur-ringed-site-grothendieck-abelian` supplies the Grothendieck categories; on the trivial site it also gives ordinary abelian groups. Exactness of the abelian inverse image from step 6 and `lem-sp-right-adjoint-preserves-injectives` give injective preservation for the direct image. The acyclicity of injectives for derived evaluation is explicitly in `def-weil-pbc-sites-and-cohomology` (2). Evaluation at the terminal object identifies the composite section functor. Thus the spectral sequence has the actual module/abelian cohomological abutment needed, with no unbounded convergence issue.

Step 9 invokes only the new spectral-space theorem, with spectralness from step 1 and the dimension upper bound from step 3, for the abelian sheaf of each higher direct image. Stacks 0A3G(1) has no Noetherian or coefficient restriction. Step 7 supplies the complementary row bound. Step 10 is the elementary argument through subquotients and the finite filtration of the convergent first-quadrant spectral sequence: every associated graded group in total degree greater than e+a is zero, so the abutment is zero. The comparison already obtained in step 5 restores exactly the required module-derived cohomology group.

I tested the item at X empty, B empty (which forces X empty), e=0, a=0, and zero coefficient ring or module. The dimension argument uses no choice of a point in an empty space. A nonreduced zero-dimensional base causes no issue: closedness of its points suffices, and no regularity or reducedness was used. An infinite product of fields illustrates why the base need not be Noetherian or have algebraically closed residue fields; the proof still uses spectralness rather than discrete finiteness. For the new lemma, the empty space and non-Noetherian profinite spaces have dimension at most zero and agree with the zero-dimensional case in the source; in particular no finiteness of their underlying set was assumed.

The new statement is self-contained with every notion defined or cited, has empty proof and proof-dependency lists, and has its blueprint source and searches filled. It is not a clause of the item or a restatement of its entire argument. The geometric dimension argument, local-zero sheafification argument and rectangle argument remain steps instead of unnecessary nodes. All ten proof steps have fewer than 2000 characters. Off-unit dependencies are declared as generic tool uses in `split_report.tool_uses`; they do not change the compactification unit route. The server checks run before this report returned `check_dag OK` and `review_split PASS`; final validation is the required delivery dry run.
