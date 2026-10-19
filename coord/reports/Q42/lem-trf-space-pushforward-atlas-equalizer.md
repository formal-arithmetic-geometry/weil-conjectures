## Files written

- `dag/nodes/sec-trace-formula/lem-trf-space-pushforward-atlas-equalizer.json`: statement, split into six steps; not a Mathlib leaf. No new nodes and no new Mathlib leaves.
- `citations.json`: the verbatim statements backing all 13 step/node citation pairs.

## Attachments

None. Searches of the read-only slopmaster2 `WeilConjectures/` for the exact blueprint tag and for atlas/equalizer, compute-pushforward and algebraic-space terminology found no declaration giving this item. The exact upstream master checkout likewise supplies no attachment. No Lean file was written or compiled.

## WANTED

None. All sources used are present under `literature/stacks-project/`.

## Statement corrected

STATEMENT-DISPUTED: the imported formula `F_R=p_1^*F` (also `p_2^*F`) is ill-typed. The domain of `p_1^*` for `p_1:R -> U` is Mod(O_U), while F belongs to Mod(O_X). The corrected formula is `F_R=p_1^*F_U`, canonically identified with `p_2^*F_U`; equivalently it is the restriction of F along `p p_1=p p_2:R -> X`. This is the restriction F|_R in Stacks 03M8, rather than a new hypothesis or a changed conclusion. X and U can be distinct, for example the identity morphism f of the projective line with its atlas consisting of the two standard affine opens (their finite disjoint union is affine); F=O_X then has the wrong domain for the printed expression. The correction merely makes the intended expression meaningful.

All original hypotheses remain: S is any scheme, f any algebraic-space morphism, p the given surjective etale affine-scheme atlas, and F an arbitrary O_X-module. No separatedness, quasi-compactness of f, quasi-coherence, or finite-generation hypothesis is used or added. The statement now cites the existing algebraic-space fibre-product theorem for R; the scheme-only fibre-product definition was removed from its direct statement dependencies. Affineness is defined in def-pc-scheme and is not needed by the proof, just as 03M8 permits arbitrary scheme atlases.

## Source error

Stacks `spaces-morphisms.tex`, Tag 03M8, label `lemma-compute-pushforward`, prints `(V times_Y U) times_X (V times_Y U) = V times_Y R`. The overlap for the covering is instead taken over W=V times_Y X. This is not an innocuous equality over X: take X=U=Y=Spec(k), f=p=id, and V=Spec(k) disjoint union Spec(k). The printed left side has four points and the right side has two. Over W=V the overlap has two points and is exactly V times_Y R. Step 3 writes the correct universal-property argument, keeping the same v coordinate in both copies. The source also calls the displayed three nonzero terms a “short exact sequence”; we use exactly its displayed assertion, exactness at the first two terms, with no claim of surjectivity onto the last term.

## Searches and reuse

The entire DAG was searched for Tag 03M8, compute-pushforward, atlas/equalizer and sheaf descent terminology. Whole-blueprint searches with `tools/blueprint_refs.py` included `03M8 equalizer pushforward`, `equalizer`, `atlas`, and `direct image`; none states this algebraic-space atlas/direct-image result. The equalizer hits about scalar extension are different statements. The historical ancestor remains lem-trf-local-term-locality through the existing via chain; this is the 03M8 input to the 03M9 affine-target paragraph, not a new proof of the current unit's contracting-correspondence theorem. I read the chapter, current unit record, current main-20261015 locality statement/proof, and the parent's 03M9 dependency use. The unit's realized fields belong to its key node and were not touched.

Existing nodes provide all substantial inputs: enlarged etale ringed-site comparison, fibre products and pullback of covers, chartwise etale permanence, and etale module restriction. No elementary consequence or clause of the item was made into a child node.

Retained the item's original Q05 search records. Five additional searches were actually run via msearch.py and read from the command output/log: two LeanFinder phrasings, Loogle on `SheafOfModules, CategoryTheory.Limits.equalizer`, grep on `AlgebraicSpace|atlas.*equalizer|equalizer.*atlas`, and LeanSearch on the direct-image atlas equalizer. Loogle and grep returned zero hits; the semantic searches returned scheme/Zariski module operations, scheme gluing, and quasicoherent presentations. I inspected Mathlib/AlgebraicGeometry/Modules/Sheaf.lean: its Modules are modules on a scheme's Zariski ringCatSheaf, not the algebraic-space small-etale site. These are not one-line specializations of the item. No service was unavailable, and the new query texts/results are preserved in the node and searches.jsonl.

## Review by Q42

I read Stacks 03M8 (`spaces-morphisms.tex`, lemma-compute-pushforward, statement and complete proof), 03H7/03G1 (`spaces-properties.tex`, remark-explain-equivalence and lemma-compare-etale-sites), 03G2 (lemma-functoriality-etale-site), the module push/pull discussion preceding 03LV, 03LV/03LW (lemma-etale-exact-pullback and equation-restrict-modules), 041F(3) (`spaces-topologies.tex`, lemma-etale), the sheaf definition in sites.tex, and 03DA (`sites-modules.tex`, lemma-abelian). There are no new-node sources to check. The 041F covering assertion is cited through an existing node, not silently treated as elementary because the source omits its proof.

Step 1 uses the statement of lem-trf-space-enlarged-etale-ringed-site-model for the module equivalence and the canonical morphism induced by V -> X times_Y V. I checked that it supplies module sheaves, regular-function ring maps and composition, not only an equivalence of set-valued sheaves. The continuous direct-image clause of def-weil-pbc-sites-and-cohomology says exactly precomposition. Def-trf-space-etale-module-functors fixes the canonical direct image and its chart projections, so no arbitrary isomorphism of functors is substituted. Sites are chosen small in the existing size convention of the model and algebraic-space definition; no colimit over an unbounded category is invoked.

Step 2 uses the actual statements of lem-trf-space-fibre-products-etale-covers and lem-trf-space-chartwise-etale-permanence: base changes preserve coverings, a base change of a representable etale map to a scheme is a scheme, and the relevant composites are etale. The source of V -> Y is a scheme; p is representable surjective etale by hypothesis; R is a scheme because it is the pullback of p to U. Thus each stated scheme representability assertion has its required scheme test. W may remain an algebraic space and is therefore evaluated only on the enlarged site. No affineness of R or fibre-product representability for an arbitrary morphism f is asserted.

Step 3 takes only the fibre-product universal property from the fibre-products node. The displayed triple establishes both directions and the projection compatibility explicitly. It is elementary, and it is also where I repaired the source's erroneous overlap base. This is not an appeal to the proof of the cited node.

Step 4 uses the precise tensor-pullback-equals-restriction clause of lem-trf-space-etale-module-pushforward-restriction, not just its base-change comparison for another category. Its etale hypotheses hold for p and the projections of R. The enlarged model's statement gives the localized-site identification, including the structure sheaf. This identifies a_* and b_* on sections with the same extended F on Z and Q; their maps are the actual restriction maps, whose chart projections are specified by the functors definition. This step corrects the imported F_R type error and retains the canonical p_1/p_2 identification.

Step 5 invokes the equalizer formulation of the sheaf axiom, verbatim in def-weil-pbc-sites-and-cohomology, for the singleton cover Z -> W. It proves injectivity and existence/uniqueness of gluing, rather than merely naming “descent.” Def-weil-sheaf-of-modules-category supplies the semilinear restriction rule; the common map to V makes each map linear over O_Y(V). Equality of two elements in an abelian group is equivalent to their difference being zero. These are elementary consequences of the cited definitions.

Step 6 spells out naturality using restriction functoriality and the module functor definition, and uses exactly the sectionwise-kernel clause of def-weil-sheaf-of-modules-category. Unique preimages ensure that the inverse to the sectionwise kernel map respects restrictions, addition and scalar multiplication. No false sectionwise computation of cokernels or of arbitrary sheaf images is used. Hence the first arrow is monic and its image is the kernel, with no last-term surjectivity claim.

I tested the statement/proof on the identity atlas, F=0, empty X (the empty-cover sheaf axiom gives zero sections), empty V, the two-component etale test V above, and a nontrivial two-open atlas. In all cases the corrected overlap and pullbacks have the asserted domains. The proof works for arbitrary modules, so no quasi-coherence assumption is hidden. All step lengths are below 900 characters; no non-elementary step crosses 2000 or hides a separate comparison lemma. Every cited statement was opened and its full text was copied to citations.json; the seven cited nodes have no dependency path back to this item. The proof-dependency list is exactly the union of uses. No new node raises B1-B9 or duplicate issues, and no off-unit theorem is needed: the substantive algebraic-space helpers are in this unit, while the generic sheaf/module definitions are definition or Mathlib tools. No SGA source is used.

The corrections found in this review were the ill-typed F_R expression, the printed overlap base, and the statement's scheme-only fibre-product dependency. The proof follows the source's sheaf-condition route with these repairs; it does not relabel the item as a new lemma or move its proof into a child.

## Unfinished work and validation

No mathematical step is left unfinished. The item is split; its cited unsplit inputs remain separate queue items. The server-only preliminary review_split check passed with 0 new nodes. Required final dry run and push follow this report; their stdout is the delivery evidence.
