# Split of lem-sfb-proetale-affine-subsite-equivalence

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-proetale-affine-subsite-equivalence.json: statement, now split in six steps; not a Mathlib leaf.
- citations.json: 18 verbatim step/node statement extracts.
- No new nodes and no Mathlib leaves. The item statement and its three statement dependencies are unchanged. The inherited blueprint ancestry, source, creation fields, and earlier searches are retained.

## Attachments

None. Searched the entire read-only WeilConjectures tree for the item id, affine-subsite terminology, and affine equivalences, then read Comparison/Affine.lean and the comparison sheaf uses. AlgebraicGeometry.Scheme.AffineProEt.isEquivalence_sheafPushforwardContinuous_toProEt (Comparison/Affine.lean:441) concerns the full subcategory defined at lines 88–91 by proAffineEtale, whose objects admit cofiltered affine-etale presentations over the base. This is narrower than all affine weakly etale objects in this item, so it is not an exact attachment. Its existence is useful context, not a proof of the item as stated. No compiler was invoked. The upstream master reference was not used as finished evidence.

## WANTED

None. All mathematical sources are present locally.

## Corrections and source alignment

The item had no proof. Its statement accurately means Stacks 098W and needs no correction. Stacks' displayed restriction target in lemma-alternative reads S_affine,etale, although its immediately preceding definition and its asserted equivalence use S_affine,proetale. This is a typographical inconsistency in the source display; the item already uses the correct affine pro-etale site. No mathematical source error or statement dispute is introduced.

Read the fixed six-functors-basics chapter, module-derived-factorization unit, and current ancestor lem-sfb-module-mapmod-pullback-kflat. This is an auxiliary descendant through the enough-points argument, not a key unit node; no unit realization file is changed. Its inherited blueprint.from.place already records the auxiliary nature of the stalk route. Searches of all blueprint nodes for “affine pro” and “special cocontinuous”, together with DAG searches by 098W, 03A0, affine basis, comparison, stability and fpqc, found the reusable nodes cited in the split. No new node is needed.

The item is absent from Mathlib as an exact theorem. The logged LeanFinder and LeanSearch phrasings returned generic dense-subsite comparisons and affine-etale/affine-Zariski comparisons. Loogle confirmed the generic dense-subsite API; the grep over AlgebraicGeometry/Sites found affine-etale and Zariski equivalences, not the all-affine weakly-etale comparison. Read Proetale.lean, AffineEtale.lean:140, DenseSubsite/Basic.lean:538ff and DenseSubsite/SheafEquiv.lean:107ff. The generic API requires the density and topology conditions this split proves, so it does not make the item a one-line Mathlib leaf. Actual tool results are retained in searches.jsonl and appended exactly by query to mathlib_searches; inherited searches are not rewritten.

## Unfinished work

None for this one-level split. Existing cited statements remain their own DAG items where applicable. No new unsplit node, hidden statement, or off-route replacement is proposed.

## Review by NH

I read Stacks proetale.tex, lemma-alternative (098W), lemma-proetale-affine (098D), definition-standard-proetale (098E), the covering definition and covering-stability lemma (098C). I also read sites.tex, lemma-equivalence (03A0), its five hypotheses and beginning of its proof, and checked the existing special-cocontinuous definition and comparison statements against those hypotheses. Each step's source identifies the tag and TeX label. The source's one-sentence exercise has been expanded into the actual verification, rather than turned into another node restating 098W.

Step 1 uses open-immersion-etale exactly for open immersions, the first clause of det-pe-morphisms-etale-comparison for etale implies weakly etale, and the composition clause of sk-lem-pe-weakly-etale-stability for their composites to X. Schemes 01IT and the affine-opens-basis node give the cover of an arbitrary U. The proetale-site statement gives the finite-affine-refinement condition. For the family of all affine opens, each affine test open W itself is one member, so no unjustified quasi-compactness argument or non-elementary refinement theorem is being suppressed.

Step 2 uses morphism-affine-schemes-affine, whose statement really gives affineness of the inverse image of every affine open. I read Morphisms 01SH (lemma-morphism-affines-affine). For a finite jointly surjective family of affine weakly etale maps, the inverse images of W are therefore finitely many affine opens with image union W. This proves the exact covering condition of the proetale-site node and checks the agreement with standard covers in 098E; pointwise surjectivity alone for an arbitrary infinite or non-affine family was never substituted for fpqc covering.

Step 3 uses affine-spectra fibre products exactly with affine middle object U, as guaranteed here. I read Schemes 01I4 and 01JQ. It does not assume affine intersections over an arbitrary non-separated X. Weakly-etale stability supplies composition and base change. The fpqc-covering-axioms node states all three covering axioms for arbitrary schemes; I read Topologies 022D. Combined with the proetale-site definition these prove the axioms on the finite affine families and give the continuous-functor conditions stated by sites-and-cohomology. All objects and morphisms remain over X; the pullback is over U, not over X. The small-site hypothesis is provided by the original universe/skeleton convention.

Step 4 takes the finite affine opens directly from the proetale-site statement applied to the affine target U itself. Step 1 and composition stability make their maps weakly etale, and step 2 supplies the covering check. Each required factor is the actual open inclusion into the selected original covering member. The special-cocontinuous definition's cocontinuity clause is exactly this refinement condition. Nothing from the proof of a cited node, rather than its statement, is being borrowed.

Step 5 is elementary: fullness and faithfulness of a full inclusion give the requested lift and equality globally, and identity coverings give their local versions. I checked these against clauses (c) and (d) of the cited special-cocontinuous definition; the other clauses are the explicit conclusions of earlier steps. This elementary observation is not a new node.

Step 6 uses the existing special-cocontinuous-sheaf-equivalence statement, which explicitly says both that the morphism of topoi is an equivalence and that its inverse-image functor is precomposition. It therefore gives restriction on sheaves and on all components of sheaf maps, not merely an abstract equivalence of categories. The same compatible universes and skeletons fixed in the original statement make its two input sites small. Generic off-unit statement tools are declared in split_report.tool_uses with the precise role of each; definitions are notions, not route replacements.

I tested empty schemes, the empty covering of an empty affine, singleton identity coverings, non-quasi-compact X, and non-quasi-separated X. Empty finite families give the required image union exactly when the target is empty; all affine-open and pullback arguments remain valid. No global finite affine cover, affine intersection, Noetherian hypothesis, or ind-etale presentation is assumed. All six steps are shorter than 2000 characters. Every non-elementary fact used is a cited existing statement; the refinement and local-fullness calculations are written out. I checked delivery-errors B–E for self-contained notions, sources, actual searches, no duplicate or clause-restating new nodes, exact hypotheses and citations, and absence of circular proof structure. citations.json contains one literal statement extract for every one of the 18 uses, checked by substring membership against the repository JSON. The dry run below provides the independent mechanical DAG/cycle and route check.
