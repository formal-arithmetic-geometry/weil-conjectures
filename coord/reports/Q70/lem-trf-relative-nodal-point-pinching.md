# Q70: lem-trf-relative-nodal-point-pinching

## Files written

- dag/nodes/sec-trace-formula/lem-trf-relative-nodal-point-pinching.json: item, statement unchanged, split into eleven steps; retains the original metadata and searches.
- dag/nodes/sec-trace-formula/lem-trf-codimension-one-points-affine-neighbourhood.json: new statement-only node, Stacks 09NN; no Mathlib match after two semantic phrasings, LeanSearch, Loogle and logged Mathlib grep.
- citations.json: one verbatim statement quotation for each use in every item step.
- searches.jsonl: actual msearch records, including searches of possible completion prerequisites that were ultimately unnecessary as new nodes.
- report.md: this report.

One new unsplit statement, zero new Mathlib leaves. Only sandbox files were written. No Lean, compiler, Lake, build or direct git command was used.

## Attachments

None. Searched all lean/WeilConjectures for the blueprint id, pinching/Ferrand and closed-pushout terminology; the additional algebraic-geometry search for finite sets and affine neighbourhoods found ProjectiveSpace/AffineNeighbourhood.lean. Its IsQuasiProjective.exists_isAffineOpen_superset needs quasi-projectivity, unlike the new general 09NN statement, and does not state the item. No sorry declaration was treated as a finished proof.

## WANTED

None: the proofs used here are in the locally available Stacks source. The ancestor's Temkin archival request is not needed for this finite pinching proof.

## Audit of the imported material

The original node had an empty proof. Its statement is sound as written; no STATEMENT-DISPUTED correction was necessary. The absolute separatedness needed for 09NN is obtained only on the inverse image of an affine open of S, never assumed of X or S. For properness of the quotient, 03GN also needs separatedness and local finite type of the target over S; these are proved before it is applied. Merely quoting 03GN for descent of properness would have missed those hypotheses.

I retained the existing blueprint ancestry. The current main-20261015 lem-trf-local-term-locality.proof.md describes the contracting-correspondence theorem, not this auxiliary construction. This node serves the already-recorded descendant chain for complementary-subcurve contractions; the proof does not claim that the ancestor file itself contains a pinching theorem. The chapter and unit statements and routes were not changed. Generic off-unit tools are declared in split_report.tool_uses, rather than asserting maintainer-owned tool_uses.

## Search and reuse

Read coord/delivery-errors.md B--E in both copies and checked each category. Whole-DAG searches by tag, keyword and statement, together with blueprint_refs.py searches for pinching, pushout, 09NN, 0E36, codimension one, finite set of points, complete local and regular complete, found no existing general 09NN node. The existing generic Ferrand node lem-sfb-ferrand-scheme-pushout supplies construction, quotient topology, chart rings, complements, open restriction, relative separatedness and finite type. Its statement was read in full.

I initially considered a separate 0E36 node but did not create it: the existing exactness and finite-extension-completion nodes give the completion calculation directly. Similarly there is no new smooth-completion node: regularity, completion regularity/dimension and the existing complete coefficient coordinates give k[[t]]. There is no new node for finite generation of A over its equal-residue subring, for the power-series quotient, for the singleton case, or for the subcurve immersion; those arguments are written in the item's steps.

Mathlib hits were read as returned, including affine-open bases (only one point), finite unions of disjoint affine opens (the needed opens need not be disjoint), separated/affine morphism lemmas, smooth charts and formal lifting, and finite-module completion/tensor comparisons. None states the item or the new affine-neighbourhood statement. The new node's five exact queries and actual response digests are retained in its mathlib_searches. The extra completion searches are retained on the item and do not support any claim that those tools are absent from Mathlib.

## Not duplicates

lem-trf-codimension-one-points-affine-neighbourhood vs lem-trf-relative-nodal-point-pinching: 09NN is the general affine-neighbourhood prerequisite for arbitrary separated schemes with the stated component condition and local dimension bound; it asserts no pushout, pinching, node, proper quotient or subcurve immersion. The item uses it only to verify the hypothesis of the already existing Ferrand theorem.

lem-trf-codimension-one-points-affine-neighbourhood vs lem-trf-exceptional-contraction-diamond: the latter proves a diamond for supplied rational-component contractions on multipointed curves. It does not state the general common-affine-neighbourhood assertion; its reference to 09NN occurs in its proof material. The new node does not contract any component and does not state a clause of that diamond.

The quasi-projective affine-neighbourhood declarations in Lean and the Hilbert-representability nodes require stronger hypotheses or take the affine-neighbourhood property as an assumption. The generic-points neighbourhood nodes concern generic points, not these arbitrary closed points. Neither is a duplicate.

## Review by Q70

I read more-morphisms.tex Situation 0ECI and Proposition 0E25, including its explicit chart and complement construction, Lemma 0E26 and Lemma 0E27. I read varieties.tex Proposition 09NN in full, curves.tex's pushouts section and Lemma 0E36 with its proof, Example 0C1J, and morphisms.tex Lemma 03GN with its exact extra hypotheses. For the smooth-branch calculation I read varieties.tex 056S, more-algebra.tex 07NY/07NV, and algebra.tex 0C0S(2). For completion I read algebra.tex 00MB and 07N9. These sources give the route, while the relative-base adaptations, the finite-module bound, the field-extension check and the branch-restriction interpolation are written out by me; proof_origin is therefore agent.

For the only new node I compared every hypothesis with varieties.tex 09NN: separatedness, finite components on quasi-compact opens, and Noetherian local rings of dimension at most one are all present. Its r=0 clause is witnessed by the empty affine open, Spec of the zero ring. Its r=1 case agrees with an affine-open basis, and for r>1 its conclusion genuinely needs the common-neighbourhood theorem. It has a statement only and no postponed proof disguised inside that statement. I found no blueprint counterpart. Its definition dependencies introduce schemes, separatedness, components, Noetherian rings, local dimension and affine spectra.

Step 1 uses the multipointed definition for finite presentation, the proper definition for its closed relative diagonal, finite-type-over-Noetherian for X, and finitely-many-components for quasi-compact opens. I then apply precisely the new node's statement. All pinched points lie over the same point of S, so a single affine V works. X_V is absolutely separated by the two diagonal factorizations; the local dimension bound comes from specialization chains. No absolute separation of X was inserted.

Step 2 uses the full Ferrand statement, not any unstated feature of its proof: its quotient topology proves surjectivity when a is onto, its cartesian square gives the scheme-theoretic inverse image, and its affine charts and complement assertion are explicitly in the node. The finite-module definition checks integrality of a. Step 3 proves the extra finiteness directly: 1 and lifts of a finite k-basis of C/B span A over P. This also covers charts disjoint from F, where C=B=0 and P=A.

Step 4 uses Ferrand's finite-type clause over the Noetherian field base; it does not apply that clause over the arbitrary S. The two Noetherian nodes cited supply Noetherianity and finite presentation of affine coordinate rings; quasi-compactness is checked from the quotient topology. Step 5 uses the affine-source-separatedness statement for b, Ferrand's relative separatedness for t, clause (a) of the finite-type cancellation statement for t, and then exactly the last sentence of the universally-closed-image statement. This checks all hypotheses missing from a naive invocation of proper-image descent.

Step 6 uses Ferrand's stated open-restriction property. Deleting the other F-points removes their entire fibres, leaving an actual identity leg Spec k -> Spec k, whose pushout is the remaining open part of X. No assertion that the completion alone proves a neighbourhood isomorphism is used.

Step 7 uses exactly the statements of completion-exact-finite-modules and completion-finite-extension. All modules in the short exact sequence are finite over the Noetherian P. The maximal ideal of f acts trivially on k and k^r. The latter node includes compatibility of the local maps and explicitly identifies the semilocal completion, so the resulting fibre product uses the actual residue maps. No uncited 0E36 comparison is hidden: its proof is the calculation in this step.

Step 8 uses smooth-scheme-over-field-regular on a smooth open, then completion-regular-local and completion-dimension, then complete-coefficient-coordinates with d=1. I explicitly cite completion-mod-power at N=1 for the residue-field identification; its stated surjectivity and kernel formula give precisely the needed quotient. The regular-local-ring definition supplies one generator of the maximal ideal. The dimension is exactly one, not just bounded by one: a generic point of a component containing e_i gives the nontrivial specialization since pure dimension excludes singleton components. The residue and coefficient field are k, as the original closed immersions are rational k-points. Step 9 writes both the surjectivity and kernel computations of the formal power-series map. The kernel is exactly (uv) by its coefficients; no division by 2 is used.

Step 10 also cites the Ferrand node for the base-changed affine quotient charts and finite-type-over-Noetherian for the geometric source curve. It uses exact field scalar extension to identify the base-changed chart rings, so the earlier arguments apply over every algebraically closed extension Omega, not just over k. The topological argument preserves generic points and only identifies finitely many closed points. Images of components are closed because their saturations add finitely many closed points; pulling back a proper closed subset to a source component shows it is finite. This proves pure dimension one rather than assuming it from the ring calculation. Flatness over a field and the empty marking clauses then give exactly the two multipointed definitions cited. Empty fibres, disconnected curves, self-identification of two points on the same irreducible component, and pairs on different components are all covered.

Step 11 uses the Ferrand chart statement and the closed-immersion affine criterion. It does not infer a scheme factorization merely from a set-theoretic inclusion. The explicit q_j delta_j corrections realize a surjective ring map to A/I, with no need to assume D contains a whole neighbourhood of a chosen point. Each residue on D is kept fixed; at most one such residue per fibre is precisely the required hypothesis. This calculation even works for a general closed D with that intersection condition, so reducedness is used only to identify its image as reduced. For a prohibited pair with both points in D, incompatible residues cannot be corrected, explaining why the hypothesis is necessary.

I checked the empty pinching (Y=X), the empty subcurve, singleton pinching, same-component and different-component pairs, characteristic two, arbitrary nonseparated S, and an X not separated over k but proper over S. No counterexample or typing defect arose. I corrected a tag in the drafted step source from the guessed situation number to the actual 0ECI found in tags/tags. All eleven steps are under 2000 characters. Every cited node was opened and its statement read; citations.json quotes those statements verbatim. New-node TeX uses single mathematical backslashes, the graph dependencies are the exact union of step uses, no circular dependency was introduced, and no existing node except the assigned item was edited.

## Unfinished work

The new general 09NN prerequisite is deliberately unsplit, as required for one-level stage-1 delivery. No part of the item's argument is left as an unsupported assertion or a promise of a future proof.

## Validation

Server review_split passed. The first complete dry run passed at 62a27efe6bb. A final citation audit then added explicit references for the completed residue field and the base-changed charts; the complete dry run is repeated for this final version before pushing.
