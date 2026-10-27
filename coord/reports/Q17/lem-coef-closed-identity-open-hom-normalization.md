# Stage-1 repair: lem-coef-closed-identity-open-hom-normalization

## Files written

- `dag/nodes/sec-six-functors/lem-coef-closed-identity-open-hom-normalization.json`: same statement, repaired split; four assembly steps, 2565 characters total.
- `dag/nodes/sec-six-functors/lem-coef-proper-identity-open-site-comparison.json`: statement, unsplit, no Mathlib match. Proper identity-open comparison normalized to the named direct-image mate, including the exact identity-open factor.
- `dag/nodes/sec-six-functors/lem-coef-relative-hom-change-of-presentation.json`: statement, unsplit, no Mathlib match. Arbitrary chosen compactification and changes of both compact-support presentations, with counit-compatible right-adjoint change in the normalized relative Hom bijection.
- `citations.json`: verbatim statements for every cited node of every parent step. `searches.jsonl`: actual search-command records. `returned-proof.json`: exact returned four-step proof retained for review.

## Attachments

None. I searched the live read clone's WeilConjectures source for the exact blueprint tag, `closedIdentityOpenHomNormalization`, `compactSupportSiteComparison`, `specifiedExceptionalHomEquiv`, and identity-open language. No project declaration there states the item. The existing Sheaf.Paper.ClosedIdentityOpenHomNormalization theorem ends in `sorry`; it is not an attachment. Its property does retain the same coefficient quotient, two canonical identity-open isomorphisms and the counit-compatible adjoint comparison. I read the complete property and theorem and the specified Hom-equivalence implementation in Sheaf/AlgebraicGeometry/SpecifiedExceptionalClassHom.lean. No Lean file was written and no compiler was run.

## WANTED

None. All sources used are present locally.

## What was wrong and how the return is repaired

This is the batch5 human-requested re-split of the 4887-character proof, not an unchanged re-push. The sandbox initially held only dispatcher marker files, with no node, report or searches to reuse. I restored the node from the current shared repository, whose four proof lengths match the return (901, 823, 1221, 1942). Its statement and maintainer metadata remain unchanged. The supplied return and current node provide the returned argument; no independent old sandbox head was available.

The two substantial normalization calculations now have separate, self-contained, statement-only unsplit nodes, each with its own source, blueprint ancestry and five actually executed Mathlib searches. They do not transfer the whole item to one child. The proper-comparison node works for every proper map, not only a closed immersion; it does not assert the exceptional Hom or witness conclusion. The presentation-change node works at any chosen compactification and with arbitrary isomorphic left-functor presentations; it does not assert that the proper compact-support comparison is the named direct-image mate and does not construct the parent's particular origin witness. Both are needed in the assembly, since the second lemma's B is only identified with delta by the first. No new node contains proof steps or a proof sketch inside its statement.

Old steps 1 and 2 remain as explicit coefficient, geometry and domain checks. Old step 3 is the proper-comparison child. Old step 4 is the presentation-change child, the parent's direct-image domain check and the closing definitional identification with the existing boundary Hom map. Thus no mathematical work is discarded. The exact old steps are reproduced below, including all their cited dependencies, so the independent reviewer can check the transfer sentence by sentence.

## Review by Q17

I read the current chapter sec-six-functors and unit sk-prop-sf-biduality-general, the three levels in SETUP.md, GOAL.md, the worker contract, stage-1 document, and both copies of delivery-errors sections B--E. This repair stays below the unit route: it computes the closed-counit site transport needed by lem-coef-finite-dualizing through lem-coef-site-closed-counit-transport. The blueprint ancestry search gives lem-coef-finite-dualizing; each new node's via list starts with this item and then its parent. I read the main-20261015 finite-dualizing proof, especially its closed-counit followed by affine-space-counit paragraph, and the complete thm-sf-ambient-adjoint-class proof, especially the displayed Hom chain and its warning that the final arrow is full faithfulness. No SGA source is used.

For parent step 1 I opened all five cited statements. def-weil-l-adic-coefficient-extension explicitly makes the quotient finite for n >= 1. lem-weil-pbc-closed-immersion-proper(a) gives properness; pqf-lem-proper-basic gives exactly separated finite type and qcqs. lem-kun-dimension-finite-type states finite Krull dimension for finite type over a field, allowing a nonnegative finite bound, with bound zero for the empty scheme. def-weil-finite-type-morphism includes quasi-compactness of the structure map, so the affine field base gives quasi-compact P. These are exactly the field, coefficient, compactification and target hypotheses needed later. I retained this argument rather than making an elementary geometry-bundle node.

For parent step 2 I opened thm-weil-pbc-site-comparison, def-sf-comparison-derived-pullback, and def-weil-pbc-etale-origin-witness. The theorem states invertibility of the actual unit on all D+ constant-finite-ring complexes, not only constructible objects. Applying I to that isomorphism is legal even without a global lower-bound preservation assertion for I; the hypothesis IH in D+ gives the lower bound at this particular input. Exact comparison preserves D+ by the definition's explicit last paragraph. The witness definition retains the pair, in the direction S_Z IH to J S_P H. Its inverse is S_Z I(eta_H inverse); no unrelated isomorphism replaces alpha. This step is elementary functoriality of isomorphisms plus the cited typing facts.

For parent step 3 I read the entire new proper-comparison statement. It supplies precisely S_P(e) C q^{-1} = b^{-1}, where e and q are the same degreewise canonical identity-open identifications. The parent's closed immersion is proper by step 1, so this applies with f=i. The named b is the parent's delta by its counit-mate definition. No theorem about merely the existence of an endpoint isomorphism is being used to identify a map. The child's source is the displayed compact-support factor in the main blueprint, with Stacks Tag 09AF, proetale.tex lemma-jshriek-comparison; I read that lemma and its proof and the complete statements of def-sf-compact-support-site-comparison-construction, lem-sf-class-compact-support-comparison, lem-cbc-proetale-extension-zero-comparison, cor-cbc-proper-coincidence, and lem-weil-pbc-comparison-direct-image-canonical-mate. The latter theorem was inspected as a nearby normalization but is not cited, since the first dry run revealed its downstream dependency cycle. The extension-by-zero definition nodes themselves fix the canonical identity identifications.

The proper child retains old step 3's argument: after removing identity extension, the canonical sheaf open factor e has e=e composed with e by composition compatibility at id composed with id. Its invertibility gives e=1 by cancellation. Termwise descent preserves that equality. Expanding the specified compact-support construction then leaves the proper factor b, fixed by its ordinary pullback/direct-image counit. The ambient comparison is the inverse bounded-below composite, hence the displayed b^{-1}, with its inclusion and associator identifications. This is the specific map equality, not a chosen adjunction obtained from the existence of an isomorphism.

For parent step 4 I read the entire new presentation-change statement and both other cited statements. With G=L, M=S_P H, and the two canonical identity-open presentations, the etale right adjoint is identified through its counit, just as the parent requires. FG is bounded below by the module-coefficient paragraph of def-weil-pbc-direct-image; M and IU_PM are bounded below by step 2. Its r is the parent's stipulated identification and its B becomes delta by step 3. The child therefore gives exactly all four displayed factors and their bijectivity. The boundary-comparison definition states those same four operations, without asserting bijectivity; I use it only for equality of the defined formula. I do not cite its definition for a theorem about adjoints.

For the presentation-change child's source I read the same four-factor blueprint chain, the finite paragraph of def-weil-exceptional-inverse-image, and the concrete retained-witness Hom construction. I also read categories.tex Tag 0B65, lemma-transformation-between-functors-and-adjoints, for the counit relation, and Mathlib Adjunction/Basic.lean:497--518 and Unique.lean:112--139. The child changes both left-functor presentations and the actual etale right adjoint; the existing bounded-site transpose node fixes those presentations and does not give this coordinate-change equation.

The argument transferred to that child is explicit: put N=U_Y M and t=g q C^{-1}. The original specified chain gives S_X(beta_c(U_Y(t) eta_{F_cG})), with no conjugation from the identity witness. Under e, unit naturality gives
U_Y(t S_Y(e_G^{-1})) eta_{FG} = U_Y(t) eta_{F_cG} e_G^{-1}.
The counit-compatible equation for r, tested by the etale adjunction inverse, gives
beta(U_Y(t) eta_{F_cG} e_G^{-1}) = r_N beta_c(U_Y(t) eta_{F_cG}).
Applying S_X gives the child's displayed equation. Each operation is bijective: B is an isomorphism, the next two are the specified adjunctions, and full faithfulness applies to G and I U_Y M, both explicitly assumed D+. The target I_c U_Y M has the same bound through r^{-1}. Naturality follows from those same fixed transformations. This keeps every operation and domain check of old step 4, with the previously implicit change-of-presentation calculation made separately available to another worker.

I tested H=0 and L=0 (all morphisms are the unique zero maps), Z empty (bound zero, derived categories trivial), i=id (identity-open comparisons reduce canonically, and any nontrivial adjunction choice is still tracked by r), n=1 (finite residue coefficient), and positive-dimensional proper maps for the generalized first child. For the second child, arbitrary nonidentity e and q are essential tests: q enters the input and B in the same direction, e^{-1} enters B, and r has direction I_c to I. Its counit equation and the naturality equation above have matching sources and targets. There is no assertion about unbounded pro-etale Hom classes, all-sheaf pro-etale cohomological dimension, constructible-only equivalences, or embeddings of E in a fixed algebraic closure.

I checked all new statements for self-containment, single-escaped TeX, explicit definitions and hypotheses. The parent statement is byte-for-byte unchanged. New proofs and proof_deps are empty with proof_origin null. Parent proof_deps is exactly the union of uses. All parent citations have verbatim quotes in citations.json. No parent proof step exceeds 2000 characters. The two new results spread the two normalization arguments requested by the human; elementary unit/domain checks remain steps. I checked existing DAG/blueprint/source results before creation; distinctions are below. No difficulty in the unit route was treated as a mathematical error.

## Mathlib and duplicate searches

I ran tools/blueprint_refs.py ancestor on the item and searched the entire imported blueprint for compact-support comparison, Hom bijection, identity-open, relative Hom, counit-compatible, Hom chain, Hom presentation and identity-open comparison. Whole-DAG searches covered identity-open, four-factor, presentation/adjoint and canonical mate language; source searches covered the exact id and new ids plus the actual specified Hom/comparison names. Existing nodes were read before creating either new node. The searches produce nearby normalization and transport nodes, not either full new statement. The new ids were absent.

For each new node I ran leanfinder twice with different phrasing, leansearch, loogle, and grep using the required launcher msearch.py; all returned successfully. The exact queries and result digests are retained unmodified in searches.jsonl and recorded in each node. Semantic results largely concerned condensed adjunctions and scheme-module open restriction. The proper grep found no site-comparison construction. The presentation grep found generic rightAdjointUniq_hom_app_counit and restrictFullyFaithful_homEquiv_apply. I read the relevant source. None states the equality between the specified derived site Hom bijections with the simultaneous e,q,r changes. The generic individual formulas are future proof ingredients, not one-line Mathlib specializations of either new node. There are two new unsplit nodes and zero new Mathlib leaves.

## Not duplicates

lem-coef-proper-identity-open-site-comparison vs cor-cbc-proper-coincidence: that node supplies the canonical identity-open identifications and proper exchange normalization; it does not identify the compact-support site comparison with the named direct-image mate inverse.
lem-coef-proper-identity-open-site-comparison vs lem-pod-identity-compact-support-normalization: the existing node normalizes identity compact support on the coefficient point at all stages, whereas the new node compares the two sites for arbitrary proper maps at finite level.
lem-coef-proper-identity-open-site-comparison vs lem-sp-finite-compact-site-coherence: that node proves refinement/composition compatibility of the forward comparison, not the specific identity-open equality with b^{-1} after removing the identity extensions.
lem-coef-relative-hom-change-of-presentation vs lem-pur-bounded-site-adjunction-transpose: the existing node fixes F_e,F_p,f^times and B for one compactification; the new node tracks arbitrary isomorphic F,Q, a separately specified adjunction F right-adjoint I, and the counit-compatible r in the Hom equality. It is not a special case of the existing fixed-presentation formula.
lem-coef-relative-hom-change-of-presentation vs lem-sf-fully-faithful-exceptional-hom-transport: the abstract node defines an independent four-factor h for globally fully faithful functors; it does not identify the existing relative site Hom construction after presentation changes in bounded subcategories and with r.
lem-coef-relative-hom-change-of-presentation vs lem-sf-locally-closed-relative-transpose-normalization: that node compares ambient pro-etale adjunctions for a locally closed immersion under additional gamma and factorization assumptions; the new node requires none of those and computes arbitrary presentation changes at any compactification.
lem-coef-relative-hom-change-of-presentation vs det-sp-et-proet-adjunction-transfer: the existing node is on constructible finite-Tor subcategories with chosen equivalence quasi-inverses and an ambient Brown adjoint; the new one is the specified bounded etale-origin relative construction with Rnu_* and arbitrary left-functor presentations.

lem-coef-proper-identity-open-site-comparison vs def-sf-compact-support-site-comparison-construction: defines the composite, but does not prove that its canonical identity-open factor is the identity or the resulting equality with the named mate inverse.

lem-coef-proper-identity-open-site-comparison vs lem-trf-open-base-change-site-transport: normalizes a Cartesian open base-change square, not the proper identity-open compactification comparison.

lem-coef-proper-identity-open-site-comparison vs lem-trf-proper-open-site-transport: normalizes finite proper/open interchange in a Cartesian square, not this identity-open compact-support comparison.

lem-coef-proper-identity-open-site-comparison vs sk-lem-uniform-constructible-ext: the existing node concerns Uniform Ext bound; it does not state the derived proper identity-open compact-support comparison equals the named counit-mate inverse.

lem-coef-proper-identity-open-site-comparison vs det-ctf-finite-comparison-localizing: the existing node concerns $\nu_X^*$ identifies the localizing closures; it does not state the derived proper identity-open compact-support comparison equals the named counit-mate inverse.

lem-coef-proper-identity-open-site-comparison vs det-proper-heart-bound-torsion: the existing node concerns The torsion bound over a weakly contractible base; it does not state the derived proper identity-open compact-support comparison equals the named counit-mate inverse.

lem-coef-proper-identity-open-site-comparison vs det-uniform-constructible-ext-torsion: the existing node concerns The torsion stratum bound; it does not state the derived proper identity-open compact-support comparison equals the named counit-mate inverse.

lem-coef-proper-identity-open-site-comparison vs def-pur-finite-site-coordinates: the existing node concerns Finite Tate site comparison coordinates; it does not state the derived proper identity-open compact-support comparison equals the named counit-mate inverse.

lem-coef-proper-identity-open-site-comparison vs lem-sp-open-scalar-site-coherence: the existing node concerns Open extension scalar/site square on flat models; it does not state the derived proper identity-open compact-support comparison equals the named counit-mate inverse.

lem-coef-proper-identity-open-site-comparison vs lem-sf-open-comparison-tensor-normalization: the existing node concerns Tensor compatibility of the etale/pro-etale open-extension comparison; it does not state the derived proper identity-open compact-support comparison equals the named counit-mate inverse.

lem-coef-proper-identity-open-site-comparison vs def-pur-finite-site-tensor-projection: the existing node concerns Finite-site tensor and projection coordinates; it does not state the derived proper identity-open compact-support comparison equals the named counit-mate inverse.

lem-coef-proper-identity-open-site-comparison vs lem-sf-proper-open-comparison-site-normalization: identifies the proper/open refinement transformation alpha under site comparison, not C at the identity-open compactification.

lem-coef-proper-identity-open-site-comparison vs def-pur-proetale-affine-line-counit: the existing node concerns Restricted pro-etale affine-line counit; it does not state the derived proper identity-open compact-support comparison equals the named counit-mate inverse.

lem-coef-proper-identity-open-site-comparison vs def-pur-supported-projective-site-arrows: the existing node concerns Supported Kummer projective-line arrows; it does not state the derived proper identity-open compact-support comparison equals the named counit-mate inverse.

lem-coef-proper-identity-open-site-comparison vs lem-sp-varying-ring-graph-summand: the existing node concerns Graph-supported comparison for semilinear sum extension; it does not state the derived proper identity-open compact-support comparison equals the named counit-mate inverse.

lem-coef-proper-identity-open-site-comparison vs def-pur-vector-tensor-site-equations: the existing node concerns Canonical tensor integration comparison equations; it does not state the derived proper identity-open compact-support comparison equals the named counit-mate inverse.

lem-coef-proper-identity-open-site-comparison vs def-pur-proetale-frame-integration: the existing node concerns Local pro-etale vector integration on a frame; it does not state the derived proper identity-open compact-support comparison equals the named counit-mate inverse.

lem-coef-proper-identity-open-site-comparison vs def-pur-proetale-ordered-integration: the existing node concerns Ordered pro-etale affine integration; it does not state the derived proper identity-open compact-support comparison equals the named counit-mate inverse.

lem-coef-proper-identity-open-site-comparison vs def-pur-open-site-comparison-arrows: the existing node concerns Derived open-extension and restriction site comparisons; it does not state the derived proper identity-open compact-support comparison equals the named counit-mate inverse.

lem-coef-proper-identity-open-site-comparison vs lem-exc-etale-origin-open-restriction-transport: transports normalized open restriction, not identity-open compact support for a proper morphism.

lem-coef-proper-identity-open-site-comparison vs def-pur-proetale-projection-integration: the existing node concerns Canonical proper integration counit; it does not state the derived proper identity-open compact-support comparison equals the named counit-mate inverse.

lem-coef-proper-identity-open-site-comparison vs def-pur-proetale-vector-integration-arrows: the existing node concerns Canonical vector projection and integration arrows; it does not state the derived proper identity-open compact-support comparison equals the named counit-mate inverse.

lem-coef-proper-identity-open-site-comparison vs lem-amb-compact-support-open-factor: normalizes the open base-change factor in a Cartesian square, not the identity-open proper compact-support comparison.

lem-coef-proper-identity-open-site-comparison vs def-pur-proetale-projective-coefficient: the existing node concerns Projective tensor source comparison; it does not state the derived proper identity-open compact-support comparison equals the named counit-mate inverse.

lem-coef-proper-identity-open-site-comparison vs lem-amb-open-site-evaluation-counit: computes the derived open evaluation counit, not the proper identity-open compact-support comparison.

lem-coef-proper-identity-open-site-comparison vs lem-pur-vector-integration-site-comparison: the existing node concerns Finite-level site comparison of normalized vector-bundle integration; it does not state the derived proper identity-open compact-support comparison equals the named counit-mate inverse.

lem-coef-proper-identity-open-site-comparison vs lem-pur-open-projection-site-transport: the existing node concerns Site transport of the normalized open tensor projection and its inverse; it does not state the derived proper identity-open compact-support comparison equals the named counit-mate inverse.

lem-coef-proper-identity-open-site-comparison vs lem-amb-compact-support-proper-factor: normalizes the proper base-change factor in a Cartesian square, not the removal of identity extension in compact support.

lem-coef-proper-identity-open-site-comparison vs def-pur-supported-projective-chern: the existing node concerns Supported projective-line Chern arrow; it does not state the derived proper identity-open compact-support comparison equals the named counit-mate inverse.

lem-coef-proper-identity-open-site-comparison vs lem-amb-compact-support-site-comparison-open: commutes a compactified site comparison with target-open restriction, not with removal of identity extension.

lem-coef-proper-identity-open-site-comparison vs lem-sf-open-comparison-unit-normalization: states the open-adjunction unit normalization of the sheaf comparison; the new statement includes the derived proper factor, both identity-open presentations and the inverse compact-support comparison.

lem-coef-proper-identity-open-site-comparison vs def-pur-proetale-vector-integration: the existing node concerns Pro-etale vector integration and its adjoint arrows; it does not state the derived proper identity-open compact-support comparison equals the named counit-mate inverse.

## What could not be finished

Nothing remains in the stage-1 split. The two new lemmas intentionally have statement-only unsplit status so independent workers can prove them. The first delivery dry run exposed a cycle through cor-cbc-proper-coincidence, whose downstream six-operation exchanges depend back on the item. I removed that unnecessary statement dependency. The canonical e and q are now defined directly by the sheafification identity-extension identifications of def-weil-pbc-extension-by-zero and def-weil-extension-by-zero, degreewise, with derived associators. This keeps their actual maps fixed and does not import a downstream theorem. The final checks and delivery follow this repair.

## Returned proof retained verbatim and transfer map

### Old step 1

The coefficient construction [def-weil-l-adic-coefficient-extension] makes $R$ a finite commutative ring. The closed immersion $i$ is proper by [lem-weil-pbc-closed-immersion-proper](a), hence separated, of finite type, quasi-compact and quasi-separated by [pqf-lem-proper-basic]. Thus $c=(\mathrm{id}_Z,i)$ is a compactification and the named qcqs direct-image mate applies. Since $Z$ is finite type over the field $k$, [lem-kun-dimension-finite-type] gives an integer $d\geq0$ with $\dim Z\leq d$ (take $d=0$ when $Z$ is empty). This checks the geometric and coefficient hypotheses of the bounded comparison-class adjunction used in Step 4. Also $P$ is quasi-compact: its structure map has affine target $\operatorname{Spec}k$ and is quasi-compact by [def-weil-finite-type-morphism], whose definition includes this condition in finite type. This checks the proper-case Hom-map definition used below.

Citations: def-weil-l-adic-coefficient-extension, lem-weil-pbc-closed-immersion-proper, pqf-lem-proper-basic, lem-kun-dimension-finite-type, def-weil-finite-type-morphism.

### Old step 2

By [thm-weil-pbc-site-comparison], the actual unit $\eta_H:H\to U_PS_PH$ is an isomorphism. Applying the functor $I$ gives an isomorphism $I(\eta_H):IH\to IU_PS_PH$, with inverse $I(\eta_H^{-1})$: their two composites are identities by functoriality. Therefore $IU_PS_PH$ has the same lower cohomological bound as the assumed bounded-below object $IH$. Applying $S_Z$ gives the isomorphism $\alpha_H$, with inverse $S_ZI(\eta_H^{-1})$. The exact derived pullback [def-sf-comparison-derived-pullback] preserves bounded-below objects, so $S_ZIH$ and its isomorphic target $JS_PH$ are bounded below; likewise $S_PH$ and $S_ZL$ are bounded below. The pair $(IH,\alpha_H)$ is now precisely the retained etale-origin witness of [def-weil-pbc-etale-origin-witness]. No boundedness theorem for $I$ on other inputs has been assumed.

Citations: thm-weil-pbc-site-comparison, def-sf-comparison-derived-pullback, def-weil-pbc-etale-origin-witness.

### Old step 3

Let $C_{c,L}:QS_ZL\to S_PFL$ be the comparison of [lem-sf-class-compact-support-comparison] at the identity witness. Its construction is explicitly fixed in [def-sf-compact-support-site-comparison-construction]: the forward comparison is first the proper counit mate, then the direct image of the exact open-extension comparison, with the canonical associators; $C_{c,L}$ is its inverse. Here the open factor is the identity. To check its map, let $e$ be its component after the canonical identifications of identity extension with the identity functor. Compatibility with composition in [lem-cbc-proetale-extension-zero-comparison], applied to $\mathrm{id}_Z\circ\mathrm{id}_Z$, gives $e=e\circ e$. Since $e$ is invertible, cancellation gives $e=1$. The descended termwise comparison is therefore also the identity. The forward compact-support comparison consequently reduces to $b_{i,L}$ of [lem-weil-pbc-comparison-direct-image-canonical-mate], whose defining transpose is the comparison pullback followed by the etale direct-image counit. This is exactly the named $\delta_L$, not a newly chosen isomorphism. Its inverse is $C_{c,L}=\delta_L^{-1}$. The same canonical inclusion identifications are used on both sides.

Citations: lem-sf-class-compact-support-comparison, def-sf-compact-support-site-comparison-construction, lem-cbc-proetale-extension-zero-comparison, lem-weil-pbc-comparison-direct-image-canonical-mate.

### Old step 4

Unpack the stipulated relative Hom bijection of [thm-sf-ambient-adjoint-class] at the identity witness $(L,1)$ and at $c=(\mathrm{id}_Z,i)$. Its form is fixed in [def-weil-exceptional-inverse-image]: the etale adjunction transported by the compact-support comparison, followed by full faithfulness of $\nu^*$ on $D^+$. Since $J=S_ZIU_P$, passing from $S_PFL$ to the etale adjoint goes through the comparison adjunction $S_P\dashv U_P$, and the etale adjunction is $F\dashv I$ by the counit-compatible identification stipulated in the item. So the bijection precomposes with the inverse of the compact-support comparison $C_{c,L}$, applies the comparison adjunction, then $\beta$, then $S_Z$. Step 3 gives $C_{c,L}^{-1}=\delta_L$. For $g:QS_ZL\to S_PH$ these operations therefore give
$$g\longmapsto g\circ\delta_L\longmapsto U_P(g\circ\delta_L)\circ\eta_{FL}\longmapsto\beta_{L,U_PS_PH}\!\left(U_P(g\circ\delta_L)\circ\eta_{FL}\right)\longmapsto S_Z\!\left(\beta_{L,U_PS_PH}\!\left(U_P(g\circ\delta_L)\circ\eta_{FL}\right)\right).$$
Each arrow is bijective: Step 3 gives the inverse to the first; the next two are the comparison adjunction and $F\dashv I$ of [lem-exc-closed-ambient]; the last is full faithfulness of [thm-weil-pbc-site-comparison], since $L$ and $IU_PS_PH$ are bounded below. Also $FL$ is bounded below by the module direct-image construction [def-weil-pbc-direct-image], so every intermediate Hom is in the stated comparison domain. The unit formula for the second arrow is the defining adjunction formula. The identity origin witness inserts no conjugating arrow. The same four operations define the map $h_{L,S_PH}$ of [def-weil-boundary-exceptional-comparison-data] for $Z\to P$ (its hypotheses were checked in Step 1, and its mate $b$ is the mate defining $\delta_L$). Thus this is exactly the specified bijection, with all four factors retained, rather than a different bijection deduced from right-adjoint uniqueness.

Citations: thm-sf-ambient-adjoint-class, def-weil-exceptional-inverse-image, def-weil-boundary-exceptional-comparison-data, lem-exc-closed-ambient, thm-weil-pbc-site-comparison, def-weil-pbc-direct-image.

Destinations: old steps 1--2 remain parent steps 1--2; old step 3 is the proper identity-open comparison child, invoked in parent step 3; old step 4 is the presentation-change child, invoked in parent step 4, with the direct-image typing and boundary-definition closing check kept in that assembly step.
