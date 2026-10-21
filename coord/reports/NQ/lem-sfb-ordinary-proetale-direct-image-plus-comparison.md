# Stage-1 report: lem-sfb-ordinary-proetale-direct-image-plus-comparison

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-ordinary-proetale-direct-image-plus-comparison.json — statement, split into seven proof steps; not a Mathlib leaf.
- citations.json — one verbatim statement quotation for each step/dependency pair.
- report.md — this report.

No new DAG nodes and no new Mathlib leaves. The sandbox also contains the search tool's searches.jsonl and the local write_split.py used to prepare the JSON.

## Attachments

None. I searched lean/WeilConjectures for the exact blueprint tag and for ordinary/pro-etale direct image and K-injective terminology. The closest project construction is AlgebraicGeometry.ProEtale.rightDerivedLowerStarComparisonIso' in SixFunctors/ProEtale/BaseChange/SmoothBaseChange.lean:77. I read its definition, the surrounding bounded-below comparison, and the pro-etale derived UpperLowerStar module. This construction is for externally valued sheaves with coefficient category A. It does not state the full item's identification with intrinsic modules over the constant ring sheaf or the common-right-adjoint normalization. It therefore is not an exact attachment, regardless of the completion state of its prerequisites.

## WANTED

None. All sources used are available in literature/.

## Corrections and scope

The item was unsplit, with no proof. I preserved its statement, its inherited creator search records, and its blueprint ancestry, and supplied its proof. There is no statement dispute or hypothesis change. Finite B is allowed to be zero. No assumption about invertibility of its order, Noetherianity, finite cohomological dimension, bounded-above cohomology, completeness, or constructibility is introduced.

The bounded-below pro-etale operation is the restriction of the ordinary uncompleted functor; def-weil-pbc-proetale-operations itself defines the full ordinary functor. The proof makes this distinction explicit rather than treating that definition as a separate bounded-below comparison theorem. The new argument establishing the normalization uses the existing abstract injective statements. The final comparison is then a specified composite, not an assertion that inverse image preserves injectives.

I read the chapter and unit records. This item is a subsidiary input to the finite-field direct-image argument under lem-sfb-dc-hom-preserves, not the key statement of sk-def-sfb-dc-restricted-functors. It does not change the unit's realized fields. The relevant ancestral blueprint sentence is the finite-coefficient finiteness assertion after reduction modulo the uniformizer; this item supplies the ordinary bounded-below comparison called for by its inherited from.place. No SGA result is used in this proof: the route here is Bhatt-Scholze Lemma 5.4.3 and the Stacks ordinary ringed-site derived construction.

## Searches and reuse

I searched the whole DAG by K-injective, Grothendieck module sheaves, the source tags 070K/070J/099R, bounded-below representatives, and constant-ring module inverse image. I ran tools/blueprint_refs.py ancestor for the item and searches for K-injective, direct-image comparison, and bounded below injective. These found all required inputs already present. In particular, prop-pur-kinjective-resolutions-exist applies to arbitrary small ringed sites, so the pro-etale intrinsic module case needs no new existence lemma. The general comparison already has prop-weil-pbc-comparison-direct-image; it is retained, while this item supplies its ordinary full-derived interpretation. No existing blueprint node states the item's full package, so same_as remains empty.

The six retained sandbox searches run through msearch.py are recorded verbatim in searches.jsonl and appended to the seven inherited creator records in mathlib_searches. All retained query results were reread for this repair; the search questions and item statement have not changed, so no search was repeated. Both semantic phrasings returned generic derived-functor and module-pushforward infrastructure; the Loogle result rightDerivedFunctorPlus and its units was read at Mathlib/Algebra/Homology/DerivedCategory/RightDerivedFunctorPlus.lean:25-68. The grep hits on pro-etale sites were read in Mathlib/AlgebraicGeometry/Sites/Proetale.lean; SheafOfModules.pushforward was read in Mathlib/Algebra/Category/ModuleCat/Sheaf/PushforwardContinuous.lean:42-53. None states the intrinsic etale/pro-etale package or its geometric comparison. All services answered successfully. No absence claim is based on an unavailable service.

## Not duplicates

No new nodes were created. Existing general ringed-site, injective-resolution, and comparison nodes are cited directly rather than duplicated by their scheme-specific specializations.

## Review by NQ

For the item I read Bhatt-Scholze, The pro-etale topology for schemes, Lemma 5.4.3 and Remark 5.4.4, printed page 39. The first gives the bounded-below qcqs comparison; the following remark explicitly prevents claiming its unbounded extension. I also read Stacks derived.tex, labels lemma-K-injective (070I), lemma-bounded-below-injectives-K-injective (070J), lemma-K-injective-defined (070Y), lemma-enough-K-injectives-implies (070K), and lemma-injective-resolutions-exist (013K); sites-cohomology.tex sections section-unbounded (07A5) and section-derived-functors (071J); sites-modules.tex lemma-adjoint-push-pull-modules (03D3) and its module-pullback context; and proetale.tex lemma-morphism-comparison (099R). The Stacks 099R statement alone concerns a sheaf input, so I use the existing bounded-below comparison node and Bhatt-Scholze 5.4.3 for the complex statement. There are no new nodes needing individual source reviews.

For step 1 I opened prop-pur-kinjective-resolutions-exist and lem-sp-grothendieck-enough-injectives. The former explicitly supplies both the Grothendieck property and K-injective resolutions for modules over any commutative ring sheaf on a small site; the latter supplies enough ordinary injectives. The universe-small representatives and B_W satisfy those hypotheses for both sites and both schemes. I did not use the less general etale-only enough-injectives node for the pro-etale site.

For step 2 I opened both direct-image definitions and def-weil-sheaf-of-modules-category. The pro-etale definition explicitly gives the scalar-restriction action and additivity; the etale definition gives the corresponding formula and left exactness. The common proof of left exactness is written out from sectionwise kernels and products, which the module-category node actually states. This is an elementary step, not a new lemma or an uncited appeal to exactness of arbitrary evaluation functors.

For step 3 I opened lem-weil-pbc-kinjective-total-derived and def-sfb-right-derived-functor. Their statements include the total right-derived universal property and invertibility of its unit on K-injectives, not merely existence of resolutions. I checked exactness of the functor on homotopy categories by the explicit shift/cone matrix, using only additivity, not exactness of sheaf direct image. The K-injective existence assumption is provided by step 1. Thus the resolution formula is for the full ordinary derived category.

For step 4 I opened lem-weil-pbc-dplus-injective-representative and lem-weil-pbc-right-derived-plus-injective. The first is for cohomologically bounded-below objects, not just complexes whose terms vanish below a bound, and includes K-injectivity of the resulting injective model. The second gives the bounded-below functor, computation, and its unit, under enough injectives and additivity. These hypotheses were verified in steps 1-2. The image complex has the same lower bound because an additive functor preserves zero. The two operation definitions fix the intended etale and ordinary pro-etale functors.

For step 5 I opened lem-weil-pbc-kinjective-hom-derived and the two unit/computation statements again. The Hom node gives bijectivity from homotopy to derived morphisms into a K-injective, and homotopy equivalence of K-injective models; it is not merely uniqueness of an underived resolution. This proves naturality for all derived morphisms using their unique homotopy classes. For the unit equation on a bounded-below complex I cite lem-sc-bounded-below-injective-resolution-existence, whose statement really gives a quasi-isomorphism from that complex to a bounded-below injective one. I wrote the two naturality equations and the explicit comparison at that model; their cancellation proves unit compatibility. This repairs the potential gap of identifying only the objects Q(f_*J).

For step 6 I opened def-weil-pbc-site-comparison-morphism, lem-pe-coefficient-comparison-data, lem-pe-constant-left-module-inverse-image, and lem-weil-pbc-module-inverse-image-unit-comparison. They give respectively the geometric morphism and sectionwise right adjoint, the intrinsic constant-section presentation, exact constant-ring inverse image, and the normalized module adjunction-unit comparison. Both ring actions are induced by the same scalar sections, so both presentations have the same module right adjoint. I wrote the adjunct formulas and checked each composite by its image under the adjunction bijection. No extra uniqueness-of-adjoints node is necessary for this few-line calculation. This retains the distinction between fixed-scalar and intrinsic sheaf-of-rings presentations until their identification is justified.

For step 7 I opened lem-pe-coefficient-comparison-derived-functor and prop-weil-pbc-comparison-direct-image. The former explicitly descends the actual intrinsic functor termwise and commutes with cohomology, hence preserves bounded-below objects. The latter explicitly states the displayed natural isomorphism for qcqs u and D+ input with the required coefficients. I checked u=f, Lambda=B, L=G, the direction of both theta maps, and the final category D(Y_proet,B). The three-factor formula proves that the arrow is precisely the specified old comparison after the normalizations. It uses neither a claim for unbounded-below etale inputs nor a hidden preservation-of-injectives assertion for nu*.

I checked B=0, the empty scheme, f an identity, and a sheaf in degree zero with shifts. For B=0 the only unital module is zero and all constructions and units reduce to the zero-category isomorphisms. Empty sites/schemes cause the same zero calculations. Identity f gives the usual injective computation of the identity functor, and the comparison reduces to the identity after the unit normalizations. A shifted degree-zero sheaf preserves the expected lower bound; the proof uses no uniform upper bound. The same argument actually allows arbitrary commutative B, but the item's finite hypothesis is retained.

I checked each cited statement, not its proof, against what its step consumes. citations.json copies the full statements verbatim, including every clause used. I checked the transitive dependencies of all additional theorem citations for a path back to this item and found none. Each proof step is below 2000 characters (maximum 1348); no hidden standalone lemma is compressed into a long step. The abstract off-unit inputs and the existing comparison are declared in split_report.tool_uses, with why they are general tools rather than alternative unit routes.

## Unfinished work

None within this one-level split. Existing unsplit dependencies retain their own work; no claims about their Lean proofs are made. The dry run and delivery outcome are recorded below after execution.

## Previous validation

The required server dry run completed successfully: `OK (not pushed)` at be5988d3f47, with server preflight passed. No local DAG checker, compiler, Lake command, or repository git command was run. The final push uses the required delivery tool and reruns its preflight.

## Repair of returned head ae9a1446d52

The return at coord/returns/NQ.md:64 says that the reader approved the split but landing refused the side completion because the live queue still read an unsplit node. I retained the delivered sandbox proof, report, citations, and search history. I compared its item with the current read mirror: statement, statement dependencies, source, blueprint ancestry, creator, chapter and unit agree; the current item remains unsplit with empty proof. Only the split-owned proof, dependencies, proof origin, search additions and split report are supplied. The required delivery tool rebuilds these fields on current origin/sheaf-dag and preserves maintainer fields. The initial repair dry run passed at 68d544123be. This repair is then amended as below and validated again.

I reread all 18 distinct proof-dependency statements in the current DAG and compared all 21 step/node quotations verbatim: none of the statements changed from the retained citations. I also reread the three direct-image definitions, the intrinsic coefficient comparison nodes, and the exact local Lean comparison declaration. The latter still concerns externally valued sheaves and does not supply every clause of this intrinsic-module item, so no attachment is claimed. I rechecked the current blueprint ancestor and the direct-image comparison search; the existing general comparison is reused, and the larger ordinary-derived/unit-normalization package still needs this item.

The current DAG marks five theorem inputs as Mathlib leaves: lem-sp-grothendieck-enough-injectives, lem-weil-pbc-dplus-injective-representative, lem-weil-pbc-right-derived-plus-injective, lem-weil-pbc-kinjective-hom-derived, and lem-sc-bounded-below-injective-resolution-existence. I removed their redundant off-unit tool declarations from split_report.tool_uses; their proof citations remain. This uses their current live classifications without editing those nodes. I reread RightDerivedFunctorPlus.lean and the bounded-below injective-resolution declaration returned by the retained searches.

For step 5 I made the normalized component explicit: at QC it is (R+F(Q+s))^{-1} alpha_J eta_J^{-1} RF(Qs). The two unit naturality identities cancel to theta_QC eta_C = alpha_C. All arrows have target in the full derived category after the stated inclusion; Qs is invertible, and both units are invertible on J because J is bounded-below injective and K-injective. The current cited statements provide exactly those hypotheses. No new lemma is hidden here: this is substitution of the two displayed identities. Step 4 now cites the precise 05TI/05TH source places as well as 013K/070J. I reread those Stacks statements and Bhatt–Scholze 5.4.3 with Remark 5.4.4 from the local PDF. The bounded-below restriction remains essential.

I rechecked C1/C4 for each unchanged step against the current quoted statements, the zero-ring and identity-morphism cases, and the absence of any dependency path back to this item. No statement change, new node, or new Mathlib leaf is needed. The changed step stays below the 2000-character threshold. These are my current checks under the Review by NQ signature above, not an unchanged re-push.

## Repair validation

The amended repair passed the required server dry run: OK (not pushed) at 702616505fa, preflight passed. The delivery tool reruns preflight on the pushed commit after this result is recorded. No local DAG checker, compiler, Lake command, repository git command, or launcher edit has been used.
