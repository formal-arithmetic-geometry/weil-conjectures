## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-regular-gysin-calculus.json`: item, split into twelve steps; live statement unchanged.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-immersion-class-calculus.json`: statement-only supported regular-immersion class, including flat pullback without regularity of the schemes; Mathlib no match.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-smooth-immersion-interchange.json`: statement-only smooth-square and section identities; Mathlib no match.
- `citations.json`: verbatim statement excerpts for every node cited in each item step, numbered from one.

The previous five-node draft, report and citations are retained in `previous-attempt/` in this sandbox. Its raw search results and `searches.jsonl` remain intact. Three uncommitted proposed nodes were removed from the delivery tree after finding overlapping existing nodes. Both retained nodes have the old searches plus new searches for their refined statements, with the actual command output preserved in `search-results/`.

## Attachments

None. I searched the read-only slopmaster2 `WeilConjectures/` tree for `lem-per-regular-gysin-calculus`, Gysin/gysin and absolute-purity terminology. There is no project declaration stating all clauses of the item. The existing smooth Kummer declarations take orientation data as parameters and are not this theorem.

## WANTED

None.

## Problems and repairs

The required initial dry run failed on all five proposed nodes because their citations were grouped in one bracket. The refined nodes use individual bracketed node references.

The saved proof also had substantive defects: the immersion class was given the positive twist/shift instead of the negative one, several new nodes overlapped the existing `lem-per-absolute-gysin-purity`, the broad interchange node simply delegated independence and composition, and the purely inseparable node repeated the last clause. The saved proof called every localization an open restriction, which fails for a generic-point inclusion. The new proof gives the correctly typed composite, uses existing purity and local algebra, proves independence by the product-refinement/section calculation, and proves composition using the affine-space cartesian square. General localization now uses the existing localization/continuity clause. The field-degree clause is proved using existing degree-p towers and the supported Cartier calculation on the projective line. No change to the live item statement is needed; the errors were in the saved attempted split.

The proof origin is marked agent: it adapts the explicit diagrams in ILO to the fixed diagonal/DNC orientation. The smooth input is `lem-per-ordinary-smooth-orientation`, from Scholze Theorem 7.19. No SGA source is used for smooth purity. ILO XVI is used for the regular-immersion classes, the two comparison identities and the diagrams; XVII is used for the regular-base-change and degree-normalization assertions.

## Not duplicates

lem-per-immersion-class-calculus vs lem-per-absolute-gysin-purity: the existing node supplies purity isomorphisms only between regular affine schemes; the new node is a supported morphism on possibly singular or nonreduced schemes, with flat pullback, and asserts no purity isomorphism there.

lem-per-immersion-class-calculus vs lem-asd-ordinary-supported-kummer: the existing node treats one Cartier divisor; the new node treats arbitrary-length regular sequences, independence of the flag, and their flat pullback.

lem-per-immersion-class-calculus vs prop-pur-regular-immersion-purity-compatibilities: the existing statement requires the smooth-over-a-field purity setting and its coefficient conventions; the new statement concerns ordinary F_ell supported classes without a smooth-over-a-field hypothesis, including singular pairs and flat pullback.

lem-per-smooth-immersion-interchange vs lem-per-absolute-gysin-purity: the existing node supplies canonical Gysin isomorphisms and their composition; the new node compares the separately specified diagonal/DNC smooth orientation with an immersion class in a cartesian square and at a section. The item's independence proof performs the refinement and algebra with these two identities.

lem-per-smooth-immersion-interchange vs lem-per-ordinary-smooth-orientation: the existing smooth orientation statement gives composition of smooth maps and base change; the new node relates that smooth orientation to regular-immersion supported classes and cancels a section.

lem-per-smooth-immersion-interchange vs prop-pur-regular-immersion-purity-compatibilities: the latter concerns the perfect-field smooth-pair setting and does not state either displayed mixed square/section identity for arbitrary regular excellent affine schemes with ordinary F_ell coefficients.

I searched the entire DAG by regular-immersion, Gysin, absolute-purity, Kummer, section and source-place terminology, and searched the whole blueprint with `tools/blueprint_refs.py search` for Gysin, absolute purity, regular immersion, section, Kummer and flat pullback. I read the candidate statements, including the regular-immersion and frame nodes in the smooth-purity chapter; their hypotheses or coefficient sites differ as above. The nearest blueprint ancestor is `lem-per-artin-gabber-affine-curve`. Both new nodes include the item itself in `from.via` followed by the existing ancestry. Neither new statement is a blueprint node in another form.

## Review by Q11

I read ILO XVI Definitions 2.3.1 and 2.5.1–2.5.6, Theorem 2.3.2, Proposition 2.2.3.1, Lemmas 2.5.7–2.5.10, the proof of Theorem 2.5.12, and Theorem 3.1.1/Corollary 3.1.2. For the two new nodes these are respectively the supported class/flat-pullback source and the two mixed identities. I also read XVII's proof of Proposition 2.4.3.3, especially the finite purely inseparable degree sentence, and Lemma 4.3.1.2. For the actual smooth input I read Scholze Theorem 7.19 and its diagonal first-Chern-class proof and DNC identification paragraph. This keeps the smooth normalization in the lecture-notes route.

Step 1 checks a gap in the earlier draft's geometry: existence of some lci factorization does not imply that an arbitrarily chosen closed embedding is regular. I read the statements for smooth-ring affine equivalence, smooth ascent of regularity, excellent finite-type/localization permanence, regular-local quotient kernel parameters, regular parameters being a regular sequence, and spreading a sequence to a principal neighbourhood. Their hypotheses hold for our regular Noetherian affine rings. Finite generation of the ideal permits the explicit denominator shrinking. Thus the affine-space and product embeddings used later really are regular. The Stacks sources are 00NR, 00NQ, 07NF and the cited spreading lemma. Affine space is supplied by the existing smooth projection node.

Step 2 uses exactly the factorization and immersion purity clauses of the existing absolute-Gysin node, specialized to n=1, and the new supported-class identification. Step 3 displays the entire correctly signed composite and uses the existing ordinary smooth orientation; the compact-support composition statement and the counit characterization of `det-sp-unique-right-adjoint` supply the transitivity identification. Step 4 uses only the two displayed identities of the new interchange node, immersion composition from absolute Gysin, and smooth composition from the smooth orientation. I checked the product diagram and the types of j, q', s: q' is smooth over the regular U, j is the base-changed regular immersion, and s is its section. The written equalities actually derive factorization independence.

Step 5 uses the isomorphism and identity clauses of those same two inputs. Step 6 uses the explicit restriction clauses and, for localizations which are not open immersions, the continuity clause of the existing absolute-Gysin statement. Step 7 follows ILO's composition diagram with affine space: j' is the pullback of j, the vertical projections are smooth, and every ambient scheme is regular. The three displayed products yield the required formula and the additive twist. Step 8 uses flat pullback of the supported class and Noetherian base change of the smooth orientation. It asserts equality under the canonical supported comparison, without assuming an arbitrary exceptional-pullback base-change isomorphism.

Step 9 uses exactly the statements of `lem-per-smooth-local-dimension` and `lem-kun-dimension-formula`, which I opened: the first gives local topological dimension d of the smooth ambient over F, and the second splits d into local-ring dimension plus residue transcendence degree. At the generic point of the closed integral subscheme the local-ring dimension is its immersion codimension c. I checked the Stacks labels 0AFF/lemma-smoothness-dimension and 02FX/lemma-dimension-fibre-at-a-point.

Step 10 uses the existing integral/radicial/surjective assertion for a purely inseparable field inclusion, the universal-homeomorphism criterion, and the etale-topos equivalence. An exact equivalence has the inverse equivalence as right adjoint also after deriving; the unique-right-adjoint statement identifies the counit normalization. The quasi-finite formula in the absolute-Gysin node gives virtual dimension zero for fields. Step 11 uses the supported Cartier statement exactly as written: its composite with the unit is c1 of the divisor line bundle. The homogeneous degree-p equation gives O(p), the Kummer connecting homomorphism gives p times c1(O(1)), and the explicitly normalized smooth integration sends c1(O(1)) to one. The degree-p class is therefore the scalar p under the specified adjunction. Step 12 uses the existing pth-root tower and multiplicativity of field degree, whose statements I opened and read; I also read Stacks 09HI/lemma-finite-purely-inseparable and its proof. Composition and identity normalization complete the arbitrary finite extension and characteristic-zero cases.

The two new nodes have empty proof/proof_deps and introduce all their schemes, maps, coefficients and hypotheses. I read the old recorded search results and the new LeanFinder, LeanSearch, Loogle and grep outputs. Hits on flat preservation of weakly regular sequences are commutative algebra, and the Kummer-named hits concern field extensions; neither states the supported etale class theorem. No match is declared a Mathlib leaf. Services returned responses for the new queries; no unavailable service is recorded as absence. The original searches remain verbatim.

I checked the B–E checklist against the files: each uses entry is a statement I opened, and citations.json quotes it verbatim; no use takes a fact only from a cited proof. The dependencies now supply the omitted local algebra and right-adjoint uniqueness. The new statements have no inline proofs. I removed the three redundant uncommitted nodes and reduced interchange to its two input identities, so the item's steps carry the actual factorization and composition arguments. Generic off-unit tools are declared in split_report.tool_uses for the maintainer's review. Every proof step is under 2000 characters; the maximum is 1164.

Small cases checked: c=0 and d=0, the identity and empty scheme, a divisor c=1 with e=-1 (source Lambda(-1)[-2], concentrated in degree +2), an open restriction, and a generic localization (which need not be open). The supported-class node allows the nonreduced Cartier divisor (t-b)^p after field extension, so it does not accidentally assume a regular base-changed closed subscheme. In the inseparable case p is nonzero modulo ell by the invertibility hypothesis; a tower of length zero gives one. Characteristic zero has L=F. There is no perfect-field assumption in the smooth input.

## Unfinished work

None at the item's one-level split. The two new statement-only lemmas are future stage-1 items. No Lean file was written and no compiler or Lake command was run.
