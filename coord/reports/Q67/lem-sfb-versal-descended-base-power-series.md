# Worker report

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-versal-descended-base-power-series.json: the item, statement unchanged, split into six proof steps. No Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-split-local-power-series-section-criterion.json: one new statement-only algebra lemma, unsplit. No Mathlib match.
- citations.json: one verbatim statement excerpt for every citation in every proof step.
- searches.jsonl and algebra-search-0.txt through algebra-search-5.txt: actual logged searches and their saved outputs. write_split.py is sandbox-only preparation material, not a project tool.

## Attachments

None. I searched lean/WeilConjectures both for the exact blueprint tag and for the words versal, miniversal, and predeformation, using word boundaries to exclude universal. No declaration of the project states this item. The broader power-series/section search returns punctured-section and coefficient-subring results, not a split complete-local presentation theorem.

## WANTED

None. All proof sources used here are available in literature/stacks-project.

## Problems found and corrected

On resumption the sandbox contained only dispatch marker files: no earlier item copy, report, citations, search log or delivery receipt. No deliver.py process for Q67 and this item was running. I started from the current unsplit live node, retained its statement, all five inherited Q106 Mathlib searches, chapter, unit and complete provenance chain, and appended only searches actually run in this session. There is no stage-1 repair note or Q67 return entry for this item. The source is Tag 06T3, not the existence theorem Tag 06T2: the latter's two minimality conclusions are already assumptions of the item. I did not cite its existence assertion as if it proved a property of an arbitrary specified descent.

The first minimality assumption and (S1) remain in the statement, although the proof after existence uses the second minimality assumption and the given morphism. This is not a statement change. In particular no (RS), representability or coefficient-field embedding is added.

I read the chapter and assigned unit records and the latest blueprint at literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md, paragraph (3). This item is a supporting deformation-theoretic input in the recorded moduli prerequisite chain, not a new route for direct images. tools/blueprint_refs.py ancestor prints a null ancestor for this historical chain; I preserve that null and the whole via list, adding the item at the front for the new node. No unit or chapter record is edited.

## Source error

Tag 06SG (formal-defos.tex, lemma-power-series) says that the canonical quotient map has a "left inverse", but its proof uses a map back that is injective and then proves it surjective by cotangent spaces. Tag 06T3 supplies a section of the quotient map. I avoid the terminological slip by stating the exact right-inverse equation phi_n sigma_n = identity on C/m_C^n. That equation makes sigma_n injective, and cotangent surjectivity makes it surjective; hence phi_n is an isomorphism. A left inverse of the already surjective phi_n would also imply an isomorphism, so the printed statement is not being rejected as false. The new node states precisely the nontrivial section version actually used by the source proof. The item itself has no statement dispute and is unchanged.

## Not duplicates

lem-sfb-split-local-power-series-section-criterion vs lem-sfb-complete-local-cotangent-graded-rigidity: the existing statement gives surjectivity from the absolute cotangent map, and isomorphism only with equality of every graded dimension. The new lemma constructs the split power-series presentation and derives its isomorphism from sections of finite quotients; it assumes no equality of higher graded dimensions and no coefficient-field embedding.

lem-sfb-split-local-power-series-section-criterion vs lem-sfb-complete-local-cotangent-surjectivity: the existing statement is about maps of complete local k-algebras with a common coefficient field and only concludes surjectivity. The new statement works with general complete local rings, including mixed characteristic, and supplies the section criterion for injectivity as well.

lem-sfb-split-local-power-series-section-criterion vs lem-sfb-complete-local-smooth-power-series: the existing lemma assumes a coefficient field k and formal smoothness of a morphism of represented test functors. The new lemma assumes a retraction and quotient sections instead, with no formal-smoothness hypothesis. The sections obtained by versality need not even be B-linear.

lem-sfb-split-local-power-series-section-criterion vs lem-sfb-versal-descended-base-power-series: the new node contains no deformation category, formal object, versality or minimal descent assertion. The item must still obtain a retraction, select its kernel basis, build quotient sections by versality, and establish descended versality. The new node is an independent algebraic lemma, not the item or a clause of it.

The whole DAG was searched for Tag 06SG, lemma-power-series, cotangent-surjectivity, surjective endomorphisms and power-series sections before the node was written. No node has source Tag 06SG. Whole-blueprint searches for 06SG, descends-versal, split complete, cotangent, power series and power-series.*section found no equivalent statement; same_as is therefore empty. The broad versal search was also read and contains universal-homeomorphism and other substring matches, not a duplicate of this assertion. Existing power-series evaluation nodes give evaluation maps but neither this split-kernel presentation nor the quotient-section criterion.

## Mathlib searches

For the item I ran a new semantic LeanFinder query, a separately phrased LeanSearch query, Loogle on MvPowerSeries and IsLocalRing, and a source grep for predeformation/versal/miniversal. The hits give Weierstrass preparation, general ring formal smoothness, the power-series local-ring instance, or weak universal properties. None states the formal-deformation theorem. The inherited five Q106 searches are kept as historical records, not asserted to be new Q67 calls.

For the new node I ran two differently phrased LeanFinder queries, LeanSearch, Loogle on MvPowerSeries and bijective, and two source greps of RingTheory/MvPowerSeries. All services answered. Loogle returned no hit. The first grep was polluted by Lean section declarations, so I made a narrower second grep and read its six hits. It locates MvPowerSeries.isNoetherianRing at Equiv.lean:225 and the zero-variable C_surjective at Basic.lean:368; neither is the new lemma. I opened Equiv.lean:215-229 and the local-ring instance at Inverse.lean:152. The semantic results concern Weierstrass quotient equivalences, Henselian completeness, finite submersive presentations, cotangent modules of algebra extensions and ordinary algebraic formal smoothness. I also read Smooth/AdicCompletion.lean:80-109, including exists_mkₐ_comp_eq_of_isAdicComplete, whose hypothesis is an algebraically formally smooth algebra, not our quotient-section criterion. None is an exact match or one-line specialization. No leaf is claimed.

All new-node queries are copied exactly from the actual searches.jsonl records. The raw result file for each query is associated by its query text, rather than by concurrent completion order. An unavailable service is never recorded as a negative result; there was no unavailable search in this session.

## Review by Q67

I read formal-defos.tex at Tags 06T2 (lemma-smallest-where-descends-versal), 06T3 (lemma-descends-versal), 06HT (lemma-versal-object-quasi-initial), 06SG (lemma-power-series) and 06GZ (lemma-surjective-cotangent-space), and algebra.tex at Tag 06RN (lemma-surjective-endo-noetherian-ring-is-iso). I checked their labels against stacks-project/tags/tags. The item retains exactly the specified descent and the two minimality properties of the source, over a Noetherian base with a finite marked residue field. The new node spells out the ambient split complete-local algebra construction and the quotient-section lemma from 06SG. Its statement introduces B, C, their residue field and maximal ideals, i, rho, I, the basis, S, phi, the quotients and the section equation. Its proof and proof_deps are empty, and no proof sketch is inserted into its statement.

Step 1 uses the statement of lem-sfb-versal-formal-object-quasi-initial, which I opened: it gives a morphism from a specified versal formal object to every specified formal object over a complete local algebra. Its finite-residue-field hypothesis is precisely the item's hypothesis. Applying it to xi and eta gives f:C to B. Composing the actual formal morphisms gives eta to eta over fi. The item's incoming-map hypothesis applies to that composite, so fi is surjective. It is not an unjustified inference that f alone is a retraction.

Step 2 cites only the Noetherian definition, whose statement says every ideal is finitely generated. The proof writes the finite-generation-of-the-union argument giving kernel stabilization and the preimage calculation proving injectivity. This is the two-line kernel-chain proof of 06RN, not a hidden module-endomorphism theorem; fi need not be B-linear as an endomorphism of B. Its inverse is an R-map because fi is an R-map. Consequently rho=(fi)^(-1)f is a local residue-preserving R-retraction of the original inclusion. The additive splitting is written out; no compatible formal-object morphism over the normalized rho is claimed.

Step 3 uses the same Noetherian definition to see that finitely many generators of I span I/m_C I. A maximal independent sublist gives the finite basis. I then checked the new algebra node's entire construction clause: it explicitly provides completeness and Noetherianity of S, the local coefficient-compatible evaluation map and surjective Artinian quotient maps. Those are actual conclusions of that statement, not facts borrowed from its unwritten proof. The coefficient map is the original i; no new B-structure is substituted. The quotient rings with their induced R-structures are the test objects needed in the next step.

Step 4 cites the definition node def-sfb-artin-deformation-test-category, which I opened. Its last paragraph explicitly gives versality for every test-algebra surjection and every specified comparison isomorphism, not merely essential surjectivity on isomorphism classes. The morphism eta to xi gives the required comparison of y_n over S/m_S^n with xi over C/m_C^n through the same B to C map. Applying that definition produces h_n with the exact ring equality phi_n h_n = quotient. The factorization through C/m_C^n follows from locality and the literal equality m_(S/m_S^n)^n=0. This short application of the definition is marked elementary. Crucially no B-linearity of h_n or sigma_n is used, and there is no assumption that sections for different n are compatible.

Step 5 cites the new node's final clause, which states precisely that the right-inverse equations for sufficiently large n force phi to be an isomorphism. We have them for every positive n. Its local and marked-residue assertions were provided in the construction clause, so all clauses of the power-series conclusion hold for the original inclusion.

Step 6 again uses only the explicit versality definition. I checked a general lifting problem with its specified isomorphism, extended the B to A map by composing with the ring retraction rho, applied versality of xi and restricted the lifted C to D map along i. The given formal morphism identifies the evaluations of eta and xi. On reduction the two occurrences of that same comparison cancel, so the resulting isomorphism extends the originally specified one. This proves versality directly and does not invoke an uncited general smoothness-descent theorem. This direct diagram chase is elementary after the cited definition.

For the new algebra node, I tested r=0 and I=0, where S=B and the conclusion allows the identity presentation; B=l and C=l[[t]], where the standard section exists; and B=l, C=l[e]/(e^2), where the kernel basis has one element but the section hypothesis fails at n=3. In the last case any lift of e to l[T]/(T^3) with the required linear coefficient has nonzero square T^2, so no ring section exists, in every characteristic. This prevents the false conclusion that every split complete-local algebra is a power-series algebra. Mixed characteristic is allowed: B=Z_p and C=Z_p[[t]] satisfy the statement, and neither is required to contain its residue field. Quotient sections may vary with n; the conclusion follows through the canonical phi_n, whose inverse limits are already compatible once each is an isomorphism.

I checked the item on the constant deformation groupoid (minimal base forces the incoming surjectivity condition), on a minimal versal base itself, and with no free variables. No coefficient-field section, equicharacteristic assumption, representability, (S2) or (RS) enters. The local and residue-preserving conditions survive composition and inversion and are verified in each application. The first minimality assumption is retained even though it is redundant once the stated incoming-map property is given.

This checks B--E against the actual files: the new node is self-contained TeX with named notions or inline definitions, carries the correct source tag and blueprint provenance, and is genuinely smaller than the deformation assertion. All non-elementary facts are citations of statement nodes; the remaining short calculations are written out. The union of uses equals proof_deps, and citations.json contains literal statement excerpts for each use. All proof steps are shorter than 2000 characters. No SGA route is used. No file in the shared repository or launcher was written; no git, compiler, Lake or build command was run by the worker. The remote review_split invocation passed; the required full dry run follows this report.

## Unfinished work

No part of this one-level split is left unfinished. The single new algebra lemma is intentionally statement-only and remains an item for later splitting. The maintainer's independent review remains required after direct delivery.
