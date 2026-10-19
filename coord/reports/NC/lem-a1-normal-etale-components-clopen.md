# Stage-1 report: lem-a1-normal-etale-components-clopen

## Files written

- dag/nodes/sec-purity-real-sheaves/lem-a1-normal-etale-components-clopen.json: item split into seven steps; Mathlib searches find no match for the full statement.
- citations.json: 29 step/node records with verbatim quotations from the statements read.
- report.md: this report.

No new nodes; zero new Mathlib leaves. Existing searches and blueprint ancestry were retained. Additional actual searches are in searches.jsonl and appended to the item's research field.

## Attachments

None. Searched the read-only WeilConjectures source for the exact blueprint tag, normal/etale combinations, geometric unibranchness, and component/clopen combinations. No project declaration supplies every clause of this item. In particular, smooth-base-change etale-cover declarations have stronger integral/separably-closed-function-field assumptions and do not establish this statement. No master sorry declaration was treated as a proof.

## WANTED

None. Read the local Bhatt-Scholze PDF, printed p. 71, Lemma 7.4.10, first paragraph. Read the Stacks sources properties.tex (normality, component decomposition, local irreducibility), algebra.tex (smooth ascent and strict-henselization construction), more-algebra.tex (normality of henselizations), morphisms.tex (finite type over a locally Noetherian base), and the connectedness/irreducibility definitions in the topology statements. No SGA source is used.

## Findings and corrections

The item statement is unchanged and is true, including its explicit empty-scheme allowance. Its proof was empty. The Bhatt-Scholze paragraph applies to locally topologically Noetherian geometrically unibranch schemes; this item has the stronger locally Noetherian normal-base assumptions, so the existing affine normal decomposition proves the component assertion directly. This is below the ancestor blueprint node, within the same normal-cover argument; it replaces no chapter or unit step.

The original blueprint ancestor's lisse-section sentence alone does not supply these component facts; its already-created monodromy and normal-cover children explain their use. I read the current main-20261015 ancestor proof, chapter record, and Rankin-Selberg unit. No unit binding or realized field was changed.

No new statement-only nodes are needed. Searches of the whole DAG by tags 0357, 0BQ3, 033C and by normality/component/henselization terminology found reusable inputs. Blueprint searches for normal etale, normal local, geometrically unibranch and irreducible components found no equivalent blueprint node for the whole item; same_as stays empty. In particular rem-pc-regular-normal is used only through its Noetherian normal-decomposition clause, not its regularity clause. lem-fin-etale-normal-components assumes an integral base and a Noetherian source and is not used as a global substitute.

The seven proof steps are all shorter than 1000 characters. The component-restriction and strict-henselization identifications are explicit cited inputs, not hidden inline lemmas. Corrected source references while checking the tag map: finite-type Noetherianity is 01T6/lemma-finite-type-noetherian, Noetherian topology is 01OZ, and affine-local normality is 033J. No statement dispute arose.

## Unfinished work

None in this one-level split. Its existing unsplit dependencies remain separate queue items. No Lean was written or compiled.

## Not duplicates

No new nodes were created. The existing ring ascent, henselization, finite normal decomposition, and open-restriction nodes are reused instead of making scheme-specialized duplicates or nodes restating clauses of this item.

## Review by NC

I checked B through E of delivery-errors.md against the written item, the source passages, and the full statements of every cited node. There are no new nodes requiring a separate source review, small-case audit or Mathlib-leaf certification.

Step 1 uses the actual locally-finite-presentation clause of def-weil-etale-morphism and the polynomial-quotient definition in def-sbc-locally-finite-presentation. The generators visibly give local finite type as defined in def-weil-finite-type-morphism. pqf-lem-locnoeth-lft assumes only a locally Noetherian target and local finite type, exactly what is available; it requires no quasi-compactness of Z or q. pqf-def-locnoeth supplies affine Noetherian neighbourhoods and lem-sc-affine-noetherian-underlying-space supplies their Noetherian topology. This proves the local topological claim without silently promoting Z to a globally Noetherian scheme.

Step 2 uses the stalk/localization isomorphism of lem-weil-pbc-affine-open-stalk-localization at every prime of an affine chart. The hypothesis on all stalks of X therefore says exactly that each prime localization of its section ring is a normal domain. That is the stated definition of a normal ring in def-weil-pbc-normal-ring; this elementary step neither assumes that an affine section ring is a domain nor confuses the two normality conventions.

Step 3 uses the affine-cover description explicitly present in def-weil-etale-morphism, and lem-weil-pbc-etale-over-normal-ring-normal applies to precisely the resulting etale map between affine spectra. The normal-ring conclusion means its prime localizations are normal domains; the same stalk/localization node identifies them with the stalks of Z. This argument allows disconnected affine charts and imposes no finite or separated hypothesis on q.

Step 4 applies lem-weil-pbc-localization-normal-domain to the normal domain A=O_(Z,z); the complement of any prime does not contain zero. This checks the normal-ring hypothesis of lem-weil-pbc-etale-colimit-normal-local-domain, rather than merely assuming an integrally closed domain is already normal in both conventions. The colimit being used is the pointed etale-algebra colimit of def-sc-ring-strict-henselization, so I use lem-sc-pointed-etale-small-filtered for filteredness and essential smallness, and lem-sc-ring-strict-henselization-local-maximal-ideal for its local vertex. The colimit normal-domain result then applies literally. Its domain conclusion invokes clause (2) of lem-weil-pbc-spec-domain-stalks-function-field, and def-pc-integral-scheme supplies irreducibility. Read Stacks 06DI in more-algebra.tex: this is its stated normal strict-henselization argument, also explaining the geometric-unibranch observation in 0BQ3. No extra excellence or Noetherian hypothesis on a henselization theorem was introduced.

Step 5 invokes clause (2) of rem-pc-regular-normal only on an affine Noetherian neighbourhood W. Such W is quasi-compact as an affine scheme, locally Noetherian by the cover, and normal because its local rings are those of Z. Thus all hypotheses of that existing node are satisfied. lem-sc-components-open-injection states both that C intersect W is a component when nonempty and that restriction is injective. Here it contains the chosen point z, so it is nonempty. The local decomposition makes this intersection open; its union over z is C. Closedness is explicitly in def-weil-irreducible-components.

Step 6 checks global disjointness rather than assuming that the chart result already states it globally: if C and D meet at z, the two nonempty restrictions are components of the same W. Their meeting forces equality by the chart decomposition, and injectivity of restriction gives C=D. All facts used are the statements of the same two nodes used in step 5; no lemma is extracted from a cited proof.

Step 7 uses lem-sc-irreducible-components-cover for the component through a chosen point of T. The clopen partition of T by that component forces containment using the nonempty connectedness convention in def-weil-connected-scheme. Irreducibility implies connectedness directly from the two definitions, with the two proper closed sets written in the step. Maximality of a connected component then forces equality. Empty Z gives no components, and the statements are vacuous. I also tested a disconnected normal base and an infinite disjoint union of etale sheets: the proof is local and does not require finitely many global components, finite fibres or quasi-compact source. A nodal crossing would invalidate normal stalks and is rightly excluded.

The cross-unit citations are generic tools (normal algebra ascent, henselization properties and elementary scheme/topology background), declared individually in split_report.tool_uses. They serve the normal-cover input of the ancestor's proof, not an alternative Rankin-Selberg route. citations.json contains a literal statement quotation for every occurrence of a cited node. No cited definition is used in place of a missing theorem: in particular filteredness, locality, normal ascent and component restriction each have their own theorem citation.

The standalone server review_split check returned PASS with zero new nodes before this report. The first full dry run requested longer quotations for five citation records. I replaced those short literal fragments with their complete statements; the proof and its dependencies did not change. The repaired full dry run and push follow this self-review.
