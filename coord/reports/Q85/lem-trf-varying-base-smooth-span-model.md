# Worker report

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-varying-base-smooth-span-model.json`: split into eight steps using existing nodes; the statement is unchanged. No new nodes and no new Mathlib leaves.
- `citations.json`: one verbatim statement quotation for every step/node citation.
- `searches.jsonl`: searches logged by the required msearch command. The item retains the searches inherited from its creation and adds this attempt's actual queries/results.

## Attachments

None. Searches of `lean/WeilConjectures/` for the exact blueprint tag, smooth-span/completed-base/varying-base terminology and Popescu found no declaration stating all of this item. The many Popescu ring-theory declarations do not supply the pointed two-target approximation assertion.

## WANTED

None. All mathematical sources used here are in the local Stacks checkout.

## Findings and corrections

The imported item is true as stated. The two paragraphs of Tag 0GDX (more-morphisms.tex, `lemma-relative-map-approximation-pre`) supply its route. The passage suppresses the verification that the composite from the original affine coordinate ring to the completed stalk is regular and has Noetherian fibre rings, as well as the finite-presentation checks for the two fixed target families. The split supplies both. In particular I did not infer that finite type on affine schemes means the coordinate map is finite type merely by the definition: local Noetherianity first gives local finite presentation, and the existing affine-opens characterization then gives the ring presentation. No added hypothesis or statement correction was needed.

The latest blueprint's `lem-trf-local-term-locality` and its unit now prove contracting-correspondence locality, rather than the historical nodal approximation route retained by this auxiliary node's ancestry. I read its latest statement and proof, and kept the historical auxiliary source identified in the node's existing `blueprint.from.place`; this delivery changes no blueprint/unit route and uses no SGA source.

## Search results

The whole-DAG/blueprint searches included the item, completed smooth approximation, Popescu, completion, smooth span, Tags 0GDX and 07GC. The blueprint searches for the two tags and smooth span have no matches; the broad completion hits concern different cohomological completions. Existing algebraic/limit nodes were reused rather than recreated. In particular `lem-trf-fixed-family-etale-span-descent` gives the exact fixed-target, actual-base-change and residue-field conclusions needed, so none of these clauses became a new node.

The five msearch queries of this attempt are in `searches.jsonl` and the item's `mathlib_searches`. LeanFinder was tried with two phrasings, alongside Loogle, LeanSearch and grep. Hits concerned `Algebra.Smooth.exists_finiteType`, smooth and etale Noetherian descent, standard etale presentations and scheme smoothness; none provides a Popescu smooth model of this completion with the prescribed two-target pointed diagram. I read `Mathlib/RingTheory/Smooth/NoetherianDescent.lean`; its models descend already smooth/etale algebras and do not establish that the completion is ind-smooth over the original ring. There is no claimed Mathlib leaf.

## Not duplicates

No new nodes were created. All matching existing prerequisite statements were reused.

## Review by Q85

I read the complete statement and the relevant smooth-limit and finite-stage paragraphs of Stacks Tag 0GDX in more-morphisms.tex. For the prerequisites I read the local sources behind Noetherian permanence (algebra.tex, `lemma-Noetherian-permanence`, 00FN), completion Noetherianity (`lemma-completion-Noetherian-Noetherian`, 0316), completion residue comparison (`lemma-hathat-finitely-generated`, 05GG), affine stalks (schemes.tex, `lemma-spec-sheaves`, 01HV), regular composition and ubiquity of G-rings (more-algebra.tex, `lemma-regular-composition`, 07QI, and `proposition-ubiquity-G-ring`, 07PX), Popescu (smoothing.tex, `theorem-popescu`, 07GC), directed reindexing (categories.tex, `lemma-directed-category-system`, 0032), finite-presentation factorization and relative-object descent (limits.tex, `proposition-characterize-locally-finite-presentation`, 01ZC, and `lemma-descend-finite-presentation`, 01ZM). There are no new-node sources to audit.

Step 1 uses the G-ring assertion only to obtain Noetherianity of the integers, then the exact locally-Noetherian ascent and affine-open statements to obtain Noetherianity of R,D. The affine stalk node states the actual localization map, so the Noetherian localization theorem applies to A. The completion theorem applies to its maximal ideal without additional excellence assumptions.

Step 2 uses local finite type over locally Noetherian bases exactly as stated by `pqf-lem-lft-fp-locnoeth`, then the whole-affine instance of the finite-presentation characterization. The G-ring definition gives regularity specifically of the prime-local completion map. The localization-regularity theorem gives the preceding map. I checked the extra hypothesis in the regular-composition node: the composite's fibres are explicitly quotients followed by localizations of the Noetherian completion, so the cited quotient/localization statements do give Noetherianity. The tensor-fraction isomorphism is written out, not assumed as a hidden comparison theorem.

Step 3 uses the Popescu statement on two Noetherian rings with the verified regular map. Its statement includes smooth spectra and structural colimit maps. The cofinal reindexing node preserves this colimit and has a genuinely small filtered category as hypothesis. The affine-transition limit node explicitly identifies the limit with the spectrum of the ring colimit; it is not merely a general existence assertion. The transition-affineness statement applies because all stages are affine.

Step 4 uses the completion-local-ring node's same-residue-field conclusion under its Noetherian hypothesis. The intermediate residue maps are field maps; injectivity plus the surjective composite proves each isomorphism. This is the elementary field argument in the source, and does not require rationality of the points of H over the original residue field.

Step 5 verifies all finite-stage factorization hypotheses: the index is directed, transitions are affine, stages are affine hence qcqs, and T is locally finitely presented over Spec Z. The factorization theorem is applied over Spec Z, since lambda is not initially a map over S. The tail-limit argument is written explicitly, and lambda_j(s_j)=t follows by evaluation at b.

Step 6 checks both fixed target models have finite presentation before applying the span-descent theorem. Local Noetherianity of S,T was already proved; X,Y are only assumed finite type over these bases, which suffices. The qcqs permanence node supplies finite presentation for the affine sources and its preservation under base change; the affine-spectrum fibre-product node supplies affineness. The pullback comparisons preserve both projections, with inverses given by the universal property, so the targets are the original fixed families, not arbitrary descended isomorphic schemes.

Step 7 uses the full statement of `lem-trf-fixed-family-etale-span-descent`, which I opened and read along with its proof and dependency statements. Its assumptions match the directed smooth system, its residue maps, the two affine finitely presented fixed families, and the given affine finitely presented H and etale arrows. Its conclusion supplies a common stage and the actual arrow base-change equations. Projection uniqueness keeps those equations valid under the displayed fixed-family identifications. This node has no dependency on the item, and is strictly a general limit-descent tool rather than a restatement of smooth completion approximation.

Step 8 takes all three projection residue comparisons and both elementary stage-arrow conclusions from that same node's statement; it does not borrow anything from its proof. The remaining base residue maps and base-map point equality were proved in steps 4 and 5. I checked every `uses` entry against the corresponding live node's statement and copied that statement verbatim into citations.json, giving a direct C4 audit for every citation.

For small cases, a generic point s is allowed: A and its completion are then a field, and the residue-field sandwich still applies. Positive-dimensional H or non-rational h causes no problem, since the fixed-family node only requires the two given residue-field isomorphisms, not kappa(h)=kappa(b). The hypotheses exclude empty S and H by the chosen points, but impose no unnecessary nonemptiness on other fibres. Characteristic zero, finite characteristic and mixed characteristic are covered by the finite-type integer G-ring theorem; no unrestricted DVR completion claim was used. Directed replacement is needed even if Popescu first gives a category rather than a poset, and is cited explicitly.

Against delivery-errors B--E: there are no new statements, duplicated leaves or clause-restatement nodes; the statement and all existing-node metadata stay intact; every non-elementary input has a cited statement; there is no hidden appeal to a definition for a theorem it does not state. All eight steps are shorter than 2000 characters. I retained the tensor-fraction and field-sandwich arguments as elementary computations within the assembly and used the existing general descent node for the substantial diagram comparison. The off-unit G-ring, regularity, Popescu and affine-limit statements are declared as generic tools in split_report.tool_uses, because the trace-formula unit contains no replacement for these prerequisites.

## Unfinished work

None in this stage-1 split. Formalization and proofs of downstream unsplit nodes remain outside this delivery's scope.
