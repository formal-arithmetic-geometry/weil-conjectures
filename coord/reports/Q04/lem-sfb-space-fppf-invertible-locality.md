# Q04 stage-1 delivery: lem-sfb-space-fppf-invertible-locality

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-space-fppf-invertible-locality.json: item, statement, split; no exact Mathlib match. Four proof steps use existing nodes only.
- citations.json: 14 records, one for every step/node pair, with verbatim statement excerpts.
- searches.jsonl: actual prescribed searches; inherited item searches retained in the node.

New nodes: 0. New Mathlib leaves: 0. The statement, its statement dependencies, source, inherited blueprint provenance, and all maintainer fields are unchanged.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint id and for invertible/fppf combinations and algebraic-space terminology. The Picard group documentation mentions fppf sheafification, but supplies no declaration detecting line modules on algebraic spaces. No sorry declaration was treated as finished.

## WANTED

None. All mathematical sources used below are present in literature/stacks-project/.

## Problems found and changes

The imported item had no proof. Its conclusion and hypotheses are correct. Stacks 060X reduces finite local freeness of quasi-coherent modules on algebraic spaces to schemes by etale localization. For the specified rank one, the existing lem-pc-fpqc-descent already states reflection of finite local freeness of a given rank, so there is no missing rank lemma to create. In particular lem-sfb-finite-locally-free-fppf-descent concerns finite locally free scheme morphisms and was deliberately not used as a statement about module sheaves. The existing lem-trf-algebraic-space-invertible-descent only glues line modules along etale covers; it is not a theorem detecting the property along fppf covers and was not used for that purpose.

The inherited blueprint.from.node is null; tools/blueprint_refs.py ancestor prints None. I preserved that provenance rather than fabricating a blueprint ancestor. Read the current latest blueprint's sk-thm-sf-ctf-stability unit and direct-images proof (3), and the chapter/unit records. This item is an auxiliary input down the recorded rigidified-Picard chain, not a key node of that unit, so no unit realization fields change. Whole-blueprint searches for invertible and fpqc found the scheme descent statements, not an algebraic-space version duplicating this item. The proof keeps the item's stated Stacks etale-localization route.

## Not duplicates

No new nodes were created. Existing scheme descent and scheme-site equivalence were reused instead of creating their algebraic-space rank-one specializations. Searches of the whole DAG for 060X and for descent, invertibility, finite local freeness and faithfully flat rank conditions were read before deciding that no new nodes were needed.

## Mathlib searches

Ran msearch.py with leanfinder (two phrasings), loogle, leansearch and two grep patterns. Every service answered. The first semantic query returned generic QuasicoherentData declarations; the second returned scheme/algebra etaleness and generic finite-presentation declarations. LeanSearch returned the generic quasi-coherence class and constructors. Loogle returned IsLocallyFree and its local-generator data and consequences. The descent/rank-one grep had no hits; the second grep located IsLocallyFreeData at LocallyFree.lean:47 and IsLocallyFree at :61. Read that source: this is arbitrary locally free data on one fixed ringed site, not reflection of rank one across an fppf map of algebraic spaces. Therefore none is an exact match or one-line specialization of the item. Existing search records were preserved; added records use exactly the queries in searches.jsonl, and no unavailable service was called a negative result.

## Review by Q04

I read spaces-descent.tex, lemma-finite-locally-free-descends (060X), including its explicit scheme-localization proof, and descent.tex, lemma-finite-locally-free-descends, which derives the ordinary result from finite presentation and flatness descent. I also read descent.tex 05VG (lemma-equivalence-quasi-coherent-properties) and 03LC (proposition-equivalence-quasi-coherent-functorial), spaces-properties.tex 03GA (lemma-pullback-quasi-coherent), and the fppf-to-fpqc comparison in topologies.tex 022C and spaces-topologies.tex 0DFQ. No SGA source is used. There are no new nodes needing separate source reviews.

For step 1 I opened each of def-trf-algebraic-space, lem-trf-space-representable-etale-scheme-tests, lem-sfb-space-fppf-covering-calculus and lem-trf-fppf-covering-is-fpqc. The first supplies surjective etale scheme atlases. The second explicitly says that the product of two scheme-source maps to an algebraic space is a scheme. The covering-calculus statement supplies etale-to-fppf comparison, composition, arbitrary base change and the scheme comparison. The last states that the same fppf family is fpqc. I apply it only after the sources and target are schemes. This avoids the false assumption that an arbitrary algebraic-space base change is a scheme, and needs no quasi-compactness of X or of the atlas.

For step 2 I opened lem-sfb-space-module-pullback-quasicoherent, lem-trf-space-representable-etale-scheme-tests, def-sfb-space-module-tensor-composition and def-trf-algebraic-space. Their statements give respectively quasi-coherence under arbitrary pullback, etale base change/composition, the normalized composition isomorphism for arbitrary space morphisms, and etale pullback as localized restriction. The composite B_i -> A_i -> X_i is etale because B_i -> A_i is a base change of U -> X. Thus preserving a line module here is just restriction of its trivializations; no non-etale preservation theorem is hidden. The square gives p_i^*u^*M = (q_i e_i d_i)^*M up to the cited composition maps. The local tensor formula records the identification, rather than asserting an unexplained transport.

For step 3 I opened lem-trf-scheme-zariski-etale-quasi-coherent-equivalence, lem-pc-fpqc-descent and def-sc-invertible-module. The first is an equivalence for all quasi-coherent modules and explicitly identifies invertibles with line modules; crucially its pullback comparison holds for every scheme map, so it applies to the fppf maps p_i, which need not be etale. The second's clause (2), quoted verbatim in citations.json, reflects finite local freeness of a given rank, so r=1 supplies the exact assertion needed. It starts with a quasi-coherent module and does not require it already to have finite presentation. The third identifies ordinary invertibility with Zariski local rank one. No assertion about morphisms finite locally free is substituted for a module assertion, and no rank-detection lemma is silently imported.

For step 4 the same equivalence gives a line module on U. The definition of a line module and the cited etale composition/base-change calculus let its local trivializing scheme maps be composed with the surjective etale atlas U -> X. Their images still cover X, and restriction of M along each is the restricted structure module. This is only the definition of local triviality, so the step is marked elementary; it does not cite an unproved descent theorem for the entire conclusion.

Against delivery-errors B1-B10: there are no new statement-only nodes, no invented definitions or Mathlib leaves, and no fabricated search records. The item's TeX and full hypotheses are retained. Against C1-C8: every non-elementary input is an existing node; I read its statement, not its proof, and verified the quoted text is literally present. Generic off-unit tools are declared in split_report.tool_uses for review, without modifying the maintainer's tool_uses field. Against D1-D5: the actual atlas reduction and comparisons are the proof, rather than newly named versions of the conclusion. Against E1-E7: I checked all scheme, quasi-coherence and topology hypotheses at the point of application, and needed no statement correction or source dispute.

Edge cases: the empty space has the empty trivializing cover, and an empty fppf index set can occur only in that case. Empty source members add no condition. Disconnected spaces and disconnected charts cause no difficulty because the reflection node gives the specified rank one on every component. No finite subcover is taken, so an arbitrary small cover of a non-quasi-compact space remains allowed. Non-Noetherian bases are allowed by every cited comparison and descent statement. The descended module need not be finitely generated in advance: rank-one local freeness is the conclusion. A nontrivial line bundle need not become globally trivial on X, and the proof only concludes local triviality. Every proof step is shorter than 2000 characters; none contains a hidden long comparison lemma.

## Unfinished work

No mathematical part of the one-level split remains. Dry-run and delivery results are recorded after the checks complete.
