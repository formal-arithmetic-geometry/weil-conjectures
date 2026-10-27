# Q74 stage-1 delivery: lem-sfb-neron-finite-complement-patching

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-neron-finite-complement-patching.json`: statement split into nine proof steps. No new nodes; no new Mathlib leaves.
- `citations.json`: one literal statement quotation for every node used by every step.
- `searches.jsonl`: the search command's records, retained unchanged.
- `report.md`: this report.

## Attachments

None. Searched the live `lean/WeilConjectures/` for the exact item id and the Neron/Néron/neron vocabulary, and checked `lean/Sheaf/` as supporting material. There is no corresponding project declaration to attach. Unrelated finite-complement curve declarations do not state the Néron-model assertion.

## WANTED

WANTED: Bosch–Lütkebohmert–Raynaud, *Néron Models*, project copy `literature/bosch-lutkebohmert-raynaud-neron-models.pdf`, §1.4 Proposition 1 and §1.2 Proposition 4/Lemma 5, for lem-sfb-neron-finite-complement-patching. The primary scan at https://www.math.stonybrook.edu/~kamenova/homepage_files/Bosch_Raynaud_Neron_Model_tc.pdf was read online, printed pages 13–14 and 18 (PDF pages 19–20 and 24). No download or literature-file write was performed. The proof is marked agent-origin, with its general limit and gluing inputs read from the local Stacks sources.

## What changed and what was wrong

The live item was unsplit with no proof. Its statement is mathematically sound and is retained verbatim, including its generic identifications and the mapping property for ALL smooth test schemes. Added the already existing localization-at-prime definition to statement dependencies for the notation D_s. The inherited group-scheme terminology is unused and imposes no additional group hypothesis.

The new proof supplies the arguments behind the source's brief patching passage: smooth separated neighbourhood models; extension of both directions of the specified generic isomorphism and its inverse equations; deletion of the finite bad closed set while retaining the missing point; the full transition cocycle; locality on the BASE for separatedness; and the mapping property with affine reduction and descent of maps/equalities. The local stalk spectra are never treated as open subschemes. The generic-isomorphism spreading node found in another unit assumes affine source and target, so it was NOT used for the possibly nonaffine models: the general object/map/equality theorem thm-pd-spreading-out is used instead. No mathematical error or route change was needed.

The live blueprint ancestry already has `from.node: null`; `tools/blueprint_refs.py ancestor` confirms None. Retained that ancestry and its explicit source place. Read the current chapter and latest `sk-thm-sf-ctf-stability` text. The latter is a high-level six-functor assertion and does not replace any of the local patching arguments here. Searches over the whole imported blueprint for Néron, Neron and finite complement, and searches of the latest blueprint tree for Néron/Neron/neron, found no equivalent blueprint assertion. `same_as` remains empty.

## Mathlib searches and reuse

Ran leanfinder twice with different phrasings, leansearch, loogle on AlgebraicGeometry.Scheme.GlueData, and a source grep for Neron|Néron|neron in AlgebraicGeometry, using the required msearch.py command. All services answered; inspected their hits. They give general gluing data, relative gluing, smoothness, integral/Noetherian schemes, and Dedekind-ring notions, rather than the required universal mapping property or the local-to-global construction. Retained every inherited item search and appended only the exact queries logged by this group's command. The appended results are the command log's actual records, with hit counts and returned names. No new result is alleged to be unavailable or a leaf.

Before deciding whether new nodes were needed, searched the entire DAG by titles, keywords, and the relevant Stacks tags. Existing thm-pd-spreading-out covers finite-presentation object, morphism AND equality descent over qcqs affine-transition systems; existing lem-weil-pbc-descend-smooth-qcqs and lem-weil-pbc-descend-separated cover the two properties; existing lem-galois-glue covers objects over an open base cover. Thus no new node is warranted. In particular the connected-model Néron globalization node has different hypotheses and is not used as a substitute for this item.

## Not duplicates

No new nodes. The existing general tools are cited directly. No clause of this item has been restated as a new node.

## Review by Q74

I read BLR §1.4 Proposition 1 and its proof to check that the proposed construction uses a model on a dense open and finite-type local models at its finitely many missing points, with no group structure required. I read §1.2 Lemma 5 and the proof of Proposition 4 to identify precisely the finite-presentation limit arguments hidden behind the final mapping-property assertion. I then read the local Stacks limits.tex statements labelled lemma-descend-finite-presentation (01ZM), lemma-descend-smooth (0C0C), and lemma-descend-separated-finite-presentation (01ZQ), and schemes.tex lemma-glue/lemma-glue-schemes (01JB/01JC), including their mapping properties. There are no new-node sources to audit.

For step 1 I checked each definition and the qcqs-over-affine statement. Smoothness really supplies local finite presentation, finite type really supplies quasi-compactness, and the qcqs node explicitly includes separated implies quasi-separated. The local-ring-neighbourhood node gives a small directed SET of affine neighbourhoods, qcqs bases and affine transitions, with the claimed limit. This satisfies the hypotheses of all three clauses of thm-pd-spreading-out and avoids using an unbounded or non-small index category.

For step 2 I opened the statements of object descent, finite-type-over-Noetherian, locally-Noetherian-quasi-separated, smooth descent and separated descent. Object descent gives an actual finitely presented scheme. The finite-type theorem gives a Noetherian source at an affine Noetherian stage, and the quasi-separatedness theorem supplies the remaining source hypothesis for property descent. Smooth descent additionally assumes local finite presentation, already present. Separated descent imposes no extra finite-presentation assumption on the morphism, but does require the qcqs source and target verified here. The target-open locality statement justifies later restrictions preserving separatedness. The neighbourhood limit identifies the given T_i model, rather than constructing an unrelated one.

For step 3 I checked clauses (2) and (3) of thm-pd-spreading-out explicitly: both directions of the specified generic isomorphism descend, and both inverse identities hold after a common later stage. The models are not assumed affine; that is permitted by this cited general theorem. The source and target are finitely presented over affine base neighbourhoods. Their generic fibres carry the specified identifications with V, so the resulting overlap isomorphism respects those identifications.

For step 4 the quoted closed-point finiteness lemma requires a Noetherian scheme and a closed subset consisting of closed points. W_i is Noetherian, W_i minus G_i is closed and misses the generic point, and in a dimension-one domain every nonzero prime is maximal. I verified the removal is made in W_i of a finite set of closed points of S, with s_i expressly excluded from the removal. Thus B_i is genuinely open, contains s_i, has B_i intersect U equal to G_i, and still receives T_i. This is the source's finite-complement shrinking, written explicitly.

For step 5 I checked the full statement of lem-galois-glue, not its proof. It takes schemes over a Zariski BASE cover, transition isomorphisms on the entire pairwise base overlaps and the cocycle. Those data are exactly e_j inverse composed with e_i; cancellation proves the cocycle. Therefore its conclusion really gives the restrictions of M asserted here. Base change along T_i factors through B_i and recovers the given M_i, including its generic identification.

For step 6 the separatedness and quasi-compactness locality statements really concern locality on the target, so they apply to U and B_i. Local smoothness and local finite type are checked on the affine charts of the already smooth restrictions, using the affine-local notion explicitly supplied by the smooth-definition node. Together with quasi-compactness, the finite-type definition supplies the desired finiteness. This step does not infer separation from gluing separated source charts.

For step 7 I checked the smooth base-change node actually has a smooth clause (2), not just proper base change. The mapping properties of M_U and M_i are hypotheses of THIS item and so are not missing external citations. For an affine smooth test Z, the restrictions of Z and M over an affine neighbourhood are finitely presented; consequently clause (3) of object/map/equality descent really compares the two morphisms. The resulting neighbourhoods of all missing points, together with U, cover the base. The cited scheme-morphism-gluing statement includes equality detected on an open cover, precisely the final inference needed.

For step 8 the same hypotheses permit clause (2) of the limit theorem to spread the actual extension supplied over T_i. Its generic restriction is the prescribed u_E, not a newly chosen generic map. On overlaps the source is smooth over U, so the ASSUMED mapping property of M_U, applied to that source, proves equality of the two morphisms. Pairwise missing-point neighbourhood overlaps lie in U. The morphism-gluing statement then gives an extension on Z. Step 9 applies this only to affine opens of an arbitrary smooth X; overlaps are compared on their own affine open cover by step 7 and then glued. Neither quasi-compactness nor separation of the general test scheme is assumed.

I checked empty schemes, r=0, a local Dedekind base with U just the generic point, and arbitrary smooth test schemes with infinitely many affine charts. On a trait the neighbourhood limit may have a terminal neighbourhood, so descent specializes correctly; a nonempty open generic point is allowed. No connectedness, nonemptiness, properness, group structure, excellence, completion, or residue-field hypothesis was introduced. The nine non-elementary step texts are all below 2000 characters; none transfers a hidden lemma to a new restatement of the item. Each dependency quotation in citations.json is copied verbatim from the cited statement, and I read those statements for the uses described above. Generic tools in other units are declared in split_report.tool_uses, not as top-level maintainer approvals.

## What could not be finished

Nothing in the stage-1 split. Independent maintainer review and later formalization remain the project's next stages.
