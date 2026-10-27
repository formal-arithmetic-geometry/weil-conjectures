# Q88: lem-trf-prime-pair-colimit-ind-etale-model

## Files written

- dag/nodes/sec-trace-formula/lem-trf-prime-pair-colimit-ind-etale-model.json: existing statement split into five steps; Mathlib verdict: no exact match.
- citations.json: twelve verbatim statement quotations, one for each step/node citation.
- report.md and the automatically recorded searches.jsonl.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. I searched the project source under lean/WeilConjectures for the item tag and henselization/ind-etale notions. RingTheory.pair_henselization in RingTheory/PairHenselization.lean:68 is a proved generic construction already attached to lem-weil-pbc-pair-henselization; it does not state every clause of this item, particularly locality of this particular cocone and the composite from A. It is used through that existing node rather than claimed as an attachment of the item.

## WANTED

None. All sources used are present.

## Corrections and scope

The item statement is unchanged. Its previously empty proof now gives the argument for the specified cocone, rather than merely asserting that some henselization exists. No released repair note exists for this item. No prior node, report, citations, searches, or delivery output was present in this sandbox when recovery began, and no delivery process for this group/item was running. The sandbox originally contained only dispatcher .brief files.

The current blueprint ancestor lem-trf-local-term-locality and the chapter/unit records were read. The historical algebraic auxiliary chain recorded in the item's blueprint.from is retained; no chapter or unit argument is replaced. The three generic off-unit tools are declared in split_report.tool_uses. All other cited tools are existing Mathlib leaves.

The important possible gap is that def-weil-pbc-henselian-terminology states unique idempotent lifting, not containment in the Jacobson radical. Step 3 proves the necessary containment directly: a maximal ideal q failing to contain J would make the quotient of the finite cyclic algebra C/q by J zero, contradicting uniqueness of the two idempotent lifts 0 and 1. No unstated radical assertion is borrowed from a definition. This is a short direct use of the definition, so not a new lemma node.

## Searches and reuse

I searched all DAG node statements for the pair construction, its Stacks tags, radical/local consequences, affine etale finite presentation, principal localization colimits and ind-etale stability, and used the existing nodes. tools/blueprint_refs.py ancestor and searches for henselization and ind-etale confirmed the recorded ancestor and found no blueprint node giving the entire item. The item has no exact proved project declaration. Mathlib searches were run through the required msearch.py command, read, and recorded with the exact tool/query and returned digest. Two distinct semantic formulations were tried. Hits were for Algebra.Etale.finitePresentation, HenselianRing/HenselianLocalRing properties, etale loci and general filtered ring colimits. These supply no exact match for the entire specified pair-colimit model. RingTheory/Henselian.lean:94 and 108 were read: these are property classes, not constructions. No new node is introduced merely for the already available finite-presentation fact.

## Not duplicates

No new nodes; hence no new/existing pairs require distinction.

## Review by Q88

I read Stacks more-algebra.tex, lemma-henselization (Tag 0A02), including its directed category, quotient calculation and henselian-pair construction, and lemma-henselization-local-ring (Tag 0A03), particularly its first paragraph. I also read algebra.tex lemma-localization-colimit (Tag 00CR), whose statement is a module colimit, and proetale.tex lemma-composition-ind-etale (Tag 097K). The existing localization-colimit-principal-localizations node explicitly supplies the ring version, so I do not infer a ring colimit from a module colimit without that bridge. I read the current ancestor blueprint statement and proof; its trace argument is not a source for the algebraic claims here. The proof is therefore marked agent-written following the named Stacks constructions.

Step 1 cites the actual statement of lem-weil-pbc-pair-henselization, which provides essential smallness, filteredness, the henselian pair and the structural quotient isomorphism, and def-weil-pbc-category-colimit for the universal property. I checked that its category has all base-algebra maps and exactly the same quotient condition as E. The proof explicitly transfers filteredness to the small full skeleton. It checks that the induced ring map preserves the R structure through the representative of the identity algebra, proving the algebra universal property for this very cocone. Fullness then extends skeleton cocones, so uniqueness of colimits transfers the pair properties over R. It neither assumes a colimit over a large index exists independently nor takes an extra construction from a cited proof.

Step 2 cites lem-weil-pbc-etale-ring-map-iff-etale-affine, whose statement explicitly includes finite presentation, and def-weil-pbc-ind-etale-algebra, which defines the required filtered presentation. I checked the affine-etale hypothesis on every B_i. These are the R-algebra diagram and structural map from step 1, not an unrelated isomorphic abstract ring.

Step 3 cites precisely the idempotent-lifting definition and the prime-localization definition, the latter providing that R is local and k is a field. The finite C-algebra used is C/q, finite because it is generated as a C-module by 1; q is maximal, so this algebra is nonzero. The two elements 0 and 1 are distinct there, while their reductions in the zero quotient agree. Thus uniqueness gives the radical conclusion without a hidden general theorem. Since e_C is a structural field isomorphism, J is maximal and its inverse image is exactly m; this verifies both locality and the henselian-local terminology. No finite-type or Noetherian condition is used.

Step 4 cites the exact localization-colimit node, including its directed indexing preorder and specified coprojections. Its statement applies to any multiplicative S, in particular the small nonempty complement of p, which contains 1 and is closed under products. The principal-localization-open-immersion and etale-composition-cancellation statements give respectively the open immersion and its etaleness (clause 1 only); the affine-etale bridge gives finite presentation. The algebra-colimit argument through f=1 is given explicitly. The resulting presentation therefore proves ind-etaleness of the specified A to R map by its definition, with no mistaken claim that the whole localization is itself finitely presented.

Step 5 cites the ind-etale-stability statement, whose composition clause applies to exactly A to R to C. Its source is Stacks 097K. I checked there is no coefficient change, Noetherian hypothesis or residue-field extension being inserted. Each of the twelve citation entries copies an actual cited-node statement verbatim; no use relies on a cited node's proof instead of its statement.

I checked sections B through E of delivery-errors.md against the split: no new statement-only node needs its own sources or searches, no elementary duplicate or clause restatement was created, all used non-elementary facts are cited as existing nodes, and every step is below 2000 characters. The small cases include p=0 in a field (m=0 and the quotient condition forces every diagram object to be R), non-Noetherian local bases, and the impossibility of a zero C because C/J is the nonzero field k. The radical argument allows the zero quotient D/JD and uses its unique idempotent correctly. No SGA source is used.

## Unfinished work

None in the stage-1 split. No Lean file was written and no compiler, Lake or build command was run. Dry-run and delivery results are supplied by the required delivery command.
