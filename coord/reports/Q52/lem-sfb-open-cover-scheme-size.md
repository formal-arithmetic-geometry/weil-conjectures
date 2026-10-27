## Worker report

Files written: dag/nodes/sec-six-functors-basics/lem-sfb-open-cover-scheme-size.json (existing statement, now split, no Mathlib match); citations.json; this report. There are zero new nodes and zero new Mathlib leaves. searches.jsonl contains the actual Q52 search records. No Lean was written or compiled.

Attachments: none. Searches for the exact blueprint tag and for the size/open-cover notion in lean/WeilConjectures found no declaration giving the item. The QuasiCompactOpenInduction hit is an induction theorem for properties of opens, not a size estimate. Existing sorry declarations were not counted as finished proofs.

WANTED: none.

The imported item already corrects the empty-cover exception in the printed Stacks lemma. Its statement, statement dependencies, source and inherited blueprint provenance are retained. Six steps now spell out finite affine refinements, counting labelled opens via lists, representing arbitrary affine opens by finite lists, and injecting section rings into bounded finite products. The count of a dependent union and of a finite product is reduced explicitly to the existing finite-list bound, avoiding hidden cardinal-arithmetic lemmas. No original proof, report or logged sandbox search existed to retain. Existing repository searches are retained, and the new searches are appended without inventing runs.

Nothing remains unfinished for this one-level split. Existing input nodes remain the responsibility of their owners.

## Existing duplicate

lem-sfb-open-cover-scheme-size and lem-sfb-scheme-size-open-cover-bound state the same corrected Tag 000Q estimate, up to variable names and explicit clarification of the empty supremum. The second node is also unsplit in the read repository. It should eventually be merged into this item by the maintainer; it is neither cited nor modified here. Using it as the entire proof would merely relabel the item. The size definition itself is already available as def-sfb-scheme-cardinal-size and is reused in step 1, without rewriting the statement's self-contained inline definition.

## Not duplicates

No new nodes were created. In particular no finite-affine-refinement, finite-product bound, sheaf-separatedness, or scheme-size node was added: the first and last are already supported by existing nodes, the product estimate is an explicit list injection, and sheaf uniqueness is a definition-level argument.

## Source error

Stacks sets.tex Tag 000Q (lemma-bound-size) prints a maximum without an explicit aleph_0. For the empty cover of the empty scheme its right side is 0, while the definition in section-categories-schemes makes its left side aleph_0. The assigned statement already includes aleph_0, so no statement correction is required in this delivery. Both empty and nonempty covers are proved. The tensor-like sign between cardinalities in the printed proof is cardinal product, not a tensor product of rings; the split uses a Cartesian product and a restriction injection.

## Review by Q52

I read the full proof of Stacks 000Q in literature/stacks-project/sets.tex, together with the size definition in section-categories-schemes (Tag 000H, before 000I). I read the chapter and unit records and the current blueprint latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and its direct-images proof. This is the generic size input to the inherited 04T7/04U0 supporting route; it changes no unit-level route. The inherited blueprint ancestor is null, as confirmed by blueprint_refs.py ancestor; I preserved that provenance rather than inventing an ancestor. Searches of all imported blueprint nodes for scheme size, affine basis, finite sequences, cardinal, open covering and 000Q identified no alternate blueprint size statement.

For step 1 I opened def-sfb-scheme-cardinal-size and checked that its exact maximum and supremum agree with the inline invariant of the item, including the empty scheme. Step 1 only takes the inequalities defining this maximum. The definition was independently approved in the repository and is not a new node of this delivery.

For step 2 I opened both lem-weil-pbc-affine-scheme-qcqs and lem-weil-pbc-affine-opens-basis and read their statements. The former gives quasi-compactness for an affine scheme with no additional Noetherian hypothesis; the latter gives an affine neighbourhood inside any prescribed open. I also read Stacks algebra.tex 00E8 (lemma-quasi-compact) and schemes.tex 01IT (lemma-basis-affine-opens). The open to which the basis is applied is U intersect Y_i in the scheme Y; the resulting V is affine, while U intersect Y_i need not be. Compactness is applied only to the affine U, never to Y or its cover members. Restriction of the same structure sheaf identifies V as an affine open of Y_i. This repairs the potential false shortcut of treating intersections of affine opens as affine.

For step 3 I opened lem-weil-pbc-finite-list-cardinality and read Cardinal.mk_list_le_max at Mathlib/SetTheory/Cardinal/Arithmetic.lean:746-750. Its statement applies to every set, without nonemptiness. The explicit two-entry list injection counts the labelled disjoint union; applying the same lemma again counts its lists. Thus no uncited dependent-sum cardinal estimate is used. Step 4 needs no extra cited theorem: a list has a definite union, and choosing one list representing each affine open is injective because its union recovers that open. The choice is ordinary set-theoretic choice, already implicit in cardinal inequalities.

For step 5 I opened def-pc-scheme and def-weil-locally-ringed-space-morphism. They say that schemes are locally ringed and that the structure sheaf is a sheaf of commutative rings. I read the current blueprint definition of schemes and the uniqueness axiom in sheaves.tex definition-sheaf. Equal restrictions on a cover therefore imply equal sections directly by the definition, so no additional separatedness theorem is hidden here. Sections on V computed in Y_i and Y are sections of the same restricted sheaf. No quasi-separatedness is used.

For step 6 the same finite-list cardinality node says exactly what bounds the ordered images of an n-tuple in K. This injection works also for the empty tuple, which gives the empty list. Step 1 bounds each factor; step 5 supplies the injection from sections. Supremum and maximum inequalities then prove the statement. All quoted citations in citations.json were checked literally against the current statements, and every proof-step citation is included. I checked that none of these dependencies reaches this item, avoiding a dependency cycle.

Small cases checked: empty index set forces Y empty and s(Y)=aleph_0; a nonempty family of empty opens also gives the empty scheme; a singleton cover gives equality of the bound; finite and infinite covers work with the same infinite kappa; finite section rings are allowed; the empty affine open has its unique empty-family section and is represented by an empty list. A non-quasi-separated ambient scheme causes no issue because only individual affine opens are compact and no intersection is assumed affine.

Against delivery-errors B--E: there are no new nodes needing standalone statements, searches, or duplicate-tag distinctions. The item is a proof rather than an application of its duplicate. Every non-elementary input is an existing cited statement, and all remaining steps have the elementary injections or uniqueness arguments written out. Each step is below 2000 characters. Sources have stable tags and labels. No SGA source is used. Mathlib searches ran via msearch.py in all four modes and a second semantic phrasing; their hits describe covers or affine refinements, not the requested three-term size estimate. I read the relevant Cover/Open.lean and Cover/Directed.lean constructions before rejecting these matches. No search marked unavailable was represented as an absence result.

## Delivery checks

The first dry run rejected the too-short scheme-definition quotation. I extended it to the verbatim full opening clause; the mathematical proof did not change.
