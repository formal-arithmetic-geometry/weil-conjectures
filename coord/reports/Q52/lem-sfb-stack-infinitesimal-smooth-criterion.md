## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-stack-infinitesimal-smooth-criterion.json: statement, split in four steps; no Mathlib match.
- citations.json: eight verbatim statement excerpts, one for each step/cited-node pair.
- report.md: this report.

No new DAG nodes and no Mathlib leaves. Sandbox-only search-results.json, searches.jsonl and write_split.py retain the searches and reproducible assembly; none is a Lean file.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag/id, infinitesimal smoothness, formal smoothness and lifting names. Scheme formal-smoothness and ring-lifting declarations do not state this stack assertion. No finished project declaration covers the item.

## WANTED

None. All sources used are available in literature/stacks-project/.

## Findings and changes

The live item was unsplit and the sandbox had no earlier item, split, report or search log. There is no repair note for this item. The statement is unchanged, including the locally finitely presented atlas hypothesis and the object lift with a specified restriction isomorphism. Its four statement dependencies are unchanged. Preserved source, created, chapter, unit, provenance and all other maintainer-owned fields.

The source gives a general criterion for morphisms of stacks, but the item only needs a scheme target. Its converse chooses a smooth scheme atlas and proves the structural composite formally smooth. I expanded this in the scheme-target case using the existing global smooth-space lifting node rather than creating a node for formal smoothness of representable stack morphisms or for composition. This is the source's composition-of-lifts argument, with the base-changed atlas and its two projections written explicitly.

Read the chapter and unit records, the current latest blueprint unit and its direct-image proof at main-20261023-1620, and the ancestor output. The current unit uses compactification and the proper/open direct-image inputs; this item is an inherited prerequisite of the Picard stack further below those inputs. Nothing changes that route. The inherited provenance mentions the earlier alteration expansion; it is retained as history, not silently rewritten. The ancestor command returns None, matching the inherited null from.node. Whole-blueprint searches for formally smooth, infinitesimal, smooth atlas and 04AM returned no duplicate of the item. The definition node def-sbc-smooth-morphisms concerns schemes, not stacks.

Mathlib searches were executed through msearch.py: two semantic phrasings in LeanFinder, LeanSearch, Loogle and a whole-Mathlib grep. All five services/calls returned normally. Read all hits. The semantic hits are scheme smoothness and formally smooth ring-algebra lifting, not the criterion for stack objects. Read Mathlib/AlgebraicGeometry/Morphisms/Smooth.lean, including Smooth at lines 61 onward and its deprecated IsSmooth alias, and Mathlib/RingTheory/Smooth/Basic.lean:126 (FormallySmooth.exists_lift). Neither is a one-line specialization to algebraic stacks. The existing item searches were retained; the actual new queries and their output were appended without inventing or repeating old evidence.

## Unfinished work

None at stage 1. The split reduces this item to existing nodes; it makes no claim that all downstream proofs have been formalized.

## Not duplicates

No new nodes were created. In particular, lem-sfb-smooth-space-affine-infinitesimal-lift is reused, not copied: it proves lifting for a smooth algebraic-space map, whereas the item derives smoothness for an algebraic stack from object lifts. The scheme-only criterion in def-sbc-smooth-morphisms is applied only to U -> S. No new node restates a clause of the item.

## Review by Q52

I read Stacks stacks-more-morphisms.tex, Tags 0DP0 (lemma-smooth-formally-smooth), 0DNY (lemma-reformulate-formal-smoothness), and the preceding diagram/dotted-arrow definition. I also read spaces-more-morphisms.tex, Tag 04AM (lemma-smooth-formally-smooth), both directions and the affine torsor argument; more-morphisms.tex, Tag 02H6 (lemma-smooth-formally-smooth); and stacks-morphisms.tex, Tag 075U (definition-smooth). No new-node source is needed, because no new node is introduced. No SGA source is used.

Step 1 uses the actual atlas definition in def-sfb-algebraic-moduli-stack and the scheme test definition in def-sbc-formally-smooth. The former supplies the meaning of a smooth surjective scheme atlas, and the latter tests all affine first order thickenings over S. Local finite presentation of the composite is the item's explicit hypothesis, not an inference from representability, nor an unproved assertion about all atlases. Choose that witnessing atlas once. This is an elementary choice and expansion of the hypotheses.

Step 2 uses the item hypothesis to lift a(u), retaining alpha: i*x' -> a(u), and the statements of def-sfb-algebraic-moduli-stack and def-sfb-stable-pointed-moduli-groupoids. I opened both nodes. The first explicitly says every scheme pullback of the atlas is an algebraic space with smooth surjective projection, so it supplies Z and smoothness of q without a hidden theorem on atlas base change. The second explicitly describes objects and arrows in a 2-fibre product, made fibrewise with induced pullbacks, so (i,u,alpha) supplies s with the displayed projections. Z need not be a scheme. I do not infer a lift to U merely from the stack-object lift. This step is the elementary assembly of the specified triple, not an unsupported smoothness theorem.

Step 3 uses the statement, not the proof, of lem-sfb-smooth-space-affine-infinitesimal-lift. It accepts arbitrary smooth algebraic spaces over S, arbitrary affine first order test thickenings over S, and maps with the required commuting square. Here its X is Z, its Y is T', its test schemes are the original T and T', a0 is s, and b is id_T'. The equality qs=i was proved in step 2. All its hypotheses therefore hold without extra separatedness, quasi-compactness, finite-type or Noetherian assumptions. It gives the global s', including s'i=s, and projection gives u'i=u exactly. Because the fibre product is taken in stacks over S, the two projected maps to S agree, so u' is over S. The cited def-sbc-formally-smooth then gives exactly the desired predicate for the scheme map U -> S. This is the sole non-elementary proof step.

Step 4 uses the actual scheme lifting characterization in def-sbc-smooth-morphisms, not a definition of smooth stacks mistakenly applied to an algebraic space. With local finite presentation from step 1 and formal smoothness from step 3 this makes U -> S smooth. The final sentence uses the explicit last clause of def-sfb-algebraic-moduli-stack: smooth over S means existence of such a smooth surjective scheme atlas with smooth composite. Its quote for step 4 is that clause rather than just the atlas clause. The conclusion is therefore exactly the item's conclusion.

I checked B through E of delivery-errors.md against this proof. Every cited node was opened and its relevant statement copied verbatim into citations.json; all eight excerpts were checked against the current files. Every non-elementary ingredient is covered by the smooth-space lifting node. The only remaining operations are a choice, the fibre-product triple and its projections, and two explicit definition applications. There is no new opaque lemma carrying the item's conclusion, no new definition, no informal tag used in place of a needed node, and no unproved comparison of coefficients. A dependency traversal found no path back to the item through the cited nodes. All four proof steps are under 2000 characters (395, 618, 589 and 364), total 1966 characters, so no long step hides a sublemma.

For edge cases, when i is the identity the chosen alpha still defines s and projection gives the required exact restriction. When the test scheme is empty the same lemma covers the empty affine scheme, with no point choice or nonempty assumption. For the empty stack, U may be empty and all scheme test maps into U are treated by the same argument; the conclusion is the permitted empty smooth atlas. If the stack is represented by a scheme, the construction reduces to ordinary composition of formal lifting tests. Nontrivial automorphisms are retained in alpha and in the 2-fibre product, so the proof never identifies an object lift up to isomorphism with an equality in the atlas. No claim of uniqueness or full faithfulness of restriction is used. I found no statement dispute and no mathematical correction was required.

The review is my own direct-delivery review; no second worker or agent was started. The maintainer's independent delivery review remains the acceptance check.
