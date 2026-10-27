# Q111: lem-sfb-stack-inertia-separated-diagonal

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-stack-inertia-separated-diagonal.json: statement, split; no Mathlib match. Statement, original five statement dependencies, provenance, blueprint fields and historical searches retained. Five proof steps added, with a proof origin and split report.
- citations.json: one verbatim statement excerpt for each node used in each step.
- searches.jsonl and search-*.txt: actual search log and complete results. write_split.py is sandbox-only drafting material.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searched the live project under lean/WeilConjectures for the blueprint tag, inertia/separatedness together, Deligne--Mumford, and AlgebraicStack. There is no project declaration stating the item. Ramification inertia results are different notions and do not provide an attachment.

## WANTED

None. All proof sources used are present locally.

## Corrections and provenance

The imported item is true and its statement was not changed. The existing relative-inertia/second-diagonal node already supplies representability and the second-diagonal identification, so introducing a replacement would duplicate it. The group-separatedness equivalence is not hidden in a new node: the proof writes its two elementary scheme-test calculations, including the inverse-functor and arrow calculations for inertia and the equality g^-1 h = 1 iff g = h. Thus it does not move a clause of the item into a new node.

Read the current latest blueprint direct-images proof (3). It now uses compactification and direct-image preservation without spelling out the inherited deep alteration/moduli chain. I retained the item's recorded supporting role and route, not an older blueprint snapshot. blueprint_refs.py ancestor returns None for the inherited created.item chain; no imported ancestor was invented. Whole-blueprint searches for inertia, separated diagonal, second diagonal, group algebraic space and neutral section found no equivalent stack statement.

## Not duplicates

No new nodes. Reused lem-sfb-relative-inertia-second-diagonal-geometry rather than duplicating its 050Q/034H content. The existing smooth-atlas-automorphism-diagonal-test is the unramifiedness clause of 0CL0, not this separatedness clause. The group-scheme-separated-field node assumes a field and a group scheme, so cannot replace the arbitrary-base algebraic-space argument. The representable-stack-fppf-locality node assumes a field, so it was not applied over S.

## Review by Q111

I read Stacks stacks-morphisms.tex lemma-inertia (050Q), the discussion immediately preceding lemma-diagonal-diagonal and its full part (1) proof (0CL0), and spaces-groupoids.tex lemma-group-scheme-separated (06P6), including its cartesian difference-map square. The item follows those sources. The testwise formulation avoids introducing a smooth-cover descent lemma: both directions are proved on every scheme test as the definitions demand. There are no new-node sources to check.

Step 1 explicitly cites the representable calculus statement that every representable etale map is smooth to justify the DM atlas hypothesis. It uses the actual statement of lem-sfb-relative-inertia-second-diagonal-geometry: it explicitly states representability of both the stack diagonal and inertia projection, the equivalence of the double product with inertia, and the identification of the second diagonal with e. Its hypotheses are arbitrary algebraic stacks over a scheme; the given DM stack satisfies the atlas condition, since etale atlases are smooth (also explicit in the representable calculus node). The cited CFG definition gives the triples and arrows used to compare scheme tests, and the closed-immersion definition supplies the scheme notion. I checked both directions of the scheme-test diagonal criterion; it is not being inferred from a definition of inertia alone.

Step 2 expands the CFG definition on a scheme test: (y,beta,v) is sent to v beta v^-1, with inverse (x,g,id) and the unique comparison arrow. It also computes the pullback of e as an identity locus, not merely the locus of fixed geometric points. Every groupoid in the latter fibre is empty or equivalent to the terminal groupoid, by the displayed equation w=alpha w and the unique arrow w2^-1 w1. Thus later arguments establish scheme representability of the actual pullback whenever they assert a closed immersion.

Step 3 uses only the existing fibre-product theorem to form G times_T G and the scheme closed-immersion definition. The theorem's statement allows arbitrary algebraic spaces over a scheme; G is such a space because p is representable, and T is the scheme already fixed. Separatedness of p gives separatedness of this G over T by the item's own definition. Testing its closed diagonal along (alpha,1) gives exactly the pullback of e computed in step 2. No theorem about closedness of a section over a field, no smooth-local descent, and no scheme-only result applied to a space is involved.

Step 4 uses the same two cited statements within the same hypotheses. For arbitrary scheme V mapping to G times_T G the pair (g,h) gives a genuine inertia object (x|_V,g^-1 h). Its closed e-pullback is exactly the scheme test of the group diagonal, naturally on all further schemes. This proves the inverse implication, retaining nilpotent structure and noncommutative composition order. These two elementary calculations are the complete argument behind 06P6, not unproved invocations of that tag. They require no separate node: each is the equality of the two explicitly described fibre functors followed by the stated scheme-test definition.

Step 5 uses lem-sfb-fibred-groupoid-representable-smooth-calculus, whose statement explicitly permits arbitrary fibred groupoids and arbitrary base-changing categories, without an algebraicity or atlas hypothesis. Its base-change and composition clauses make the absolute diagonal representable: the comparison from the relative product to the absolute product is a pullback of the scheme diagonal of S. The neutral-section identification is then written out on triples (x,y,(u,v)) using the CFG definition, with inverse and natural comparison (1,v). I corrected the preliminary draft here: it would have described all absolute diagonal tests as the same relative isomorphism sheaves without accounting for unequal maps to S. The final proof instead factors through the relative product, imposing their equality by the actual diagonal of S. It therefore uses no separatedness of S and no unproved change-of-base algebraicity assertion. The inertia projection and its scheme tests themselves are unchanged when forgetting S, so steps 3--4 apply verbatim.

I opened the statements of every cited node and copied exact excerpts into citations.json. No step uses the proof of a cited node as a black box. The algebraic-space fibre-product node is a generic tool from another unit; its role is recorded in split_report.tool_uses, without changing the maintainer's tool_uses field. All other proof dependencies are definitions or in the item's unit.

Small cases: for an empty stack every test is empty; for a scheme X the inertia projection and e are identities and the diagonal morphism is a monomorphism, consistent even when X or S is nonseparated. In particular X=S with S a doubled-origin scheme confirms the absolute clause cannot require S separated. For BG with a noncommutative finite constant group G, the scheme tests are the automorphism group spaces of torsors, and g^-1 h=1 iff g=h retains its stated order. Nonreduced test schemes are allowed throughout, so the argument does not replace closed immersions by set-theoretic closedness. No finite type, properness, quasi-compactness, flatness, or characteristic hypothesis was introduced.

I checked delivery-errors B--E individually: no new unsplit-node proof or duplicate; all objects/hypotheses and notions are supplied; TeX uses single escaped source commands; the sources have checked tags and labels; all added Mathlib searches really ran and their full outputs are saved; no attachment is claimed from sorried Lean; all non-elementary inputs are cited statements; no cycle or off-route replacement is introduced; and the equivalences are proved, not relabelled. The longest step is below 2000 characters. No SGA source or forbidden purity route is used.

Search results: both semantic phrasings, LeanSearch, Loogle and the recorded Mathlib grep were read. Semantic hits are scheme separatedness/closed diagonals or topological separatedness, not stack inertia. Loogle and grep returned no hits. Read Mathlib/AlgebraicGeometry/Morphisms/Separated.lean around its IsSeparated definition and its diagonal equivalence: its objects are schemes, so it is not an exact or one-line match for this stack statement. No unavailable service was represented as a negative result.

## Unfinished work

None in the mathematical split. The first server dry run passed at c93a34e1014. After that check I added the explicit step-1 citation for the etale-atlas-to-smooth-atlas implication and its verbatim excerpt; the final dry run and push validate that final version.
