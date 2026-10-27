# Worker report

## Files written

dag/nodes/sec-trace-formula/lem-trf-smooth-connected-open-spreading.json: statement, split using six existing dependencies; no exact Mathlib match. citations.json records one verbatim statement excerpt for every citation in every proof step. searches.jsonl retains the actual search results. No Lean files were written or compiled.

## New nodes

None. Zero new nodes and zero Mathlib leaves. The existing, reviewed lem-trf-geometrically-connected-fibre-open-spreading already states the more general flat, finitely presented, geometrically reduced result (Tag 055W). Creating a smooth version of that construction as a new lemma would duplicate it.

## Attachments

None. Searches of lean/WeilConjectures for the item tag and geometric connectedness/spreading found no declaration giving the whole prescribed embedded-fibre assertion. Slicing.lean gives covering/factorization and section-component statements; SlicingFlat.lean cites 055W but gives a covering factorization, not this assertion. GenericGeometricallyConnectedSpread.lean treats a generic fibre over an irreducible base, not an arbitrary point and prescribed fibre open.

## Literature wanted

None; no WANTED documents.

## Changes and mathematical issues

The statement is unchanged and has no dispute. Replaced the empty proof by four steps: smoothness gives the hypotheses of existing 055W; that theorem supplies the affine elementary etale neighbourhood and embedded open; smoothness survives base change; the affine-local definition proves smoothness on that open. Kept every original field and inherited Mathlib search, and appended the searches actually logged for Q92. The nearest blueprint ancestor and its inherited place are retained; the whole-blueprint searches for 055W, fibre-geometrically-connected-reduced, and geometric connectedness found no second statement of this assertion. Read the latest trace-formula chapter, sk-i-curve-zero unit, and lem-trf-local-term-locality proof. This is a generic geometric tool below the inherited horizontal-curve route, not a proposed change to the chapter or unit route.

## Tool uses

The off-unit generic tools are sbc-lem-smooth-criterion (smooth implies flat), sbc-lem-smooth-geometrically-reduced (all geometric fibres reduced), and lem-pc-proper-base-change (only smooth clause (2)). They are declared in split_report.tool_uses. The spreading theorem is already in the item's own unit. Definition citations do not replace theorem citations for flatness or reducedness.

## Not duplicates

No new-node pairs exist. The existing 055W generalization is cited, not recreated. Applying that pre-existing stronger theorem is a specialization, not moving this item's content into a new node.

## Review by Q92

I read Stacks more-morphisms.tex, Tag 055W (lemma-fibre-geometrically-connected-reduced), and Tag 057J (lemma-normal-morphism-irreducible), especially its opening application of 055W. I also read Morphisms 01VF (lemma-smooth-flat), 01VB (lemma-base-change-smooth), 01VC (lemma-open-immersion-smooth), 01VA (lemma-composition-smooth), and Varieties 056T (lemma-smooth-geometrically-normal). These supply exactly the smooth specialization of 055W. There are no new-node sources to audit.

For step 1 I opened sbc-lem-smooth-criterion: its equivalence explicitly includes flatness, so the forward implication applies to the given smooth h without extra base hypotheses. I opened sbc-lem-smooth-geometrically-reduced: its statement explicitly gives geometrically reduced fibres for every smooth morphism. Finite presentation is given in the item, not inferred from smoothness alone.

For step 2 I opened the complete statement of lem-trf-geometrically-connected-fibre-open-spreading. Its hypotheses are flatness, finite presentation, geometric reducedness of every fibre, and a geometrically connected open T in the indicated scheme-theoretic fibre. Step 1 and the item's hypotheses supply all four. Its conclusion explicitly supplies affine S_1, an etale map, a point above s with residue-field isomorphism, a quasi-compact open V, connectedness of all fibres including nonemptiness, and equality of the specified fibre as an embedded open. Thus no residue extension, abstract identification, or loss of quasi-compactness is hidden in the step.

For step 3 I opened lem-pc-proper-base-change and read clause (2). It states smoothness of arbitrary base change independently of clause (1); therefore properness is not being assumed. The second projection p is precisely the base change of h along a.

For step 4 I opened def-sbc-smooth-morphisms and def-weil-open-immersion. The former explicitly identifies smoothness with the affine-local smooth-ring-map definition; the latter identifies V with the open subscheme carrying the restricted structure sheaf. Every affine open of V is consequently an affine open of the ambient scheme with the very same ring map to an affine target open. This is an elementary restriction argument, not an uncited composition theorem or a new lemma. The geometric conclusions obtained in step 2 concern that same composite v. All four steps are under 2000 characters; there is no long step hiding another comparison.

I checked the B--E delivery-error cases against these files: the split creates no restatement node, uses no proof-internal construction of a dependency, and every non-elementary fact is a cited statement. citations.json has exact verbatim excerpts of all six statements. No SGA source is used. The statement definitions remain unchanged. I tested the empty-base case (there is no s), the empty T case (excluded by connectedness including nonempty), dimension-zero smooth families, nonclosed s, and non-Noetherian bases. No separatedness, properness, fixed relative dimension or base Noetherian hypothesis enters. The base may have other fibre components: 055W preserves the whole chosen open T, not just a neighbourhood of one of its points. The searches returned smooth charts, etale loci/algebras and fibre definitions, none of which asserts the required simultaneous spreading. Two semantic phrasings and the literal grep/Loogle checks were recorded as returned.

## Unfinished work

No unfilled steps remain in this one-level split. Dependencies retain their existing stage states; no claim is made that this is already a Lean proof. Required server validation and direct delivery follow this report.
