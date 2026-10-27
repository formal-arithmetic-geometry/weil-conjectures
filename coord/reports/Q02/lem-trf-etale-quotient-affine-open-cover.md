# Q02 stage-1 report: lem-trf-etale-quotient-affine-open-cover

## Files written

- dag/nodes/sec-trace-formula/lem-trf-etale-quotient-affine-open-cover.json — existing statement, now split into seven proof steps; Mathlib searches found no declaration giving the full sheaf-quotient assertion.
- citations.json — one entry for every step/node citation, checked as a literal substring of that node's statement.
- report.md; searches.jsonl is the genuine log produced by msearch.py.

New nodes: 0. New Mathlib leaves: 0. Existing Mathlib leaves reused: scheme coproducts, source locality of etaleness, and open immersions being etale.

## Attachments

None. Searched the live project's WeilConjectures source for the exact blueprint tag, etale quotient and open-cover terminology, and equivalence relations. No declaration states this item. The finite-group quotient gluing declarations in WeilConjectures/Mathlib/AlgebraicGeometry/ColimitsOver.lean concern finite monoid actions and do not supply this general fppf relation quotient statement.

## WANTED

None. All sources used are in literature/stacks-project/.

## Problems found and corrections

The statement is sound as written; no statement change or dispute. Its initially empty proof hid several hypotheses and the meaning of the covering assertion. In particular, finding-opens needs surjectivity of both relation projections, which follows from their common reflexivity section, and local surjectivity must be proved for sections of the sheafification rather than assumed for pointwise sections. Steps 5 and 7 supply these arguments explicitly. The direct restriction to V_i and the restriction through the coproduct are compared on test-scheme points in step 4, including the induced canonical sheaf maps.

The existing node has no lean_audit field. Its imported search records came from its creation in another sandbox; the delivered records are the fresh searches actually performed here, retained in searches.jsonl. Two distinct semantic phrasings, Loogle, grep and LeanSearch were run. The Loogle hit Etale.instOfIsOpenImmersion is a match only for the already existing auxiliary Mathlib leaf, not the item. LeanSearch and LeanFinder hits were covers of schemes or inverse-limit auxiliary covers, not representable open immersions into an unrepresented quotient sheaf. Read the open-immersion etale instance in the Mathlib source. No compiler or Lake was run.

## Not duplicates

No new nodes were created. Reused lem-trf-etale-relation-restriction-quotient (02WT/045Z) and lem-trf-etale-relation-finding-opens (02WU), rather than creating special cases. The parent lem-trf-etale-relation-quotient cites this item and is intentionally not used, avoiding a cycle. Searched the whole DAG by these tags and relevant concepts and the whole imported blueprint with blueprint_refs.py (affine open, coproduct, etale quotient, relation restriction). No blueprint statement duplicates the full item. Its blueprint ancestor and via chain are retained; same_as remains empty.

## Review by Q02

I read Stacks spaces.tex, theorem-presentation (02WW), from its replacement by a surjective etale cover through its restricted affine quotient paragraph. I read lemma-pullback-etale-equivalence-relation (02WT) and lemma-finding-opens (02WU), including the latter's full hypotheses and the start of its descent proof, and groupoids.tex lemma-quotient-pre-equivalence-relation-restrict (045Z), including its injectivity and covering argument. These sources do not assume an algebraic-space structure on either quotient for the restriction or finding-opens conclusions. I also read schemes.tex lemma-glue and lemma-glue-schemes (01JB/01JC), morphisms.tex lemma-etale-characterize (02GJ) and lemma-open-immersion-etale (02GP), and sites.tex lemma-sections-sheafification (00WK). There are no new-node sources to audit.

For step 1 I opened lem-weil-pbc-scheme-coproduct-family: its statement gives existence, the universal map, disjoint images, covering, and clopen coprojections, exactly the data used. Surjectivity of g is proved on points using the given cover, not inferred from a nonexistent global section.

For step 2 I opened lem-weil-pbc-open-immersion-etale and lem-weil-pbc-etale-local-on-source: they assert respectively that an open immersion is etale and the equivalence between etaleness and etaleness on an arbitrary open source cover. The summands from step 1 form such a cover. I opened def-weil-etale-morphism to check it explicitly includes flatness and local finite presentation, and def-pc-fppf-site to check its covering convention is jointly surjective families of such morphisms without a quasi-compactness assumption. Thus even an infinite coproduct gives the needed cover.

For step 3 I read the entire statement of lem-trf-etale-relation-restriction-quotient. It gives both preservation of the etale equivalence relation and the canonical isomorphism when the etale map is surjective. The map g satisfies precisely these hypotheses by steps 1 and 2. The assertion used is the statement, not its proof.

For step 4 the same restriction statement applies to each open summand, which is etale by the existing open-immersion lemma; no surjectivity of the individual summand is claimed. I checked def-pc-fibre-product supplies its test-scheme universal property. The description of a restricted relation is written out explicitly, so the equality with direct restriction is a tuple calculation, not a hidden geometric comparison theorem. I read def-weil-pbc-sheafification: its universal factorization property is sufficient to identify the two canonical maps after identifying their pointwise quotient maps. No exactness or plus-construction claim is taken from that definition.

Step 5 uses the definition of etaleness only for flatness and local finite presentation. Reflexivity at the test scheme U itself supplies e:U -> R_U; composing with the two projections is the identity, so both projections really are surjective on points, including when U is empty. This is a short direct consequence of the equivalence-relation hypothesis and is marked elementary. Thus every hypothesis of finding-opens is present, with no representability assumption smuggled in.

For step 6 I read lem-trf-etale-relation-finding-opens in full. Its conclusion explicitly gives the open subscheme representing the pullback along every h_T -> Q. Transport along the already proved isomorphism Q -> F is just the universal property of the fibre product; it proves the actual requested representable-open assertion for the composite, not merely an open image on topological points.

For step 7 I read lem-weil-pbc-site-sheafification-sections-local: it supplies local quotient-presheaf sections, not maps to V; the step then chooses a representative in each quotient set. The V_i cover is fppf by the already cited open-immersion theorem, the definition of etaleness and def-pc-fppf-site. I opened def-weil-pbc-sites-and-cohomology and checked it explicitly states both the base-change and composition axioms for coverings. Applying these to T_a x_V V_i produces a covering of T, and the projection to V_i supplies the desired F_i-section. The equality of images is given by the defining commutative fibre-product square. This expands precisely the sentence 'It is clear that coproduct F_i -> F is surjective' in 02WW without using the later algebraic-space presentation theorem.

I tested the diagonal relation (the conclusion becomes the ordinary open cover of V), a relation identifying different components (chart images in the quotient may coincide, which is allowed), redundant and empty charts, an infinite affine cover, and the empty scheme with the empty index set. No affineness of intersections, finite index set, separatedness, or quasi-compactness is required. An empty-index cover forces V empty; a section of the empty quotient can exist only on a test scheme locally admitting a map to the empty scheme. The site-cover argument handles this case without inventing an index for a nonempty domain.

Against delivery-errors B--E: the item introduces its objects and retains its definition dependencies; no new statement-only nodes or duplicate clauses were introduced; every non-elementary input is an existing cited node whose statement was opened; quotation membership was checked before writing citations.json; the proof never cites its parent; the split carries the affine-refinement and local-lifting argument rather than relocating the conclusion into a new node. Every step is below 2000 characters, and the restriction comparison and refinement constructions are written explicitly. No SGA source is used. Generic local sheafification and site-cover axioms from another unit are declared in split_report.tool_uses because they are tools for the same Stacks route. This item is not its unit's key node, so no unit realization record is changed.

## Unfinished work

None in this one-level split. Existing cited unsplit facts remain with their existing nodes; their proofs are not part of this item. Required server checks and delivery are recorded by deliver.py.
