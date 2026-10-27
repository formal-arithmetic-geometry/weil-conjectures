## Worker report

Files written:
- dag/nodes/sec-six-functors-basics/lem-sfb-space-universal-isomorphism-open.json: split the item in six complete steps, without changing its statement.
- dag/nodes/sec-six-functors-basics/lem-sfb-space-universal-surjective-flat-open.json: statement; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-space-universal-closed-immersion-open.json: statement; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-space-surjective-flat-closed-immersion-isomorphism.json: statement; no Mathlib match.
- citations.json: verbatim statement evidence for every use in every item step.

Attachments: none. Searched WeilConjectures for the blueprint tag, AlgebraicSpace, isomorphism loci, and flat/closed/surjective variants. The loci found in scheme modules do not state this arbitrary-space item.

WANTED: none.

The imported statement is faithful to 05XD. The earlier scheme-only nodes do not cover algebraic spaces or space-valued parameter changes. Keeping that distinction is necessary here. The current blueprint latest direct-images proof was read; this is an inherited supporting geometric prerequisite, not a change of the sketch route. No statement dispute, no abandoned clause, no incomplete work. No Lean file or compiler was used.

Searches: reused the three interrupted-turn searches after reading their logged hits; completed the item semantic search. For each new node ran leanfinder twice with different phrasings, leansearch, loogle, and grep through the required msearch.py. All were available. Hits are scheme open-map/stability/descent results or scheme closed-immersion criteria. Read FlatMono.lean:25--30 and the scheme-only UniversallyOpen definition. The existing scheme criterion already records the FlatMono specialization, and was not duplicated as a new scheme leaf. searches.jsonl retains every actual query. Whole DAG searches by tags 05XA, 05XC, 05XD, 04PW and keywords, and blueprint_refs searches for where-surjective-flat, where-closed-immersion, surjective flat, flat closed immersion, universal closed immersion, closed immersion locus, where-isomorphism and isomorphism locus were read. No imported blueprint statement gives the general-space inputs.

## Not duplicates

lem-sfb-space-universal-surjective-flat-open vs lem-sfb-open-image-universal-surjectivity: the existing result assumes an already open image and proves only a scheme surjectivity locus; the new result also constructs the flat locus and treats algebraic spaces.

lem-sfb-space-universal-surjective-flat-open vs lem-sfb-universal-surjective-flat-open: the existing result quantifies only schemes; the new statement allows algebraic spaces in the diagram and in every parameter change.

lem-sfb-space-universal-closed-immersion-open vs lem-sfb-universal-closed-immersion-open: the existing result is the scheme specialization; the new statement allows arbitrary algebraic spaces and space-valued parameter changes.

lem-sfb-space-universal-closed-immersion-open vs lem-sfb-fibrewise-very-ample-evaluation: the existing result concerns cohomology/base change of a line bundle on a flat proper curve and its projective evaluation embedding, not a general diagram closed-immersion locus.

lem-sfb-space-surjective-flat-closed-immersion-isomorphism vs lem-sfb-universal-isomorphism-open: the existing result is a universal parameter-locus theorem for schemes; the new criterion concerns one surjective flat closed immersion of algebraic spaces with no parameter-family hypotheses.

lem-sfb-space-surjective-flat-closed-immersion-isomorphism vs lem-sfb-surjective-flat-closed-immersion-isomorphism: the existing Mathlib leaf is a morphism-of-schemes criterion; the new result requires passing to scheme charts of an arbitrary target algebraic space and gluing their inverse sheaf maps.

lem-sfb-space-surjective-flat-closed-immersion-isomorphism vs lem-sfb-space-universal-isomorphism-open: the item constructs an open parameter locus from six family hypotheses; the new criterion concerns one already surjective flat closed immersion and has no parameter locus.

## Review by Q131

I read spaces-more-morphisms.tex, lemma-where-isomorphism (05XD) in full, its two input statements lemma-where-surjective-flat (05XC) and lemma-where-closed-immersion (05XA), and their proofs. I also read morphisms.tex lemma-characterize-flat-closed-immersions (04PW), especially its final scheme-theoretic factorization assertion. The space criterion is exactly the final representable-map reduction of the 05XD proof. It needs a genuine chart/base-change comparison, so it is a separate unsplit input rather than being silently treated as a scheme theorem. Its later proof can test a target atlas, apply the existing scheme criterion to each surjective flat closed immersion, and glue the unique inverse maps as sheaf maps. This proof explanation stays in the report; the new node is statement-only.

For step 1 I opened def-sfb-space-morphism-properties, def-sbc-locally-finite-presentation, and def-weil-finite-type-morphism. Universal closedness explicitly quantifies all space changes, including identity, and the displayed finite presentation explicitly has finitely many generators, which proves the local finite type implication on the same charts. No cancellation or finiteness theorem is smuggled into this elementary step.

For step 2 I compared every hypothesis and the all-space universal conclusion to the new 05XC node: p is lfp, flat, closed; q is lft, closed. In particular q need not be universally closed or flat. For step 3 I compared to the new 05XA node: p is lft and universally closed, q separated. Neither p separated nor q flat is required. Both input statements introduce their own S,A,C,B and tests T, spell out the relevant morphism properties and define surjectivity/closed immersion where used. These are independent weaker-property locus results, not the isomorphism assertion or its clauses renamed.

For step 4 I opened def-a1-space-open-subspace and def-trf-algebraic-space. Their statements give subfunctors represented by opens on every scheme test and identify maps as natural transformations. The finite intersection is constructed sectionwise; on tests it is just intersection of opens with restricted structure sheaf, and a pair of lifts has the same section of B, so it gives a unique natural lift to the intersection. This works for an algebraic-space domain T; no topology-only factorization through a closed subspace is used. For step 5 I opened the new space criterion, the space-property definition, the algebraic-space definition and def-weil-closed-immersion. The two locus conclusions supply exactly its surjective, flat, representable closed-immersion hypotheses for f_T. For the converse an inverse identifies every chart/test with an identity, giving the three properties directly from their definitions. No unquoted arbitrary-base-change stability theorem is needed. Step 6 is the identity scheme test in the open-subspace definition. Every citation has a verbatim quote in citations.json; proof_deps is exactly the union of uses.

I tested the new statements at identities (the locus is all B), the empty source and empty target (the isomorphism criterion requires both empty), and nonreduced bases. The inclusion Spec(k) into Spec(k[e]/e^2) is surjective and closed but not flat: it is not an isomorphism, and the criterion correctly excludes it. No finite presentation was added to closed immersions, and no scheme-only test replaces the all-space universal quantifier. The scheme-only same-tag nodes have been read and distinguished above; no node here can be replaced by them without a descent argument. The assembly proof does not rely on the proofs of cited nodes, only their statements. All non-elementary steps are below 2000 characters and use explicit theorem nodes. I checked delivery-errors B--E: standalone statement-only nodes, single TeX escaping, exact labels/tags, genuine logged searches, complete definitions, no false C4 citations, no unnamed non-elementary facts, no circular or clause-restating split, and all hypotheses present. I retained the original statement and inherited blueprint chain, and filled the item's split report. There was no mathematical correction to make.
