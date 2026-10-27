# lem-a1-space-open-factor-scheme-tests — Q29

## Files written

- `dag/nodes/sec-purity-real-sheaves/lem-a1-space-open-factor-scheme-tests.json`: statement, split in five steps, no exact Mathlib match.
- `citations.json`: ten step/node entries with verbatim statement excerpts.
- No new nodes and no Mathlib leaves. The existing searches in the item are preserved; five actual searches from this attempt are appended with their exact queries and results summarized from `searches.jsonl`.

## Attachments

None. The item-id and AlgebraicSpace searches in `lean/WeilConjectures/` found no declaration stating the item. Searches for open subspaces returned topology/sheaf results and scheme results, which do not supply all clauses for algebraic spaces. No compiler or Lean-writing tool was used.

## Literature wanted

None.

## Corrections and findings

The statement is unchanged, and no statement dispute was found. The former node had no proof. Stacks 03IE proves the open-factor assertion by pulling back the open and using its full point image. Stacks 06NF proves the scheme-source etale-image case by identifying its scheme tests using the monomorphism of the open inclusion. The same test argument works for the item's arbitrary algebraic-space source. Stacks 03H4 gives the point-image equality under arbitrary base change. The proof uses these results through the existing point-open calculus node, rather than creating new copies of the individual clauses.

The non-Mathlib dependency `lem-trf-space-fibre-products-etale-covers` is a generic categorical tool filed in the trace-formula chapter. Its statement supplies existence of the sheaf pullbacks and their universal property; its atlas-cover assertions are not needed. This is declared in `split_report.tool_uses`. The algebraic-space definition is also cited explicitly when interpreting representable etaleness. The unit's Rankin–Selberg proof and the chapter route are not changed. The geometric auxiliary branch is below the blueprint node `lem-a1-affine-hc0`, whose current main-20261015 text was read.

Mathlib searches: LeanSearch, two LeanFinder phrasings, Loogle with the expected open-immersion lift names, and a source grep ran through the required msearch command. All services answered. The candidates are for schemes, presheafed spaces, or locally ringed spaces. Reading `Mathlib/AlgebraicGeometry/OpenImmersion.lean` lines 701, 705 and 708 verifies that `lift`, `lift_fac`, and `lift_uniq` quantify over schemes; they do not prove the algebraic-space assertion or identify the fppf-sheaf scheme tests. The grep returned no AlgebraicSpace/OpenSubspace hits.

## Not duplicates

No new nodes. Whole-DAG searches by 03IE, 03H4, factor-through-open-subspace and open-subspace keywords found the parent open-image result (which depends on this item), the independent point-open-calculus node (reused), point-lifting nodes for scheme sources, and the invariant-open quotient construction. The latter statements neither replace this complete item nor justify citing the parent circularly. Blueprint searches for `open subspace` and `03IE` found no equivalent blueprint node. The ancestor command returned `lem-a1-affine-hc0`; the existing precise provenance and via chain are retained.

## Review by Q29

I read `spaces-properties.tex` at lemma-points-cartesian (03H4), lemma-open-subspaces (03BZ), lemma-factor-through-open-subspace (03IE), and lemma-etale-image-open (06NF), together with `spaces.tex` at lemma-base-change-immersions. I also read the statements of all four nodes cited by the five proof steps: the open-subspace definition, algebraic-space definition, fibre-product theorem and point-open calculus. No new node needs an additional source review.

In step 1 the fibre-product theorem explicitly supplies an algebraic space and its categorical fibre-product property. The open-subspace definition states representability by an open subscheme for every scheme test. Writing the iterated pullback on each test scheme proves openness directly; no separate theorem about representable morphisms is hidden there. The point-open calculus states the exact image formula for arbitrary algebraic-space morphisms, not just for atlas maps. It therefore gives both required inverse-image identities with h=f and h=g, without imposing a hypothesis on either map.

In step 2 that same calculus explicitly says that an open subspace with full point image equals its ambient space. Containment of the image of f, the actual hypothesis here, gives that full point image. I use the projection inverse to construct the factor, and sectionwise injectivity of the subfunctor inclusion proves its uniqueness. This is valid for an open inclusion; it would not justify factorization through an arbitrary locally closed immersion. No such extension is made.

Step 3 writes the inverse comparison on all test-scheme sections: equality after the inclusion of J implies equality in J because J is a subfunctor. Restriction preserves those pairs, so the construction is an isomorphism of sheaves and of algebraic spaces over T. This is a short argument from the cited universal property and subfunctor definition, and is marked elementary. It is not left as an unnamed comparison lemma.

For step 4 I checked that the algebraic-space definition defines representable etaleness by exactly the projections to every scheme T. The isomorphism from step 3 preserves those projections. I separately checked both parts taken from the point-open calculus: injectivity of the point map for an open subspace and the criterion that a representable point-surjection is surjective on every scheme base change. Representability of the factor has already been established by the scheme-test argument before applying that criterion. Equality of the original point image with |J| is used only for this surjectivity clause; containment suffices for the factor and etaleness clauses.

Step 5 uses the arbitrary-morphism image formula already stated by the calculus. Substituting im|f|=|J| and step 1's description of J_G yields the asserted equality. Neither f nor g needs to be etale for this last conclusion. In particular I did not assume that the topological space of a fibre product is itself the set-theoretic fibre product; only the cited surjection/image formula is used.

I checked empty Y and empty J (containment forces an empty source when J is empty), J=X (the factor and comparison are identities), proper image containment (which supplies no surjectivity assertion), and arbitrary nonflat/non-etale g. Each argument still applies. The comparison construction is valid for T empty and for disconnected tests. No new hypotheses, finite-type condition, quasi-compactness claim, or coefficient-category identification was introduced. Every citation excerpt was checked as a literal substring of its node's statement. All steps are below 2000 characters, and the only elementary step is the explicit compatible-pair comparison.

## Unfinished work

None in this one-level split. The reused point-open calculus remains its own independent stage-1 item; no proof of it or of another worker's node is included here. Server dry run and delivery are the final checks.
