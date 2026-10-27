# Q157: lem-sfb-relative-universal-flat-open

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-relative-universal-flat-open.json: statement, split into four proof steps; no Mathlib match after searches. The statement, stmt_deps, source and creation metadata are retained.
- citations.json: one verbatim statement excerpt for every node cited by each proof step.
- searches.jsonl: the search command's actual records; five fresh searches, including two LeanFinder phrasings.
- report.md: this report.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. The requested blueprint tag and the universal relative flatness-open notion were searched in lean/WeilConjectures, with related source also read in lean/Sheaf. No project declaration states the item exactly with a completed proof. The relative source-locus theorem in lean/Sheaf/AlgebraicGeometry/RelativeFlatLocusBaseChange.lean has a sorry and states the existing prerequisite, not this item.

## WANTED

None. All sources used are present locally.

## Corrections and source comparison

No statement error was found. The live item is unsplit and the sandbox initially held no item, report or search log; no repair note exists. Its statement matches Stacks Tag 05XB specialized from algebraic spaces to schemes: p is flat, locally of finite presentation and a closed map, while q is only locally of finite type. Closed does not mean universally closed here. The proof uses closedness only before base change. The final sentence of the source is expanded using the exact subset image identity, avoiding an unjustified assertion that the underlying topological space of a scheme fibre product is a topological fibre product.

The inherited null blueprint ancestor was retained: tools/blueprint_refs.py ancestor prints None. Its precise from.place and via chain already identify the direct-image alteration subargument through the universal-isomorphism and surjective-flat opens. I read the chapter and unit records and the current blueprint's det-thm-sf-ctf-stability-direct-images proof, especially (3). This is a generic scheme-theoretic input below that route, not a replacement of the unit argument; I changed neither chapter nor unit. Searches of the whole imported blueprint for flat locus, universal flatness, 05XB and where-flat found no matching blueprint node, so same_as remains [].

## Not duplicates

No new node was created. Existing lem-sfb-relative-flat-locus-base-change is reused for the source flat locus. Existing lem-weil-pbc-base-change-image and lem-weil-pbc-morphism-factors-through-open-subscheme supply the two generic scheme facts in the universal property. The former has the identity for every subset, not only the whole scheme. The latter is explicitly for an open subscheme, which is crucial. Neither the relative source locus alone nor the surjective-flat or universal-isomorphism opens is an exact duplicate of the item.

## Review by Q157

I read the complete statement and proof of Tag 05XB in spaces-more-morphisms.tex, and Tag 05VK in more-morphisms.tex. The former constructs the complement of the image of the nonflat locus; the latter states exactly the open source locus and its formation under arbitrary parameter base change. I also read the subset-image formula in the proof of Tag 01S1 in morphisms.tex, and Tags 01HI and 01IK in schemes.tex for open restriction and the affine-neighbourhood verification. The tags were checked against tags/tags. There are no new-node sources to audit and no SGA source is used.

Step 1 cites the statement of lem-sfb-relative-flat-locus-base-change: its p is flat and locally finitely presented, its q locally of finite type, and its commuting triangle is precisely the present one. It gives both openness of U and the full equality Flat(f_T) = pi_X^{-1}(U), not merely preservation of already-flat maps. I read its statement rather than relying on its proof. No properness, Noetherianity, quasi-compactness, flatness of q or finiteness of T is added.

Step 2 is the elementary closed-image/complement argument plus the local scheme check. Closedness of p sends the closed complement C to a closed subset. The cited principal-open-basis statement gives a D(a) around each point inside F and the cited principal-localization open immersion identifies its ringed open with an affine scheme. Thus the restriction is locally affine by the scheme definition, and the restricted sheaf inclusion meets the open-immersion definition. I read all four cited statements; the principal-open topological identification alone would not identify the sheaf, so I also cite the open-immersion statement. This argument is short and has no hidden sublemma needing a new node.

Step 3 uses the full arbitrary-subset identity in lem-weil-pbc-base-change-image, with its X = X, Z = S, Y = T and C = X minus U. Its square is exactly the defining fibre product. Together with Step 1 it identifies the image of the nonflat locus in T as h^{-1}(p(C)). The definition of a flat morphism identifies everywhere flat with an empty nonflat locus; a subset has empty image exactly when it is empty. This gives both directions, including the necessity direction when h is neither flat nor surjective. I explicitly avoided assuming p_T is closed. I read the cited flat definition and subset-image statement in full.

Step 4 applies the open-factorization node to the open subscheme already constructed; that statement gives a unique scheme morphism when the image lies in F. The converse is immediate from the inclusion's image. This uses the statement for open subschemes, not a false extension to closed or locally closed strata. The factorization is a scheme factorization with its sheaf map, not only a continuous map. The citations file copies an exact sentence giving this conclusion.

I checked B1–B10: there are no new statement-only nodes to misformat or duplicate; TeX is singly escaped in decoded JSON; all proof sources have tags and labels; all five fresh searches were actually run by msearch.py and copied from its log. LeanSearch, Loogle, LeanFinder and grep were available. The semantic hits were global flatness, its stability under base change, affine/stalk criteria, and UniversallyOpen.of_flat; I read the Flat and UniversallyOpen source declarations. None constructs the universal parameter open. The second semantic phrasing also found no match. Earlier item search records are retained unchanged.

For C1–C8, each non-elementary input has an existing cited statement, every uses entry has a verbatim quote in citations.json, and the union equals proof_deps. The relative flat-locus node is in this unit; the other statement tools are Mathlib leaves and are generic, so no off-route replacement or undeclared tool use is needed. For D1–D5, the proof actually constructs F and establishes the equivalence by the subset identity; no clause has merely been renamed into a new node. For E1–E7 I checked all hypotheses and the correct fibre-product square as described above, and no source error was found. All four steps are under 2000 characters (330, 583, 619, 371).

Small cases: if X is empty, C is empty and F=S, and every f_T is flat vacuously. If f is flat everywhere (including f=id), again F=S. If a fibre of p is empty, its base point belongs to F, as it must. Over a field S=Spec k, with X=Spec k, Y=Spec(k[epsilon]/epsilon^2), and f induced by epsilon -> 0, p is flat, finitely presented and closed, q is finite type, and f is nonflat. Then U=F=empty; after any nonempty k-scheme base change the image formula and the source-locus equality retain a nonflat point. The empty test scheme factors through empty F and has an empty, flat base-changed morphism. Nonreduced test schemes cause no exception: factorization into an open is controlled by the underlying image, unlike factorization into a closed subscheme.

## Unfinished

Nothing in the mathematical split. Delivery validation and push are recorded below when completed.
