# Stage-1 report: lem-sfb-affine-closed-pinching-pushout

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-affine-closed-pinching-pushout.json`: item, statement unchanged, seven-step split; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-fibre-product-spectrum-topology.json`: one new statement-only unsplit node, Stacks 0B7J; no Mathlib match.
- `citations.json`: one verbatim statement excerpt per step/node citation (19 entries).

The sandbox also contains the honest `searches.jsonl` produced by msearch.py, this report and two sandbox-only JSON preparation scripts. No repository file, Lean source, launcher file or unit realization was edited. No compiler, Lake, build or local delivery-check script was run. This item is not the unit's key theorem.

## Attachments

None. Searches in the live `lean/WeilConjectures/` for the item's blueprint tag, pinching, 0ET0, 0B7J, and closed/pushout phrases found no declaration stating this item. The affine ring-sheaf pushout results in that tree concern tensor products and scheme pullbacks; the open-immersion pushout results concern open gluing. Neither proves closed pinching.

## WANTED

None. All mathematical sources used are present in `literature/stacks-project/`.

## Corrections and route

The current item already correctly states the general Stacks 0ET0 theorem: only A -> D is required surjective; T -> D need not be finite. I retained every hypothesis and clause, including zero rings. Its inherited proof was empty. The seed's older Mathlib queries mentioned a finite map; the fresh searches test the general surjective-map statement and the topological lemma, with two semantic phrasings.

I read the chapter record and the unit record and retained their route: this is the affine conductor-square prerequisite below persistent-node normalization in the alteration branch. It does not replace any step of the constructibility unit. The inherited ancestor lookup prints `None`, and the item's existing blueprint.from.node is null. I retained that supplied lineage, copied it to the new node, and prepended this item to the inherited via list. I filled same_as after whole-blueprint searches. No imported blueprint fields were changed.

The written proof is marked `proof_origin.by = agent`: it realizes the matching-structure-sheaf argument of 0ET0 on principal affine charts and writes out the target-chart gluing, rather than appealing to the quasi-coherent-module equivalence in the source's first paragraph. It uses the source's topology theorem and the actual localization argument of 01Z8. The item-level choice stays within the affine pinching prerequisite and uses no alternative unit route. There are no undeclared off-unit tool statements: the reused general tools are Mathlib leaves.

## Source error

In the local text of 0ET0 the second displayed direct-image formula for (n')_* O_{T'} has incorrectly swapped subscripts: m' has source S' but is applied there to O_T, and the denominator and n_* factor also have incorrect sheaves. The well-typed formula, in this item's names, is h_* O_Q = f_* O_Y times over (f|_E)_* O_E with g_* O_W. The source's first displayed sheaf formula and its argument specify this correct identity. Our principal-open matching rings use exactly A_a times over D_d with T_t, so do not reproduce the typographical error. Neither the imported statement nor the Stacks statement needs correction.

## Mathlib and duplicate searches

All fresh searches were run through the required msearch.py and are preserved verbatim as tool/query records with the raw logged result summaries in mathlib_searches. Searches included leanfinder for a spectrum of a fibre product over a surjection being a scheme pushout, two topological pushout phrasings, LeanSearch for both forms, Loogle `PrimeSpectrum, "pushout"` and `"PrimeSpectrum", "pullback"`, and source grep in AlgebraicGeometry, RingTheory/Spectrum and all Mathlib. No service was unavailable. Loogle's first query found rank-at-stalk invariance for ring pushouts, and its second found nothing. Semantic hits were Spec of a ring pushout giving a scheme pullback, spectrum embeddings induced by surjections, or the definition of Spec. I read the candidate Spec/pushout declarations at Mathlib/AlgebraicGeometry/Pullbacks.lean:794-804 and the open gluing instances at Limits.lean:709-727. The arrows and hypotheses distinguish these from both requested pushouts. The hits are not matches, so there are zero new Mathlib leaves.

Before creating the topology node I searched the whole DAG for 0B7J, points-of-fibre-product, topological pushouts and ring fibre products, and searched the whole imported blueprint using blueprint_refs.py with 0B7J, topological pushout, pinching, pushout, fibre product and fiber product. No blueprint node states this topology result. Existing closed-union pushout and dual-number pushout nodes are special cases, not a general topological theorem. The new node is not an elementary localization identity, and is not the scheme universal property moved to a new name: it says nothing about structure sheaves or scheme morphisms. Its proof field and proof_deps are empty.

## Not duplicates

- lem-sfb-fibre-product-spectrum-topology vs lem-sfb-affine-closed-pinching-pushout: the new node concerns only continuous maps from prime spectra to arbitrary topological spaces and joint surjectivity; the item constructs and uniquely glues locally ringed space morphisms to arbitrary schemes. The matching-ring and scheme-gluing argument remains in the item's steps.
- lem-sfb-fibre-product-spectrum-topology vs lem-trf-closed-union-pushout: the latter concerns scheme-theoretic unions of two closed subschemes of an ambient scheme, hence two closed maps, not arbitrary T -> D and a topological pushout.
- lem-sfb-fibre-product-spectrum-topology vs lem-sc-dual-number-scheme-pushout: the latter concerns the wide pushout of finitely many dual-number thickenings over a field. It does not state the general topological ring-fibre-product theorem.

No existing node other than the item cites 0B7J; none of these comparison nodes is cited in the proof.

## Review by NO

I checked delivery-errors B through E with the node statements and the cited sources open. In particular I read more-morphisms.tex, lemma-basic-example-pushout (0ET0), more-algebra.tex, lemma-points-of-fibre-product (0B7J) and its Situation, and lemma-diagram-localize (01Z8). For exactness I read algebra.tex, proposition-localization-exact (00CS); for affine charts I read schemes.tex, lemma-standard-open-affine (01I3); for gluing I read schemes.tex, section-glueing-schemes, and sheaves.tex, lemma-mapping-property-glue and its reference to lemma-glue-maps (04TN). The new topology statement is exactly 0B7J with A'=A, A=D, B=T, B'=P, up to swapping the order of the two product factors. Joint surjectivity is proved explicitly in its first proof paragraph. I did not claim its nontrivial topological quotient assertion elementary.

1. Step 1 uses def-weil-affine-spectrum for contravariant functoriality. Its statement expressly supplies contravariance and the bijection for affine morphisms. The P-module kernel computation is written out and is elementary, not outsourced to a new node. The difference map is P-linear because both scalar structures on D agree.
2. Step 2 uses lem-weil-pbc-localization-module-exact. I opened its statement: it preserves exactness of any three-term R-module sequence, not merely a definition of flatness. Apply it separately at P in 0 -> P -> A direct-sum T and at A direct-sum T in P -> A direct-sum T -> D. Localizing zero is zero by fractions. Thus both injectivity and the kernel assertion follow. The powers of p act on the three factors as powers of a, t and d. The finite direct sum comparison is the explicit common-denominator map; it needs no extra finite-product lemma. This proves the full matching-ring isomorphism, including compatibility with both projections.
3. Step 3 cites the new topology statement for both existence of the continuous h and joint surjectivity. I checked agreement on E is exactly its compatibility hypothesis. It cites lem-weil-pbc-affine-opens-basis for the affine target neighbourhood, and lem-weil-pbc-spec-localization-away-basic-open for a principal source neighbourhood inside h^{-1}(V). These actual statements supply the required neighbourhoods. During review I replaced the less explicit reference to the scheme definition by the existing affine-basis theorem.
4. Step 4 uses def-weil-affine-spectrum for the two contravariant ring maps and their equality on E. It uses lem-weil-pbc-principal-localization-open-immersion, whose statement identifies Spec of the localized ring with the actual principal open as a scheme, not just a homeomorphic space. It uses def-weil-open-immersion for restriction to open subschemes. Factorization through an open target is restriction of the given locally ringed space morphism, with the same local stalk maps. The inverse-image equalities are checked by contraction of primes. The ring map into P_p is an explicit pair followed by the isomorphism of step 2. Its composites are the prescribed maps, so functoriality gives both required scheme equalities. The topology node's joint surjectivity identifies its underlying map with h. Nothing is inferred from mere image containment for a closed immersion.
5. Step 5 uses the affine spectrum correspondence and the principal-open scheme identification again. Its equality test is only two affine ring maps whose composites with an injective map P_r -> A_{a_r} times T_{t_r} coincide. This is an elementary application of the injection already proved, not a new general scheme-pushout lemma or a circular use of the item.
6. Step 6 uses the existing affine-open basis theorem on the open V intersect V', and the principal-open basis theorem on Q. It uses open restriction and lem-weil-pbc-scheme-morphism-gluing, whose statement supplies both unique gluing and equality detected on an open cover. I checked its statement rather than a construction in its proof. I did not assume affine intersections affine or Z separated. The maps on a sufficiently small D(r) factor through the same affine target and step 5 proves their equality. Only then are they glued. The inverse-image covers of Y and W prove the resulting morphism has the prescribed composites.
7. Step 7 uses the topology statement to give any competing map the same underlying h, open restriction to the chosen affine V, and scheme gluing to pass from affine-chart equality to global equality. The existing category-colimit definition supplies precisely the final universal property; its indexing category is the finite span, so there is no smallness gap. It does not substitute an abstract colimit-existence lemma for the actual construction.

I verified every citation.json quote is a literal substring of the statement of the node cited, using the current repository for reused nodes and the sandbox for the new one. The proof_deps are exactly the union of step uses. The new node has only its own statement, introduces all rings and maps, defines P explicitly, records actual searches, and has blueprint references. No new lemma merely restates the item or an existing stronger node. No step is over 2000 characters; the affine equality argument and finite-product localization calculation are elementary consequences of stated injections and fraction definitions.

Small cases checked mathematically: if alpha is an isomorphism then P is T and the pushout is W; if beta is the identity then P is A and it is Y. If D is the zero ring then P=A times T and its spectrum is the disjoint union, as the topological statement requires. If A is zero, surjectivity forces D zero and P=T; if T is zero, a unital beta forces D zero and P=A. If both A and T are zero, Q is empty and the empty open-cover gluing property gives the unique map. Inverting a nilpotent p gives zero rings throughout the matching identity. No division by a nonzerodivisor, finite generation, finite map or Noetherian hypothesis occurs. The proof also treats a non-affine or non-separated target through common small affine target neighbourhoods, not a global-affine assumption.

## Unfinished work

None in the one-level split. The new 0B7J topology statement is intentionally unsplit and ready for its own future item. Full delivery dry-run and push results follow from deliver.py; this report does not assert a successful push before that command completes.
