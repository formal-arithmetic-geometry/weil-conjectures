# Q65: lem-trf-valuation-arbitrary-height-limit

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-valuation-arbitrary-height-limit.json`: statement, now split into eight proof steps; no Mathlib match for the whole item. The original mathematical statement, creation record, source, ancestry, and inherited searches are retained.
- `citations.json`: eleven entries, one for each citation in the eight steps, with exact excerpts from the cited node statements.
- `report.md`: this report.
- `searches.jsonl`: actual searches recorded by msearch.py. No new DAG nodes and no new Mathlib leaves.

## Attachments

None. I searched `WeilConjectures/` in the read-only slopmaster2 source for the exact item id and for finite-height/finite-rank valuation descent. The hits concern unrelated finite-rank modules, valuations, or p-adic constructions; there is no project declaration stating this item. The master source is reference material only and was not treated as a finished proof.

## WANTED

WANTED: local archival copy of Michael Temkin, *Stable modification of relative curves*, arXiv:0707.3953v3, Section 2.1 pp. 7–8 and Theorem 3.5.5 Step 5 p. 24, for lem-trf-valuation-arbitrary-height-limit. The author-hosted primary PDF https://math.huji.ac.il/~temkin/papers/Stable_Modification.pdf was read online. I did not download it into the shared repository. Its Corollary 2.1.3(ii) gives the finite-height approximation; Step 5 misprints its reference as Lemma 2.1.1(ii).

## What needed work

The imported item had no proof. Temkin's short limit argument does not itself spell out a separably closed coefficient field, the faithful flatness of its valuation inclusion, or the descent of the two properties of the algebra. These are supplied by actual cited statements, rather than left as an invocation of a limit argument. There is no statement dispute or mathematical change.

The historical ancestor is lem-trf-local-term-locality. I read the current main-20261015 ancestor proof and the sk-i-curve-zero unit record: the current local-term argument uses contracting correspondences and no longer contains this older valuation-normalization argument. The item already records this historical supporting ancestry. I retain it and split only its assigned algebraic ingredient; I do not install a replacement unit route or change any unit record.

## Mathlib and reuse searches

The item's inherited searches are retained. I ran two new semantic phrasings of the whole assertion, the Loogle query `"ValuationSubring", "FinitePresentation"`, a grep of `RingTheory/Valuation`, and LeanSearch. Neither the empty Loogle/grep results nor the semantic results give the whole theorem. The useful semantic hit for presentation models gives only coefficient descent and not a finite-height separably closed valued subfield, faithful flatness, or geometric reducedness descent.

I also searched relative separable closure and geometric reducedness under field extension. The former returned `separableClosure.isSepClosure` and related facts, but the DAG already has the Mathlib leaf def-weil-pbc-relative-separable-closure, whose actual statement includes the required separably closed property. The latter returned the algebraic-closure test and injective-subalgebra lemmas; I read the pinned `Mathlib/RingTheory/Nilpotent/GeometricallyReduced.lean` and did not infer an arbitrary-field base-change equivalence from them. Instead I found the existing ring-level node lem-trf-geometrically-reduced-fibre-locus, whose statement explicitly has the base-change equality needed here. No new node is justified by either search.

Whole-DAG searches covered finite height/rank, separable closure, faithful flatness, torsion-free flatness, presentations and geometric reducedness. Whole-blueprint searches used `tools/blueprint_refs.py search` for finite height, separable closure, torsion free, finite presentation, geometrically reduced, and 035X; the ancestor command confirms lem-trf-local-term-locality. No blueprint node states the item in another form, so same_as is empty.

## Not duplicates

No new nodes are created. In particular, there is no new relative-closure lemma, polynomial-presentation descent lemma, or geometric-reducedness field-descent lemma. The existing relative-closure, presentation-base-change, and fibre-locus nodes are cited directly.

## Review by Q65

I read the author-hosted Temkin v3 PDF at Corollary 2.1.3(i)–(ii), its proof, the surrounding valued-field discussion, and Theorem 3.5.5 Step 5. I read every cited DAG statement in full. I also read the local primary Stacks source: fields.tex Tags 09HC (lemma-separable-elements) and 09HB (lemma-separable-permanence); more-algebra.tex Tag 0539 (lemma-valuation-ring-torsion-free-flat); algebra.tex Tag 00HJ (lemma-flatness-descends), Tag 00HR (lemma-local-flat-ff), and the polynomial quotient formula in Section 05G3 immediately after Definition 05G4; more-morphisms.tex Tag 0576 (lemma-base-change-fibres-geometrically-reduced), its proof via Varieties Tag 0384, and Tag 0579 (lemma-geometrically-reduced-constructible). No SGA source is used. There are no new-node sources to review.

Step 1 uses exactly the finite-presentation definition: finitely many variables and relations give finitely many coefficients, hence a finitely generated coefficient subfield F. The valuation alternative restricts to F directly and gives its fraction field. This is elementary finite data, not a new descent lemma.

Step 2 uses three statements. The relative-separable-closure node explicitly says that the closure inside a separably closed ambient field is a subfield, algebraic over F, and separably closed; these are not being inferred from its name. The finite-type-field-height node applies to F, which is finitely generated over its prime field, rather than to K_0. The algebraic-height node then applies to K_0/F and V_0; its restricted valuation is exactly W. Thus I do not apply a finite-generation theorem to the usually infinitely generated separable closure.

Step 3 proves locality explicitly. I checked the nonunits form a proper ideal by the valuation divisibility alternative, and checked the inverse of a nonzero element of V_0 belongs to K_0. Consequently units are reflected by V_0 into V and the maximal ideals contract correctly. This is a direct elementary argument, not an uncited theorem about valuations.

Step 4 verifies torsion-freeness inside the field K, applies the valuation-module flatness node to V_0 and V, then uses the local-flat-faithfully-flat node. Both rings really are local by Step 3. The source has no Noetherian or finite-height hypothesis that was silently added.

Step 5 uses the finite-presentation definition and the exact polynomial-presentation base-change statement. Every relation coefficient lies in V_0. The resulting isomorphism is an isomorphism of V-algebras for the specified inclusion, because it fixes scalars and the original chosen variables.

Step 6 uses the faithfully flat module-descent equivalence with R=V_0, R'=V and M=A_0. The tensor factor flip is written explicitly; it preserves the V-action. Flatness after base change is the given flatness of A, and faithful flatness is already established independently in Step 4. Nothing assumes that A_0 is flat before this application.

Step 7 applies the same polynomial-presentation node three times, to V_0 to K_0, K_0 to K, and V to K. Thus finite presentation of B_0 is proved, and the generic-fibre comparison is the identity on the same K-polynomial quotient. It is not an unspecified transport or an appeal to a definition of a tensor product for a nontrivial theorem.

Step 8 uses only the base-change equality that is literally in lem-trf-geometrically-reduced-fibre-locus. Its finite-presentation hypothesis holds by Step 7. Applying it to the field inclusion K_0 to K identifies membership of the sole prime in each spectrum, so the given geometric reducedness over K implies geometric reducedness over K_0. Constructibility is not used, and the local-ring-only node is not cited as if it stated this global assertion.

I checked B–E of delivery-errors.md against the finished files. No new unsplit statement hides a proof; every non-elementary step cites its actual supporting statements (C1), and the quotations in citations.json are verbatim parts of those statements (C4). There is no repackaging of the item as a new lemma, no use of another node's proof as an interface, and no new node duplicating a special case. The off-unit citations are existing Mathlib leaves; the non-leaf citations are in the same unit. Traversing dependencies of the geometric-fibre-locus, presentation-base-change, and algebraic-height nodes found no path back to the item. All eight proof steps are under 800 characters, so none meets the long-step audit threshold.

For small cases I checked A=0 by taking the relation 1, and a polynomial algebra with no relations by allowing an empty coefficient set. For a trivial valuation V=K, its restriction is V_0=K_0 of height zero and the same descent works. Nothing assumes K is perfect, algebraically closed, finitely generated, or equal to K_0; in positive characteristic the relative separable closure inside K is the construction required. No finiteness of the extension K/K_0 is assumed. These checks required no correction of the statement.

## Unfinished work

None in this one-level split. The reused nodes retain their own current proof/leaf states; no supporting node is silently declared proved by this delivery. Only the local Temkin archive is outstanding as noted above.
