# Stage-1 delivery: lem-coef-enriched-mapping-cylinder-localization

## Files written

- `dag/nodes/sec-six-functors/lem-coef-enriched-mapping-cylinder-localization.json`: item, statement unchanged, five proof steps, status split.
- `dag/nodes/sec-six-functors/lem-coef-simplicial-natural-equivalence-homotopy.json`: new statement-only lemma; no Mathlib match. This is the general homotopy consequence of an enriched natural transformation invertible on path components, not a mapping-cylinder localization theorem.
- `citations.json`: verbatim statement excerpts for every step/node citation.
- `report.md`: this report. `write_split.py` is sandbox-only scratch; `searches.jsonl` retains the actual search-command log, including the search inherited from the interrupted attempt.

## Attachments

None. Searches of WeilConjectures/ in the read-only slopmaster2 source for the blueprint tag, mapping cylinder, Dwyer, Bergner, and enriched/simplicial natural transformations gave no exact project declaration. Upstream master sorry declarations were not treated as finished proofs. The imported item has no usable closed Lean audit.

## WANTED

WANTED: Lurie, Higher Topos Theory, Appendix A.3.5, especially Notation A.3.5.1, Proposition A.3.5.5, Lemma A.3.5.6 and Lemma A.3.5.14, for this item and the new natural-equivalence lemma. The PDF is not archived in literature/. I read printed pp.891–895 (PDF pages 909–913) by streaming the IAS mirror through pdftotext without writing a source copy. The Harvard host returned HTTP 403 and the web provider returned HTTP 429. The proof is marked agent-written because the reference is online only and its homotopy step is expanded differently from the printed model-target argument. No SGA reference is used. There is no Stacks tag for the simplicial-category result; it would be incorrect to substitute an ordinary-category Stacks localization lemma.

## What was wrong or missing

The imported item was statement-only, with no proof. Its statement faithfully matches HTT A.3.5.6 in simplicial enrichment, with the strict attachment and its specified collapse made explicit by the existing attachment node. No statement dispute, no change of hypotheses and no weakening are needed. All original statement, source, creation, unit and ancestry metadata are retained. The chapter/unit route is unchanged: this is a technical input below prop-coef-integral-exceptional-adjoint, proof paragraph 2 and its displayed derived coefficient-adjunction/inverse-limit calculation, not a replacement of the biduality unit's geometric route.

The printed proof moves to model-category targets and invokes A.3.4.12 to turn a pointwise weak-equivalence transformation into equality of homotopy classes. Directly citing the existing diagram-equivalence-classes node here would be invalid for an arbitrary target E: its target must be the bifibrant part of a combinatorial model category. Also its dependency closure returns through coherent-nerve-comparison to this item. I instead state a general natural-equivalence lemma, with an independent route through the already reviewed product-localization node. Neither this new statement nor its indicated proof needs coherent-nerve-comparison or the item.

## Mathematical argument for the new unsplit lemma

This paragraph explains the intended next split; the node itself has no proof or proof dependencies. A strictly enriched natural family eta:F=>G defines H:[1] times A -> B: use F and G on the two copies of A, and send a cross simplex u:a->a' to G(u) eta_a = eta_a' F(u). Naturality is precisely what makes all mixed compositions agree. H sends the vertical arrows (0,a)->(1,a) to eta_a, hence inverts them in pi_0. The homotopy localization universal property extends [H] over L_vertical([1] times A). By lem-coef-simplicial-inversion-product-parameter this localization is J times A, using J as a representative for the localization of [1] at its arrow. That representative is legitimate because Gamma([1],{arrow})=K and K->J is the specified DK equivalence of the attachment node. The projection J times A -> A is DK: every mapping map is literally A(a,a')->A(a,a'), and every object a has two isomorphic lifts. The two endpoint inclusions therefore have the same class, both inverse to that projection. Precomposing the extension of [H] with them gives [F]=[G]. This proof uses only the existing universal-property, strict-attachment and product-parameter statements and the definition of DK equivalence. None depends on this item (dependency closures checked: 211, 212 and 229 nodes respectively, no occurrence of the item).

Small tests: for A empty the two maps are the unique strict functor; for A a point this says isomorphic objects in pi_0B give the same map-class, as the interval construction predicts. For B an ordinary category with discrete mapping sets it reduces to natural isomorphism. A noninvertible arrow in the walking-arrow category does not meet the hypothesis, so the lemma does not equate arbitrary objects. Non-Kan mapping sets cause no issue: the localization and product-parameter theorems expressly impose no fibrancy condition. Naturality is an equality of simplicial maps, stronger than mere naturality on pi_0; no inference from the latter is claimed.

## Mathlib and duplicate searches

I retained the item's earlier searches and appended actual current exact-topic searches. For the new node I reused the inherited logged LeanFinder query, then ran LeanSearch with a second formulation, Loogle for EnrichedFunctor and grep in CategoryTheory/Enriched. I read Enriched/Basic.lean:455–484 (EnrichedNatTrans and isoMk), and SimplicialSet/HomotopyCat.lean:395–426 (mkNatTrans and mkNatIso). These give ordinary transformations/isomorphisms, not homotopy classes of simplicial functors at DK equivalences. The exact-item LeanSearch/Loogle hits are ordinary localizations; Predicate.lean was inspected, and such a result does not prove equivalences on mapping simplicial sets. Exploratory saturation searches are retained in searches.jsonl but are not represented as searches for the new lemma: the item's final step uses the existing model-target-test node's explicit last clause instead.

I searched the entire DAG statements for enriched/simplicial natural transformations, homotopy-category equality, A.3.4.10 and A.3.5.6, as well as the source Lean tree. blueprint_refs.py search for 'mapping cylinder', 'natural transformation', 'natural equivalence', and 'A.3.4.10' found no blueprint statement of the new result. I read the closest statements: simplicial-diagram-equivalence-classes, simplicial-fully-faithful-homotopy-image, simplicial-derived-exponential and simplicial-inversion-product-parameter. None states the new lemma.

## Not duplicates

lem-coef-simplicial-natural-equivalence-homotopy vs lem-coef-enriched-mapping-cylinder-localization: the new lemma compares two arbitrary enriched functors from a natural family with invertible components; the item constructs and identifies the strict localization of a particular collage, including its collapse map.
lem-coef-simplicial-natural-equivalence-homotopy vs lem-coef-simplicial-diagram-equivalence-classes: that node classifies diagrams into bifibrant model-category targets, and its restricted clause additionally assumes a cofibrant index/chunk; the new lemma allows any simplicial target and any simplicial source, with no object-class classification claim.
lem-coef-simplicial-natural-equivalence-homotopy vs lem-coef-simplicial-inversion-product-parameter: that node identifies localization of a product, without asserting equality of functor classes from an enriched natural family; it supplies a genuine tool for a future proof of the new statement.
lem-coef-simplicial-natural-equivalence-homotopy vs lem-coef-simplicial-derived-exponential: the exponential has bifibrant combinatorial-model targets and a mapping-class adjunction, whereas the new lemma concerns a given natural family into an arbitrary simplicial category.
lem-coef-simplicial-natural-equivalence-homotopy vs lem-coef-simplicial-fully-faithful-homotopy-image: that node tests postcomposition by a mappingwise weak equivalence and its essential image; it does not compare functors linked by a natural family.

## Review by N1

I read the item against HTT A.3.5.6 in full, including its definition of the collage, both conditions on W and the proof's bridge transformation. I read Notation A.3.5.1, Remark A.3.5.2 and Proposition A.3.5.5 on the same online pages. For the new lemma the literal source is the bridge-transformation step on p.894; the stronger abstract formulation and its independent product-localization argument are mine. I checked the full statement of the existing product-parameter node for that route and do not claim that A.3.4.10 literally states it.

Step 1 uses only the item's definitions. I checked naturality in every degree on C-to-C, D-to-D, C-to-D and empty D-to-C mapping sets. In particular the cross-arrow equation has the correct direction: alpha:1_M=>ij. No fully-faithful hypothesis on f is used.

Step 2 uses the strict attachment node's under-M identification and explicit identity-collapse extension. Its condition is satisfied because every j(v) is an identity, even for extra internal arrows and repeated labels. The universal-property node's image clause, applied to the identity of E, proves that pi_0(q) inverts V; its statement really includes this image clause, not just injectivity. Thus every component q(alpha) is invertible, and the target and source need not be locally Kan.

Step 3 uses exactly the new statement with A=M, B=E, F=q, G=qij. The naturality equations come from Step 1 by enriched postcomposition, and the invertibility hypothesis is Step 2. This is the only new non-elementary input. It is strictly smaller than the item: it says nothing about a collage, a labelled localization or a collapse map.

Step 4 uses the universal-property node's injectivity with target T=E and the attachment node's under-M identification, not an unproved full enriched functor-category universal property. I checked both equations: bar-j s=1_D strictly and (s bar-j)q=qij. The injectivity assertion therefore gives the other inverse in h sCat. This handles the specified extension, with no need to identify arbitrary choices of extensions strictly.

Step 5 uses the explicit final clause of simplicial-model-target-test, which states that an actual functor representing an isomorphism is DK without cofibrancy/Kan conditions. Although only that clause is used, I also verified the essentially-surjective hypothesis in its first paragraph using the strict section s. Thus no model-category saturation theorem is silently assumed. All cited nodes lie in the inherited unit; no off-route tool use or SGA route is present. Reading their full dependency closures found no return to the item.

For the item I tested C empty with nonempty D and arbitrary labels that collapse to identities; the proof still uses localization injectivity and does not assume E=D strictly. If D is empty the existence of f forces C empty, and V is empty. For f the identity of a nonempty one-object category the bridge still lies between disjoint copies of its object; it is not mistakenly an identity in M. Nonfaithful f and parallel arrows cause no failure because the naturality calculation uses f(a), not injectivity. Multiple labels for the same arrow and additional kernel arrows are harmless because q inverts all labels. Each new statement introduces all its objects and definitions through its statement dependency, is statement-only, and has the three search kinds with a second phrasing. No proof step exceeds 2000 characters. I did not package an elementary naturality or inverse-cancellation calculation as a new node; I did extract the genuine homotopy lemma rather than hide it inline. This checks delivery-errors B–E, especially C1/C4 and D1/D2.

## Unfinished work

No mathematical issue remains in the one-level split. The new lemma is intentionally unsplit as required. Final acceptance depends on the required server dry run and direct delivery; their results are reported by deliver.py.
