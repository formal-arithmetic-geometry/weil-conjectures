Files written:

- `dag/nodes/sec-deligne-laumon-a1/lem-per-finite-flat-cd-etale-exchange.json` — statement item, split into seven proof steps.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-ordinary-henselian-pointed-neighbourhood-limit.json` — new statement node, unsplit, Mathlib searches found no match.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-completely-decomposed-etale-finite-subcover.json` — new statement node, unsplit, Mathlib searches found no match.
- `citations.json` — verbatim citations for every cited node in every proof step.

Attachments:

- None. No sorry-free declaration in the slopmaster2 source states this item or either new node exactly.

WANTED:

- None. The ILO PDF and the cited Stacks source are present in `literature/`.

What was wrong or incomplete in the imported item:

- The imported item had no proof steps. I retained its statement and source, and expanded the ILO II 3.2.3 exchange sketch into the henselian-local component, section lifting, finite-stage descent, constant-rank descent, and finite-subcover arguments.
- The source says only “by passage to the limit” and “the restriction ... has a section”; the report’s proof makes those operations explicit using existing henselization, finite-algebra, filtered-colimit, morphism-descent, and finite-locally-free descent nodes.
- No statement was changed, and no source-error or statement-dispute was found.

What could not be finished:

- The two new infrastructure nodes remain unsplit as required for a one-level stage-1 delivery. They have complete statements, sources, blueprint provenance, and recorded Mathlib searches.

## Not duplicates

lem-per-ordinary-henselian-pointed-neighbourhood-limit vs def-weil-pbc-henselization-at-prime: the existing node only defines the universal property of a henselization; the new node asserts existence of a directed affine pointed-etale presentation, its inverse limit, and its residue-field identifications.

lem-per-ordinary-henselian-pointed-neighbourhood-limit vs lem-trf-artin-join-theorem-6-3: the existing node concerns component rings of tensor products of two integral henselian algebras; it does not construct henselizations from pointed etale neighbourhoods.

lem-per-ordinary-henselian-pointed-neighbourhood-limit vs lem-trf-henselization-prime-ind-etale: the existing node assumes a henselization and asserts only that A to H is ind-etale; it supplies neither a residue-preserving point at each finite stage nor the asserted pointed inverse limit.

lem-per-ordinary-henselian-pointed-neighbourhood-limit vs lem-trf-ind-etale-local-henselian-integral: the existing node starts with a henselian ind-etale algebra and proves integrality over a henselization; it does not provide the new node’s directed system or existence result.

lem-per-ordinary-henselian-pointed-neighbourhood-limit vs lem-weil-pbc-etale-triples-colimit-localization: the existing statement is only “Localization properties of the etale residue colimit.” It states no existence theorem for ordinary henselization or pointed affine limit.

lem-per-ordinary-henselian-pointed-neighbourhood-limit vs lem-weil-pbc-etale-prime-generates-maximal: the existing node identifies an extended ideal in a localization of one etale algebra; the new node constructs a henselian colimit of a whole pointed system.

lem-per-ordinary-henselian-pointed-neighbourhood-limit vs lem-weil-pbc-etale-triple-ideal-refinement: the existing node refines a single residue triple to send one element into the extended prime ideal; the new node constructs an ordinary henselian local limit.

lem-per-ordinary-henselian-pointed-neighbourhood-limit vs lem-weil-pbc-etale-triples-colimit-representative: the existing node represents an element of an already-given colimit at a stage; it does not state the local henselian limit or unchanged-residue-field property.

lem-per-ordinary-henselian-pointed-neighbourhood-limit vs lem-weil-pbc-standard-etale-monic-derivative: the existing node gives the standard-etale algebra for a monic polynomial and its root-mapping property; the new node is a henselization existence and pointed-limit statement.

lem-per-ordinary-henselian-pointed-neighbourhood-limit vs lem-weil-pbc-strict-henselization-triples: the existing node uses a separable closure K of the residue field and produces a strict henselization with residue field K; the new node uses ordinary henselization and stages whose residue field is exactly kappa(x). A separable closure need not equal kappa(x).

lem-per-ordinary-henselian-pointed-neighbourhood-limit vs lem-weil-pbc-etale-triple-unit-refinement: the existing node makes one element of one residue triple invertible after refinement; it does not construct the ordinary henselian limit with all the asserted properties.

lem-per-ordinary-henselian-pointed-neighbourhood-limit vs lem-weil-pbc-etale-triples-colimit-simple-roots: the existing statement is only “Simple roots lift in the etale residue colimit.” It gives no pointed affine presentation or existence of an ordinary henselization.

lem-per-ordinary-henselian-pointed-neighbourhood-limit vs lem-weil-pbc-etale-triples-filtered-colimit: the existing statement is only “Filtered colimit of etale residue triples.” It states none of the new node’s ordinary henselian, residue-field, or inverse-limit conclusions.

lem-per-ordinary-henselian-pointed-neighbourhood-limit vs lem-weil-pbc-etale-triples-colimit-surjective: the existing statement asserts surjectivity of a residue-colimit map to K; it does not assert the residue-preserving ordinary henselization presentation.

lem-per-ordinary-henselian-pointed-neighbourhood-limit vs lem-weil-pbc-etale-triples-colimit-simple-roots-construction: the existing node lifts one polynomial’s simple root at a stage, under an IsSepClosure hypothesis on K; the new node constructs an ordinary henselian system with residue field kappa(x), which need not be separably closed.

## Review by Q96

I read the item source, Illusie–Laszlo–Orgogozo, Exposé II, Theorem 3.2.3 exchange assertion (printed pp. 30–31), including Corollary 2.2.4 on printed p. 27, and compared every hypothesis with the imported item: Noetherian base, finite locally free positive rank prime to ell, finite separated etale family of finite type, and pointwise residue-field isomorphism. I also read the Stacks algebra.tex proof of Tag 04GN for the ordinary henselization construction and Tag 04GH for finite algebras over henselian local rings.

The first proof step uses `lem-pc-flf-properties` for a free affine algebra chart, the new henselian-neighbourhood node for the filtered pointed system, `lem-weil-pbc-finite-over-henselian-local-product` for the finite henselian factorization, and `lem-weil-pbc-finite-projective-standard-free-cover` for local freeness of each factor; those statements say precisely the facts used. Step 2 is elementary: the nonzero factor ranks sum to d, so one is prime to ell, and the completely decomposed hypothesis supplies a residue-field lift. Step 3 uses the existing etale base-change and henselian etale-retraction statements; the chosen residue point is exactly the retraction hypothesis, and the existing etale composition node covers the open restriction. Step 4 uses filtered-colimit finite-data descent to carry the idempotent to a finite stage, the finite-presentation limit theorem to descend the section as a morphism over Y, and the affine finite-presentation criterion; each cited statement supplies the corresponding operation. Step 5 uses finite-presentation base change and composition, finite-free algebra spectra, and finite-locally-free descent to make the descended map finite locally free of the selected constant rank. Step 6 now cites `lem-weil-pbc-noetherian-open-subscheme-noetherian` and `lem-weil-pbc-qc-open-immersion-finite-type`: on every affine chart P of X, the open P intersect T is quasi-compact, so T to X is quasi-compact and finite type. Etale and finite-type composition use their existing theorem nodes. The separated diagonal is checked over T using that an open inclusion is a monomorphism. Step 7 proves surjectivity from positive-dimensional fibre algebras and applies the new finite completely decomposed subcover node to obtain the required finite family.

I checked small edge cases while reading the statements: the empty base admits the empty family; a positive-rank finite algebra over a field has a maximal ideal and hence a point, including nonreduced algebras; and the selected factor rank is positive because each factor is nonzero. I verified that no step assumes the finite factor or its residue ring is reduced, and that the residue-field condition is used only for the henselian retraction. The required Mathlib searches were run through `msearch.py` and their actual outputs are preserved in `searches.jsonl`; I reread those logged results rather than repeat unchanged queries; all searches found only general etale, henselian, filtered-colimit, or compactness results, with no exact exchange theorem. I also checked the new node source tags against the existing DAG and recorded each differing pair above.

The imported statement and its blueprint provenance are unchanged. The item now has seven explicit proof steps, all dependencies are present, and all citation quotes are copied verbatim from the cited node statements.

Continuation review on 2026-10-19: the pre-existing split first passed `deliver.py --no-push` at b499c2a4ac. I compared its item statement with the current shared node (identical, still unsplit) and retained its proof, citations and search records. Source text for the item was read directly from PDF pages 36–37 (printed 30–31), and for the finite-subcover node from PDF page 33 (printed 27): Corollary 2.2.4 applies also to the completely decomposed case, and Proposition 2.2.3 explains why the rational-lift loci are open in the constructible topology. The ordinary-henselization node was checked against Stacks Tag 04GN, `lemma-henselization`, including its proof by pointed etale pairs; Tag 04GH, `lemma-finite-over-henselian`, confirms that each chosen finite factor remains henselian. The diagram uses ordinary henselization, so the base point retains its original residue field rather than a separable closure.

I repaired citation gaps in the existing proof: Step 1 now cites the finite-locally-free definition for affineness of Y over an affine chart; Step 4 cites the finite-presentation base-change theorem explicitly; Step 6 cites the two existing finiteness tools above instead of its unused finite-subcover citation. I also corrected Step 3’s wording: the map to Y_T factors through the clopen component inclusion and the projection from Y_H, rather than identifying that composite itself with the component inclusion. The henselization statement now labels its colimit notion explicitly. These are citation and exposition repairs, with no change to the item’s mathematical statement.

For B–E, I checked that both new nodes introduce their objects and carry statements only; neither is an elementary restatement or a clause of the item. The ordinary-henselization node is a general construction used before selecting a component; the finite-subcover node extracts a finite subfamily from any completely decomposed etale family. I reread the current statements for all same-tag neighbours and made each nonduplicate explanation specific. Every cited statement was opened and its quoted clause checked against the operation in its step; all citation quotes were regenerated against the current files after the repairs. Affine charts ensure quasi-compactness and quasi-separatedness in both limit applications. The positive factor rank is computed before invoking degree descent; its primeness to ell follows from the sum of ranks, not from any residue-field degree assertion. No step exceeds 2000 characters. The empty-base case, the rank-one case, and nonreduced finite factors require no additional hypotheses. The proof follows the ILO route and uses no SGA source.
