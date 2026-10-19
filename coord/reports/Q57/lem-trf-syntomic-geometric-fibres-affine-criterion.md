## Files written

- dag/nodes/sec-trace-formula/lem-trf-syntomic-geometric-fibres-affine-criterion.json: statement, split into six steps; no Mathlib match for the full criterion.
- dag/nodes/sec-trace-formula/lem-trf-lci-affine-open-locality.json: new statement-only lemma, unsplit; no Mathlib match. An affine cover by local-complete-intersection field algebras implies that every affine open has such a coordinate algebra.
- citations.json: one literal statement quote for each dependency of each proof step. searches.jsonl retains the actual search results logged by msearch.py.

## Attachments

None. Searched WeilConjectures/ in the read-only slopmaster2 source by the item tag, syntomic/Syntomic, complete.intersection and local complete intersection; no declaration states the item or the new lemma. Also searched the read-only upstream master by item/syntomic. Master is reference material only. The item has no existing lean_audit frontier requiring additional nodes.

## WANTED

None. All sources used are available in literature/stacks-project/.

## Corrections and scope

No statement correction or STATEMENT-DISPUTED finding. The original three conditions and all statement dependencies are retained. The item had an empty proof. Its syntomic comparison has been expanded into actual chart and field-extension arguments, rather than introducing a node restating a clause of the criterion. There is one substantive new locality lemma, for schemes over a fixed field, not for families over an arbitrary base.

Read the chapter sec-trace-formula and unit sk-i-curve-zero and the current main-20261015 blueprint. The ancestor's present curve-local-term route is the contracting-correspondence route. This item's recorded historical nodal-chart ancestry is preserved, as are its unit and chapter. The split gives the generic algebraic-geometric tool already requested by that ancestry; it does not alter the unit or use SGA.

The existing lem-weil-pbc-lci-field-change is used as a generic off-unit tool: it compares finite-type algebras under an arbitrary field extension, exactly the ordinary/geometric fibre comparison needed here. It is declared in split_report.tool_uses. The other proof results reused from other units are already Mathlib leaves.

## Searches and reuse

Searched all DAG node statements, the Stacks tags 01UD/01UC/01UE/01UF/00SJ/00SL and then 01UG/00SH, and the local-complete-intersection keywords. Ran blueprint_refs.py ancestor on the item and searches for syntomic, complete intersection, local complete, 01UG and 00SH. These found no blueprint node stating either this criterion or the new affine-open locality lemma. A text search across main-20261015 finds the existing complete-intersection algebra definition, which is reused. The supporting flatness, finite-presentation, tensor-spectrum and field-change nodes were opened and their statements read before use.

New searches used msearch.py only: LeanFinder, LeanSearch, Loogle and source grep, with different natural-language phrasings for the criterion and the new lemma. The successful services returned flat_iff, locallyOfFinitePresentation_iff, LocallyOfFiniteType results, smoothness, Noetherian affine locality and the generic of_affine_open_cover theorem. The generic theorem still needs localization and gluing hypotheses for the complete-intersection predicate, so is not a one-line match. Full-source grep found only the comment at Mathlib/RingTheory/Extension/Presentation/Basic.lean:103 about when a presentation's dimension makes sense. I read the comment and surrounding declaration; it supplies no complete-intersection predicate or theorem. No hit states the new lemma or the full item. Actual queries and their logged results are preserved in the node records; pre-existing item searches are retained.

## Not duplicates

No existing DAG node carries the new lemma's source Tags 01UG or 00SH. The whole-DAG and whole-blueprint concept searches found no equivalent statement.

lem-trf-lci-affine-open-locality vs lem-trf-syntomic-geometric-fibres-affine-criterion: the new lemma concerns invariance of the coordinate-algebra complete-intersection condition under arbitrary affine opens of a scheme over one field; the item concerns arbitrary-base families, flatness, finite presentation, and comparison with all geometric fibres. The new lemma supplies only the affine-open inheritance needed in step 3.

lem-trf-lci-affine-open-locality vs lem-weil-pbc-lci-field-change: the existing lemma changes the field for one fixed finite-type algebra; it says nothing about affine opens or coordinate-ring gluing. It is reused separately for field extensions.

lem-trf-lci-affine-open-locality vs def-weil-pbc-complete-intersection-over-field: the definition describes principal-open global-complete-intersection covers inside one algebra; it does not assert invariance under arbitrary affine open covers of a scheme. The definition is reused as a statement dependency.

## What remains

The item is split by one level. The new locality lemma is intentionally unsplit and has no proof or proof dependencies; its later proof can use the intrinsic local-ring criterion of 01UG together with 00SH. No Lean writing, compiler invocation or Lake command was used.

## Review by Q57

I read Morphisms definition-syntomic (01UC), lemma-syntomic-characterize (01UD), lemma-local-complete-intersection (01UG), lemma-syntomic-locally-standard-syntomic (01UE), lemma-syntomic-flat-fibres (01UF), and Algebra definition-lci (00SL) and lemma-lci-field-change (00SJ). For the new lemma I also read Algebra lemma-lci-global (00SH) and lemma-lci-at-prime (00SG). In 01UG the hypothesis is a scheme locally of finite type over a field; the new node's cover by finitely generated field algebras ensures that hypothesis. The intrinsic complete-intersection condition on local rings is unchanged on open subschemes, and 00SH converts that condition on an affine open to its algebra being a local complete intersection. Finite generation on every affine open is the usual affine characterization of locally finite type, read in Morphisms lemma-locally-finite-type-characterize (01T2). These facts justify the new statement without assuming that arbitrary intersections of affines are affine.

Step 1 uses lem-weil-pbc-open-preimage-fibre-product precisely for the inverse image open as a pullback; def-pc-fibre-product supplies the universal property and uniqueness; lem-weil-pbc-fibre-product-affine-spectra gives the spectrum of B tensor_A k, including its projections. The regrouping of these pullbacks is explained through maps into a test scheme, and covering is just inverse image of a union. No flatness or finiteness is used.

Step 2 uses lem-weil-pbc-flat-morphism-affine-criterion for all affine pairs, and lem-weil-pbc-lfp-affine-opens-finite-presentation for finite presentation on every such pair. These are exactly their statements, not merely consequences hidden in their proofs. The base-change clause (1) of lem-weil-pbc-finite-presentation-base-change-composition applies to the residue field without any finiteness hypothesis on the base ring. The passage from a finite presentation to finitely many generators is immediate from def-weil-pbc-finitely-presented-algebra. This explicitly verifies the finite-type hypothesis needed in the next step.

Step 3 uses the existence sentence in def-weil-algebraic-closure and the point-plus-residue-field-map description in def-weil-geometric-point. The new affine-open lemma applies to the geometric fibre because (1) supplies its cover, and step 1 supplies the relevant affine open. The displayed balanced-tensor maps identify its ring with S tensor Omega. The existing lem-weil-pbc-lci-field-change states the equivalence for every field extension, so its reverse implication applies to the algebraic closure here, using the finite-type conclusion of step 2. This is genuine descent; no inference from geometric fibres to ordinary fibres was left uncited.

Step 4 uses only the local affine neighbourhood property of def-pc-scheme and the universal quantification in (2). Inverse images of opens are open, so its source charts are affine opens of X, as required in (2). This is an elementary choice of covers, not a separate lemma.

Step 5 uses lem-weil-pbc-flat-ring-map-iff-flat-affine for exactly the chart morphisms Spec B_ab to Spec A_a. The stalk maps of the restrictions coincide with the original stalk maps because the opens contain the points. The pointwise flatness definition in def-weil-flat-morphism and the existential affine-pair definition in def-sbc-locally-finite-presentation then give the two assertions globally. This is a few-line argument from cited statements and definitions, so is marked elementary; I did not cite an all-affine-pairs result as if it already asserted a one-cover criterion.

Step 6 uses def-weil-geometric-point to obtain the possibly transcendental field extension kappa(y) to Omega. The local-complete-intersection algebra definition ensures that S_b is finitely generated, so the forward implication of lem-weil-pbc-lci-field-change applies. The tensor identification is the same explicit pair of inverse maps written in step 3. The source-chart covers pull back to an affine cover of the geometric fibre by step 1. The definition in the item now gives the fibre condition, and def-weil-finite-type-morphism identifies the finite-generation cover with local finite type. No extra surjectivity or nonemptiness assumption is imposed.

I tested the new statement on Z empty and on the zero coordinate algebra: the empty affine open has ring zero, explicitly allowed by the reused complete-intersection definition. For the item, X empty gives vacuous source-cover and fibre conditions and pointwise flatness/finite presentation; Y empty forces X empty. Empty individual fibres are likewise retained. Nonreduced complete intersections such as k[t]/(t^2) remain allowed; neither reducedness nor smoothness is introduced. Arbitrary fields, including imperfect fields, are allowed by 00SJ. Neither a Noetherian base, quasi-compact source, nor a separation hypothesis occurs in the proof. Every proof step is below 2000 characters, and no standard comparison lemma is hidden in a long step. The statement, blueprint metadata and source-route fields were not weakened. The main correction during self-review was to make the new node's source point directly to intrinsic local-ring locality (01UG/00SH), and to keep its future proof discussion in this report rather than in the unsplit node.
