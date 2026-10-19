# Worker report: def-mg-determinantal-weight-multiset

## Files written

- dag/nodes/sec-purity-real-sheaves/def-mg-determinantal-weight-multiset.json — definition, split using four existing statement dependencies; six actual Mathlib searches, no exact match.
- citations.json — empty list because the item is a definition with no proof steps.
- report.md — this report. No new nodes or Mathlib leaves.

## Attachments

None. Searched WeilConjectures/ by the exact blueprint tag and by determinant-weight/weight-multiset names. The closest declaration is Representation.weightMultiset in WeilConjectures/AlgebraicGeometry/LinearAlgebraicGroup/Weights.lean:172–176: it takes a supplied family of subrepresentations and repeats each determinant weight by that family's ranks. The requested definition instead counts each composition factor once and includes composition-series independence. Thus that declaration is not an attachment. The dependency audits already attach semisimplification and its isomorphism-independence to project declarations; they are reused, not re-created. Their historical CompositionSeries.lean path is absent in this local read-only source snapshot, so I do not make a new attachment claim from those records.

## WANTED

None. The exact current blueprint definition and enclosing unit are available locally; this item introduces a definition, not a new theorem requiring a missing source.

## Statement clarified

Read main-20261015/blueprint/sec-purity-real-sheaves/sk-d-real-detweights/def-mg-determinantal-weight-multiset.md (order 2980), its _section.md, the corresponding old master definition, dag/units/sk-d-real-detweights.json, and dag/chapters/sec-purity-real-sheaves.json. Followed the current blueprint_update: the final independence sentence is retained as a property of this definition, with existing dependencies explaining it. Expanded the context-dependent phrase “the preceding normal geometrically connected curve” into the finite field, coefficient prime, embedding, curve, and Weil-representation datum already assumed by the source. Named the existing semisimplification explicitly and rendered the same determinant-weight formula without an embedded hyperref. No mathematical hypothesis or multiplicity convention was changed. The protected source and imported metadata remain as on the base; this paragraph records which newer blueprint text was followed.

## Blueprint and duplicate search

Ran blueprint_refs.py ancestor for the item and search for “determinantal weight multiset”, “determinantal”, and “weight-blocks”; also searched all dag/nodes for determinant/multiset phrases and read def-rp-weight-blocks. Its clause 1 refers back to this item for the constituent-weight multiset; its other clauses define the different rank-counted list and weight blocks, and it assumes a nonzero sheaf. It is not an independent complete replacement for this item (which also admits V = 0). No new node was made. blueprint.same_as is empty; blueprint.from stays null for this imported node. This item supplies the constituent-weight definition of the unit, not the unit's whole key statement, so no unit realization record was edited.

## Review by Q150

I read the current order-2980 definition against the four actual dependency statements, including their blueprint_update fields. def-wf-fundamental-representation supplies the full Weil action, extending the geometric representation with Frobenius descent; it is used only to specify what “Weil representation on X_0” means. Its statement applies to separated finite-type schemes with connected geometric fibre, hence to the normal geometrically connected curve here. No identification with another coefficient category is invoked.

The statement of def-mg-weil-semisimplification gives the direct sum of the simple quotients and expressly identifies its simple-summand multiset with the composition-factor multiset. This supplies both the object and the occurrence convention, rather than just a vague reference to semisimplicity. def-wf-determinantal-weight assigns a/r to an irreducible lisse Weil sheaf of positive rank on a normal geometrically connected curve with the fixed iota; it also uses that notation for the associated representation. Each simple factor is nonzero and irreducible, so this definition is applied only where its rank denominator is positive. The finite coefficient field needed for that definition is part of its own recorded construction; no common additional field is imposed on V.

lem-mg-semisimplification-independent states that the two semisimplifications of a finite-dimensional Weil representation are isomorphic, exactly under the hypothesis used here. The stronger factor-multiset identification required for passing to a multiset is explicitly in def-mg-weil-semisimplification, whose statement cites Jordan–Hölder; I also opened lem-mg-jordan-holder and def-mg-weil-composition-series to verify that this really means permutation, isomorphism and the same multiplicities, not equality merely of total ranks. Isomorphic factors have the same determinant weight: their top exterior powers are isomorphic (apply the exterior power to the isomorphism and its inverse), their ranks agree, and the unique pure weight in the determinant-weight definition is unchanged. This is the direct few-line invariance of the definition, not a new lemma. I checked the determinant-line statement and the nearby source theorem HasDetWeight.of_equiv in RealSheaves/Purity.lean:263–267 as corroboration.

There are no proof steps to audit: this is a definition, so proof and proof_deps are empty and citations.json is correctly empty. All nontrivial inputs to its well-definedness are retained as existing dependencies. No theorem has been hidden in a new definition, no lemma moved into a renamed copy of the item, and no new unsplit statements, tags, or long proof steps have been introduced. The independence sentence is the property already stated in the source, not a new conclusion.

I tested the empty series for V = 0 (empty multiset, with no call to determinant weight on zero); one simple factor S of any positive rank (one entry, not rank(S) entries); S direct-summed with itself (two equal entries); two nonisomorphic simple factors of the same determinant weight (both entries retained); and a nonsplit extension of two simple factors (the same two entries as its semisimplification). Reordering the factors only permutes the list. These cases check the main trap exposed by the Lean candidate: rank-counting would be wrong for this node.

For B–E of delivery-errors: the statement introduces its objects; all specialized notions have explicit existing dependencies; the TeX is rendered once; no new node requires a Stacks source, standalone-statement audit, or duplicate pair. Searches were run through msearch.py and their six exact query texts and results are recorded. The two semantic phrasings returned character theory and finite-group representation facts, not Weil determinant-weight multisets. The broad grep found no determinant-weight names; the second grep searched the existing RepresentationTheory directory for composition-factor/Jordan–Hölder names. Loogle returned no combined hit, and LeanSearch returned generic multiset or modular-form facts. These results support “no match”, not a Mathlib leaf. The route is unchanged: notions come from existing definition nodes, and the independence input is already Lean-closed according to its audit. No SGA source is used. I corrected the imported contextual wording and the implicit semisimplification reference; no source error or disputed statement was found.

## Unfinished work

None for this one-level definition split. The independent maintainer review still assesses the delivered definition and its dependency choices.
