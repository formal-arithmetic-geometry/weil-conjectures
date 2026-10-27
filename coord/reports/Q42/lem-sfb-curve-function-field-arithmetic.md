# Stage-1 report: lem-sfb-curve-function-field-arithmetic

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-curve-function-field-arithmetic.json: statement split in four steps, using existing DAG nodes only; Mathlib searches found ingredients but no exact declaration for the whole item.
- citations.json: a verbatim statement quotation for each node used in each proof step.
- report.md and searches.jsonl: this report and the search command's unmodified log.

New nodes: 0. New Mathlib leaves: 0. The item's statement and statement dependencies are unchanged.

## Attachments

None. Searched lean/WeilConjectures for the item id, functionField with trdeg/FG, and finite-generation/transcendence-degree wording. Curve/Brauer.lean:77–120 proves quasi-algebraic closedness of curve function fields under an algebraically closed base hypothesis, not this item's arbitrary-field, arbitrary-dimension statement. The project function-field module defines the objects and records affine fraction-field facts, not this entire statement. No attachment is claimed.

## WANTED

None. All sources used are available in literature/stacks-project/.

## Corrections and unresolved work

The imported item had an empty proof. Its statement is correct, including without separability; no STATEMENT-DISPUTED correction is needed. Filled its proof, proof dependencies, proof origin, Mathlib search record and split report. The given blueprint ancestry has from.node=null; tools/blueprint_refs.py ancestor reports None as well. Preserved that existing ancestry and its precise from.place rather than inventing a blueprint id. The latest blueprint direct-image proof has a compactification paragraph (3), not an explicit high-genus-cover argument; this item's inherited auxiliary argument is below that paragraph, and the split uses the Stacks places named by the item. No unit or chapter route is changed.

The three human levels in SETUP.md and the current chapter/unit text were read. This is an auxiliary arithmetic task, not the unit's key statement; no unit realization fields are written. No Lean, compiler, Lake, git command, or local DAG/preflight checker was run. Work was written only in the assigned sandbox.

## Searches and reuse

Read the existing item searches, then ran the required msearch.py commands for Q42 and this item. The exact query strings and command-produced results are appended to mathlib_searches and remain in searches.jsonl. Two semantic phrasings cover both scheme function fields and algebraic field extensions; Loogle returned no functionField/trdeg hit. Grep's OrderOfVanishing.lean:108 hit is the unrelated argument name hfg. Read FunctionField.lean:35–55, 148–153; IntermediateField/Adjoin/Algebra.lean:155–188; IntermediateField/Adjoin/Basic.lean:590; AlgebraicIndependent/Transcendental.lean:80–94 and TranscendenceBasis.lean:537–550. They supply ingredients already represented in the DAG. IntermediateField.finite_of_fg_of_isAlgebraic is a search-index name; the current file calls this Algebra.finite_of_essFiniteType_of_isAlgebraic. Both require algebraicity, which the item's step 3 proves.

DAG searches by tags 0BY1, 0B1C, 030H and 09GH and by function-field/fraction-field/transcendence-degree concepts found all the tools needed. Ran blueprint_refs.py search for function field, transcendence, and finite transcendence. No imported blueprint node states this combined arithmetic item. No new node was necessary: field-generation calculations and isomorphism invariance are written out inside steps, not made into nodes. The broader closed-irreducible dimension theorem is reused, not duplicated.

## Not duplicates

No new nodes. Existing lem-sc-closed-irreducible-dimension-trdeg covers arbitrary nonempty irreducible closed subsets and is reused for C=|T|. Existing lem-sc-integral-function-field-affine-fraction covers all integral schemes and is reused directly. Existing lem-kun-transcendence-degree-tower includes the zero-degree algebraicity criterion, so the other tower-law nodes are unnecessary. Existing lem-weil-pbc-algebraic-generators-finite-extension is exactly the finite algebraic generation tool. The item adds the assembly and the explicit generators, not copies of these nodes.

## Review by Q42

I read Stacks curves.tex Tag 0BY1 (theorem-curves-rational-maps), especially the first and third proof paragraphs, varieties.tex Tag 0B1C (item-dimension-irreducible-trdeg and its proof in lemma-dimension-locally-algebraic), morphisms.tex Tag 01RV (lemma-integral-scheme-rational-functions), and fields.tex Tags 030H (lemma-transcendence-degree-tower) and 09GH (lemma-algebraic-finitely-generated). There are no new-node sources to review. No SGA source is used.

Step 1 uses def-weil-finite-type-morphism, whose statement explicitly provides a finite cover by affine spectra of finitely generated algebras over the affine base, and lem-sc-integral-function-field-affine-fraction, whose statement says the generic stalk is a field and every element is a fraction g/h from any nonempty affine open. Nonemptiness of T ensures some chart in the finite-type cover is nonempty. The generators of A generate every numerator and denominator as polynomials, so their germs generate every fraction as a field. The elementary label applies to this explicit two-inclusion calculation from the cited statements; it does not claim the fraction-field theorem is elementary. No separatedness, properness, or dimension-one assumption was introduced.

Step 2 uses the actual statement of lem-sc-closed-irreducible-dimension-trdeg, with X=T, C=all of T, and eta=eta_T. T is finite type over a field as required, and integrality gives the nonempty irreducible whole closed subset. The cited lemma concludes dimension equals transcendence degree of the generic residue field, not of an unnamed function field. I supplied the missing identification: the affine-fraction node makes the generic stalk a field, its maximal ideal is therefore zero, and def-weil-residue-field states that the residue field is its quotient by that maximal ideal. The resulting isomorphism is over k because all maps are the structure map followed by germs and residue. Independence is preserved in both directions under this k-isomorphism by injectivity and polynomial evaluation, exactly using def-kun-transcendence-degree's meaning. Thus this step does not silently substitute a local ring for a residue field.

Step 3 uses def-kun-transcendence-degree for invariance under K -> image(phi), with the polynomial-relation check written out. The image is a subfield containing k since phi is a k-embedding; the ambient field is L. The statement of lem-kun-transcendence-degree-tower supplies both cardinal additivity and algebraicity iff relative transcendence degree zero. In d=d+x, x is bounded by the finite cardinal d, so x is a natural number and ordinary finite cancellation applies. No invalid cancellation of infinite cardinals occurs. All field maps in the tower are inclusions; there are no extra scalar-compatibility assumptions hidden here.

Step 4 uses exactly the algebraic-generator finiteness conclusion of lem-weil-pbc-algebraic-generators-finite-extension. L has a finite list of field generators over k by hypothesis; the inclusions k subset E subset L prove that the same list generates over E. Each generator is algebraic by step 3. This verifies every hypothesis of the cited 09GH node; it does not confuse field generation with finite generation as a ring or algebra.

I checked the B–E failure cases individually against the written files: there are no new-node well-formedness or unsplit-proof issues (B1–B10); every non-elementary fact has a node citation and every quoted statement says what is used (C1–C5); no dependency used is an ancestor of this item, and the only off-unit non-Mathlib tool is the dimension formula declared in split_report.tool_uses (C6–C8). The proof carries explicit generation, image-field and cancellation arguments, not clause-restating nodes (D1–D5). All objects and hypotheses match: finite-type cover, nonempty integral T, generic stalk versus residue field, image E, and finite d (E1–E7). There are no statements about intersections of affine opens, perfection, or separability to justify. Each step is shorter than 2000 characters.

Small cases: T=Spec(k) has K(T)=k, an empty generator list and dimension/trdeg zero; T=Spec(k') for finite k'/k gives the same zero-dimension check with nontrivial finite extension. For affine n-space the coordinate generators give the rational function field. With d=0 the tower forces algebraicity and 09GH gives finiteness, as intended. Identity embeddings give degree one. In characteristic p the embedding k(t)->k(t), t mapped to t^p, has finite purely inseparable degree p and is fully allowed; no step calls it separable. The finiteness of d is essential: the proof only cancels after showing the remaining cardinal is finite. Nothing is left mathematically unfinished.
