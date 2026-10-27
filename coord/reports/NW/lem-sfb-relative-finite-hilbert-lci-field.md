# Stage-1 report: lem-sfb-relative-finite-hilbert-lci-field

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-relative-finite-hilbert-lci-field.json: split, original statement and statement dependencies retained; five proof steps following Stacks 06DA.
- dag/nodes/sec-six-functors-basics/lem-sfb-cm-closed-fibre-regular-slice.json: statement, unsplit; no Mathlib match for regular slicing (0570).
- dag/nodes/sec-six-functors-basics/lem-sfb-space-lci-composition.json: statement, unsplit; no Mathlib match for arbitrary Koszul-lci composition of space morphisms (06C8) and the etale case.
- citations.json: verbatim statements for every use in every numbered item step.
- searches.jsonl: searches run with the mandated msearch.py, including unsuccessful alternate phrasings. Search results concerning isolated localizations were read, and the candidate Mathlib QuasiFiniteAt and finite-localization declarations inspected, but no node was created for that fact because existing scheme finiteness suffices.

## Attachments

None. Whole-library searches by the blueprint tag, Hilbert/lci terminology, regular immersion and slicing found no project declaration proving this item. Regular-immersion constructions for smooth schemes do not state this arbitrary-space, arbitrary-field assertion.

## WANTED

None. All sources used are available locally in literature/stacks-project. No SGA source is used.

## Corrections and limits

The imported statement is correct and unchanged. The inherited blueprint.from.node is null and blueprint_refs.py ancestor prints None. Its detailed from.place and via chain are preserved, and new nodes prepend the item to that chain. I read the current latest blueprint's sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability-direct-images.proof.md, which supplies the high-level direct-image route; the geometric argument is the inherited supporting prerequisite. No chapter/unit route or unit record is changed.

The old 0570 node deliberately forgets regularity, so its conclusion does not suffice here. It was not cited as if its proof supplied regularity. Finiteness uses the existing 06LH scheme theorem instead of creating an isolated-localization node. The immersion need not be replaced by a reduced residue field: doing so can destroy regularity. All new proof fields and proof dependency lists are empty; splitting them remains future work as prescribed by the one-level brief. No Lean was written and no compilation or local preflight was run.

## Not duplicates

lem-sfb-cm-closed-fibre-regular-slice vs lem-trf-cm-closed-point-flat-quasifinite-slice: the existing statement expressly forgets regularity of the immersion; the new statement retains an immersion with locally regular-sequence ideal, which the lci conclusion requires.

lem-sfb-space-lci-composition vs lem-sfb-space-lci-base-open: the existing 06C9-related result constructs a universal open on the base for a closed flat lfp morphism with lci fibres; it does not give composition of arbitrary lci morphisms or assert that etale maps are lci.

lem-sfb-space-lci-composition vs lem-sfb-space-fibrewise-lci-source-locus: the existing 06C9-related result constructs a base-change-compatible source open for a flat lfp family; the new composition statement has no flatness hypothesis and asserts neither an open locus nor base-change compatibility.

lem-sfb-space-lci-composition vs lem-sfb-syntomic-smooth-composition: that node concerns syntomic ring maps and assumes flatness; it does not imply lci composition for nonflat space morphisms. The existing syntomic result cannot be substituted for the new result.

lem-sfb-cm-closed-fibre-regular-slice vs lem-trf-cm-fibre-hypersurface-dimension-drop: the existing statement performs a single positive-dimensional hypersurface reduction and gives no regularity of the immersion or completed singleton slice; the new statement is the general regular-immersion slice theorem, including dimension zero and the completed induction.

lem-sfb-cm-closed-fibre-regular-slice vs lem-trf-zero-dimensional-closed-fibre-open-slice: the existing statement assumes a zero-dimensional fibre stalk and provides an open neighbourhood; the new statement permits a positive-dimensional Cohen–Macaulay stalk and supplies a regular immersion cutting it down to a singleton.

lem-sfb-space-lci-composition vs lem-sfb-fibred-groupoid-representable-smooth-calculus: the existing result treats smooth and etale representable morphisms and their composition, but contains no lci assertion for arbitrary, possibly nonflat, morphisms.

lem-sfb-space-lci-composition vs lem-sfb-stack-chartwise-smooth-etale-calculus: its list of stable properties omits lci; etale implies smooth is only one input to the etale-lci clause and cannot supply the arbitrary lci-composition clause.

## Review by NW

I read the full statement and proof of criteria.tex Tag 06DA, more-morphisms.tex Tag 0570, spaces-more-morphisms.tex Tags 06C8 and 06C9, the etale-smooth and smooth-syntomic lemmas in spaces-morphisms.tex, and more-morphisms.tex Tag 069L. For the regularity wording I also checked divisors.tex definition-regular-immersion. The new 0570 node retains the actual regular immersion, permits an empty regular sequence and does not assert a globally closed immersion over an arbitrary base. The new 06C8 node uses the inherited chartwise Koszul-lci definition and correctly does not assert arbitrary base-change stability. Both sources were checked against the tag map.

Step 1 uses def-trf-algebraic-space for the etale atlas, local finite presentation and finite-type definitions for the finite-type affine chart, lem-trf-generic-cm-locus-field for a dense open of Cohen–Macaulay local rings, and lem-sc-lft-over-field-jacobson-space for a closed point in that nonempty open. I opened these statements: neither genericity nor closedness is being taken from an unstated clause. Flatness over a field is the direct vector-space tensor argument, interpreted using def-weil-flat-morphism.

Step 2 applies the new regular-slice statement with base Spec k, fibre equal to V, the chosen closed point, global flatness, lfp and its Noetherian Cohen–Macaulay stalk. Its singleton fibre is the entire source because the base is Spec k. This proves that an affine neighbourhood of the only point covers Z; its topology has dimension zero. The finite-type definition identifies quasi-compact lft with finite type.

Step 3 uses exactly the statement of lem-pc-algebraic-dim-zero-affine-finite, with finite type and dimension zero just checked, to obtain finite Z. def-weil-finite-integral-morphism gives the finite module, and def-pc-finite-locally-free says finite plus flat plus lfp and defines the degree. Nonemptiness makes the coordinate algebra nonzero, so its finite dimension is positive. No separability of its residue field and no reduction of Z is assumed.

Step 4 uses the closed-immersion definition (including its factorization description of immersions), the unramified open-diagonal definition, and lem-sfb-space-unramified-permanence. The last node explicitly gives both etale implies unramified and composition, which are precisely its uses. The immersion's unramifiedness is written out from quotient algebras and the isomorphic diagonal rather than incorrectly taken from a definition node as a named theorem.

Step 5 uses the new regular-slice conclusion and lem-weil-pbc-regular-sequence-koszul-regular. I checked that the latter states regular-to-Koszul for arbitrary commutative rings and includes the empty sequence. The open factor is smooth by the explicitly written infinitesimal lifting argument and local finite presentation. The factorization is therefore exactly def-sfb-relative-finite-hilbert-groupoids' lci definition. The new space-lci statement gives both the etale clause and composition. This establishes both required properties for the same Z-to-X map. No statement of a cited node is replaced by material from its proof.

Small cases checked: a zero-dimensional nonreduced finite scheme over k permits the identity slice and the empty regular sequence; X=Spec L for finite purely inseparable L/k permits the identity map to X and degree [L:k], so the slice is not claimed etale over k; an affine line over a finite field has a closed-point slice with finite positive degree; a space with arbitrarily many components needs only one nonempty affine etale chart. A singular non-Cohen–Macaulay point is avoided by the dense open instead of incorrectly being sliced as if Cohen–Macaulay. Empty X is excluded by the item, and empty regular sequences are included by both new statements. The two new nodes have their own objects, hypotheses, definitions and sources, have no proof sketches in their statements, and are neither clauses of the item nor elementary consequences of the cited definitions. Every proof step is below 2000 characters; no hidden long comparison remains. The four off-unit uses are declared as generic tools in split_report, not as changes to the unit route.

During the dry-run refresh, the live Hilbert-groupoid definition was expanded by its own reviewer to make its existential chart test explicit. I reread the updated definition: the local Koszul factorization used in Step 5 is unchanged. The corresponding quotation now isolates exactly that factorization sentence, rather than copying unrelated groupoid data.
