# Q25 stage-1 delivery: lem-trf-derived-shriek-comma-homology

## 1. Files written

- `dag/nodes/sec-trace-formula/lem-trf-derived-shriek-comma-homology.json`: existing statement node, now split into 14 proof steps. The statement, its six statement dependencies, its source and its inherited blueprint ancestry are unchanged. Five actual searches made on 2026-10-22 are appended to the inherited Mathlib searches. No exact Mathlib match.
- New nodes: none. New Mathlib leaves: none.
- `citations.json`: 13 verbatim statement quotations covering every step-node citation.
- `searches.jsonl`: actual msearch log, retained in the sandbox. `prepare.py` is the sandbox-only preparation script, not a delivered project file.
- `report.md`: this report and signed review.

## 2. Attachments

None. Searched `lean/WeilConjectures/` for the blueprint tag, derived Kan/comma homology terminology, and ordinary left Kan declarations. Ordinary Kan-extension declarations in the open/pro-etale files and general derived functors do not state this result. The project's derived-homology coproduct and continuity declarations also do not compute this left Kan extension. No exact project declaration was found.

## 3. Wanted literature

None. All documents used were available in the read clone.

## 4. Findings and changes

The item had no proof steps. Its statement is well typed and agrees with the comma convention of Stacks 08PK: the index is the opposite of the category of maps **from** V **to** uU. No statement dispute or correction was needed. The degreewise equalities in the imported prose are canonical cohomology identifications induced by an isomorphism in D(R); the proof first gives that derived isomorphism, not just cohomology isomorphisms.

I read Stacks `sites-cohomology.tex`, Examples 08PG (`example-left-derived-colimits`) and 08PH (`example-morphism-categories`), and the full statement and proof of Lemma 08PK (`lemma-compute-left-derived-g-shriek`). The latter uses a fibred-category factorization and states the abelian-sheaf computation. This delivery instead writes out the coefficient-module bar-resolution computation underlying 08PG and 08PH, with the same comma category as 08PK. Its `proof_origin.by` is therefore honestly `agent`; it does not attribute this particular expanded proof to the printed proof of 08PK. The universal bounded-above acyclic computation and canonical derived adjunction are cited as existing statements.

The existing bar node's proof suggested the explicit resolution, but no step cites or depends on that proof. Its construction and contraction are given again as elementary computations inside this item's proof; the only facts taken from that node are its stated bar terms and signs. The non-elementary acyclic-resolution theorem is cited directly. This avoids creating another node for a clause of the item or for a routine copower calculation.

The chapter and unit records were read. This is not the key statement of `sk-i-curve-zero`, so no unit realization fields are changed. I also read the current `main-20261015` proof of `lem-trf-local-term-locality`. The inherited lower-shriek/cotangent ancestry is retained. All non-definition proof tools belong to the same unit. No chapter or unit route is replaced, and no SGA source is used.

## 5. Unfinished work

None for this stage-1 item. No Lean was written and no compiler, Lake command, or library build was run. Repository and launcher files were read only. The required dry run and direct push are the remaining delivery operations.

## Not duplicates

No new nodes are proposed, so there are no new/existing node pairs. Whole-DAG searches for 08PK/08PG/08PH, bar resolutions, projective presheaves, representable acyclicity, and pointwise Kan extension located the existing bar, derived-shriek, and bounded-above computation nodes. Whole-blueprint searches using `tools/blueprint_refs.py search` for `Kan extension`, `comma`, and `derived colimit` found no equivalent blueprint statement. In particular `lem-sfb-pointwise-kan-colimit` is an ordinary Kan formula only; it is not being recreated or used as a substitute for a derived formula.

## Mathlib search review

All five new queries were run through the prescribed `msearch.py`, and their actual outputs were read. The log contains one grep, one Loogle search, one LeanSearch search, and two distinct LeanFinder phrasings. All services answered. The inherited searches were retained as historical records, not presented as new searches made by Q25.

LeanSearch returned ordinary `Functor.leftKanExtensionObjIsoColimit`, `lanEvaluationIsoColim`, pointwise Kan formulas and a structured-arrow functor. I read `Functor/KanExtension/Adjunction.lean`, including the ordinary pointwise isomorphism. The grep hits and `Functor/Derived/PointwiseLeftDerived.lean` concern expressing a derived functor as a right Kan extension along localization; they do not compute the left derived functor of the presheaf left Kan operation. I read that file's definitions and `Functor/Derived/LeftDerived.lean`. The first LeanFinder returned module derivations, Ext and local-cohomology diagrams. The second returned `Rep.barResolution`, representation Tor, and a generic left-resolution functor. I read the representation resolution file: it resolves the trivial representation of a group, not an arbitrary coefficient diagram on a small category or its comma Kan evaluation. No hit states the item or yields it in one specialization.

## Review by Q25

I reviewed the complete source statements and proofs of Stacks 08PG, 08PH and 08PK against the item, and read derived.tex at 0646 (`lemma-projective-resolutions-exist`), 06XN (`lemma-find-existence-computes`) and 015E (`lemma-leray-acyclicity`) for the existing acyclic-computation input. There are no new nodes with separate sources to check. The proof is an explicit module-coefficient expansion, and its agent origin is recorded rather than disguising the difference from 08PK's printed factorization argument.

For step 1 I opened all four cited nodes. The sites definition gives the singleton-isomorphism sheaf condition; the module-category statement gives sectionwise kernels and sheafified cokernels, which are sectionwise here because every presheaf is a sheaf. The size convention supplies the common universe. The continuous/cocontinuous derived-shriek statement supplies definedness everywhere, the comparison, and its canonical adjunction under exactly the two continuity hypotheses checked in the step. No finite-limit preservation of arbitrary diagrams by u is assumed: only pullbacks of isomorphism coverings occur.

Steps 2 and 4 use no uncited categorical theorem: the coefficient copower adjunction is proved by the identity summand, and its left Kan image by two explicit Hom bijections with the same inverses. Preservation of sums and cokernels is a universal-property argument from the given ordinary adjunction. In step 3, the cited module-category statement provides objectwise epimorphisms. Free module lifting, copower lifting, the explicit representable-sum epimorphism, and exactness of sums are all proved in the text; in particular, I did not assume that an arbitrary coefficient module is projective. These are short elementary arguments, not proposed nodes.

For step 5 I opened the bounded-above acyclic-computation node. It really states existence of projective resolutions with the same upper bound, invertibility of the comparison on bounded-above projectives, and the acyclic-resolution comparison used here. The source category has enough projectives by step 3; applying g_! to the displayed projective resolution is exact because each target copower functor and direct sum is exact, not because a left adjoint is exact. The naturality equation then proves the required acyclicity. This is the essential coefficient check: nonflat modules are permitted. For step 8 the same cited statement explicitly gives invertibility on bounded-above complexes of acyclic objects and naturality for maps of augmented resolutions. Every hypothesis is accounted for by steps 1, 3, 4, 5 and 7.

Steps 6 and 7 give the entire bar resolution and the evaluated contraction; the cited module-category statement in step 7 is used only to pass from objectwise cohomology to presheaf cohomology. I checked the augmented n=0 identity separately: ds_0 plus s_{-1} alpha is the identity and alpha s_{-1} is the identity. The homotopy is not claimed to be natural in the evaluation object. The cancellation in arbitrary degree follows by pairing each later deletion with the corresponding old deletion, with opposite signs.

For steps 9 and 10 I opened the derived-colimit-bar node and copied its actual term/sign formulas into the citation evidence. A comma chain is uniquely determined by the chain in E and the single map V to uU_n, because all later a_j are forced by composition. The first face composes that initial arrow, the middle faces compose arrows in E, and the last face applies precisely F(h_1). The two possible comma directions therefore cannot be confused. Step 10 also cites the derived-category definition for localization, not for a separate unproved evaluation theorem: exact evaluation preserves kernels, images and cohomology objectwise, so it preserves quasi-isomorphisms and descends by that universal property. Step 12 uses the cohomology functors explicitly stated in that same definition node. These citations say exactly what the steps take from them.

Step 11 computes all restrictions and coefficient maps on generators, including the coefficient face. Steps 13 and 14 distinguish the ordinary chain augmentation from the canonical derived counit and then identify them. I reread the full normalization clause of the continuous/cocontinuous-derived-shriek node: it sends Q(c) composed with the comparison to Q(alpha). Derived adjunction sends the counit precomposed with Lg_!Q(alpha) to the same map, so injectivity gives the claimed equality with the correct direction of the comparison i_F. Naturality in both V and the coefficient presheaf follows from the actual displayed generator maps, not an unsupported assertion that the counit transports.

I tested the statements and proof on the following small cases. If E or I_V is empty, the bar terms and the evaluated left Kan resolution are zero; no nonemptiness hypothesis is needed. For u the identity, I_V is the undercategory with initial object (V,identity); after taking its opposite the colimit has the appropriate terminal object, and the evaluated resolution contracts to F(V). For terminal one-object categories the unnormalized bar includes identity chains and the augmented differential/homotopy formulas still hold; no unmentioned normalization is used. With R=Z and a coefficient Z/2, step 5 uses a projective module resolution and exact copowers, so it never substitutes Z/2 for a projective. Arbitrary infinite categories use set-indexed direct sums, and every element or homotopy calculation has finite support. If D is empty there is no evaluation object, so the pointwise assertion is vacuous.

Against delivery-errors B--E: no new unsplit node contains a proof, no new clause-node or duplicate is created, all notions already have the item's definition dependencies, all TeX uses single backslashes after JSON decoding, and all citations have literal statement evidence in citations.json. Each non-elementary input is an existing cited statement; the remaining calculations are given explicitly. No proof step exceeds 2000 characters (the longest is 964), and I checked that no shorter step hides an additional comparison theorem. The derived comparison and canonical counit are proved before passing to homology. There is no statement weakening, new coefficient hypothesis, cycle through a new node, or forbidden source route.
