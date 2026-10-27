# Q38 stage-1 report: lem-sfb-cofactor-local-descent

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-cofactor-local-descent.json: statement unchanged; split into seven proof steps; no new nodes and no new Mathlib leaves.
- citations.json: one verbatim statement quotation per step/node citation.

## Attachments

None. I searched the project WeilConjectures source for the blueprint tag and cofactor, exterior/localization and determinant/cokernel notions. There is no declaration stating this construction. The related Sheaf.LinearAlgebra.TwoTermCofactorNaturality theorem existsUnique_twoTermCofactorPresentation still has sorry (line 220), so is not an attachment. Its naturality theorem also has sorry.

## Wanted sources

None. All sources actually used are available in the read repository.

## Problems and corrections

The item was statement-only, with no existing sandbox attempt. Its statement is true and is retained verbatim. Stacks 0E9Y states its geometric construction for a short exact presentation, and explicitly omits well-definedness. Our item only constructs the cofactor map, without the isomorphism criterion, and does not need injectivity of u. The repeated-factor calculation establishes that distinction directly; no source theorem with a missing injectivity hypothesis is applied.

The inherited blueprint ancestor is null; blueprint_refs.py ancestor prints None. I preserved that field and its detailed place/via chain. I read the current latest blueprint's sk-thm-sf-ctf-stability unit and direct-images proof (3), and the chapter and DAG unit records. They frame the existing alteration-related prerequisite chain, rather than state the algebraic cofactor lemma. No unit or chapter record changes, and no alternative geometric route is introduced.

The supporting scalar-comparison theorem already exists as lem-trf-projective-exterior-scalar-comparisons. I use its general finite-projective exterior and dual comparison statements, not its determinant exact-sequence clause. Existing module-cover exactness supplies descent; no new lemma merely restates those facts. The rank-one change-of-basis cancellation is written explicitly rather than assuming a determinant-change lemma. No step exceeds 2000 characters.

## Unfinished work

None for this one-level split. Existing unsplit supporting nodes remain their own items.

## Not duplicates

No new nodes. Whole-DAG title/concept searches found the existing scalar-comparison, exterior-free-basis, localization tensor/exactness and matching-family nodes, which are reused. Whole-blueprint searches for cofactor, exterior, projective exterior and determinant found no imported node stating this item. The broader determinant and exterior material is about different assertions; none is recreated.

## Review by Q38

I read duality.tex Tag 0E9Y (lemma-determinant), including the wedge formula and the sentence omitting well-definedness. I also read algebra.tex Tag 00DM (section-tensor-algebra), the alternating relations and finite-free wedge basis, Tag 0C6F (lemma-tensor-algebra-localization), Tag 00NX (lemma-finite-projective), and the statement and proof of Tag 00EK (lemma-cover-module). I read more-algebra.tex 0FJ9 (section-determinants), 0FJB (lemma-det-ses), and perfect.tex 0FJY (remark-functorial-det) to check the supporting comparison node's scope. No new nodes need separate source validation, and no SGA source is used.

For step 1 I opened the complete statements of finite-projective-standard-free-cover, free-base-change-tower, and finite-projective-rank-locally-constant. The first gives finite unit-ideal covers; it does not supply the fixed lengths, so the proof separately uses the stalk-rank hypothesis and preservation of the basis length to identify those lengths. Products of the two unit-ideal families form a common cover by the displayed product identity. Zero charts are treated separately, so rank detection at a nonexistent prime is never used.

For step 2 I opened the exterior-algebra and exterior-power-free-basis statements. The splitting of P is available by the item's explicit direct-summand hypothesis. Applying each split map factorwise respects the alternating quotient and composes to the identity on pure wedges. Thus this is a short retract argument, not an uncited theorem asserting that exterior powers preserve projectivity. The containing wedge of A^n is finite free by the cited statement, including degree zero and degrees above n. This proves the actual finite-projectivity hypothesis required in step 3.

For step 3 I read projective-exterior-scalar-comparisons, localization-tensor-product, localization-module-exact and the module-localization definition. The first explicitly supplies both displayed pure-wedge and dual isomorphisms, their evaluation formula and identity/tower compatibility, for every ring map and direct summand of a finite free module. It therefore applies to P,Q and, by step 2, J; it requires no flatness. The tensor node gives the balanced localization comparison with denominator multiplication, and exact localization gives the cokernel identification; fraction presentation gives surjectivity. No comparison is inferred merely from a definition of exterior powers.

For steps 4 and 5 I checked the cited exterior-algebra and free-basis statements again. They provide multilinearity, alternating vanishing, spanning wedges and the free rank-one top wedge of a module with the given basis. Replacing v by v+u(x) gives a sum of repeated wedges, which vanishes even if u has a kernel. For a new basis, I wrote both coordinate matrices and their alternating expansions. The inverse scalar is established from the two basis changes, not by dividing in A. The factor a in the image wedge cancels the factor b in the dual generator, with ab=1. Thus characteristic two, zero divisors and the zero ring cause no sign or cancellation exception. The empty matrix has coefficient 1.

For step 6 I opened cover-module-exact and the localization definition. The node's statement explicitly includes both unique gluing of matching families and injectivity; these are the exact two assertions the step uses. The overlap equality follows from the proved basis calculation and explicit comparison formulas. Linearity and annihilation of u(P) are checked after localization and descend by injectivity. The localized map is determined on every fraction by its values on v/1, so the construction gives maps, not only a collection of sections.

For step 7 I reopened free-base-change-tower, cover-module-exact, exterior-power-free-basis and exterior-algebra. Over arbitrary B the images of f_i still generate 1, without any freeness assumption on Q_B. The two bases of P on B_{f_i} compare by step 5, and the injectivity assertion applies to the target module over B. Uniqueness on the original cover then gives independence from every other standard free cover. For c=0, cover injectivity first proves P=0; the degree-one exterior identification follows from the defining tensor quotient (or chartwise free-basis identification and the same injectivity). The empty wedge and tensor unit give the stated map. Over A=0 all modules and both sides are zero; even an empty cover causes no obstruction.

I tested u=0 with c>0 (the cofactor map is zero), c=0 (the identity degree-one map), c=1 over k[epsilon]/(epsilon^2) with u(a)=(epsilon a,0) (the formula is epsilon times the second coordinate), and a basis rescaling by a unit (the two factors cancel). These tests check the absence of injectivity/reducedness hypotheses and the normalization. I checked all cited nodes' dependency closures: none reaches this item, so the split introduces no cycle. Tool uses are declared for generic algebra from other units, including the scalar-comparison node; no geometric theorem is substituted for a unit step.

The required search commands were run for the item with two semantic phrasings, Loogle, LeanSearch and grep, and their real results are retained in searches.jsonl and copied into mathlib_searches. I read Mathlib/Algebra/Module/StablyFree/FreeOfInvertible.lean:25-35: cofactorToLeft operates on a given split product and is not this cokernel descent. Semantic hits were square endomorphism determinants, presentations or cokernel universal properties. No complete match or one-line specialization was found.
