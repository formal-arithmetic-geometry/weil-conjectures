# Worker report

## Files written

- dag/nodes/sec-smooth-purity/lem-route-integral-transition-comm-shift-exists-unique.json: split the provisional route statement into four proof steps; preserve its full recorded Lean signature and write the corresponding complete statement in words and TeX.
- dag/nodes/sec-smooth-purity/lem-pur-fully-faithful-composite-shift.json: one new statement-only Mathlib leaf, lifting a coherent shift through a fully faithful composite; matches CategoryTheory.Functor.CommShift.ofComp and CategoryTheory.Functor.CommShift.OfComp.map_iso_hom_app, Mathlib/CategoryTheory/Shift/CommShift.lean:520–578.
- citations.json: one verbatim statement quote for every step/node pair.
- searches.jsonl: unmodified log written by the required msearch command. No searches were imported or invented. write_split.py is only a sandbox construction helper and is not a project file.

## Attachments

None. Searches of lean/WeilConjectures for the blueprint tag and the transition-shift notion found no declaration stating the item. The attached declaration is in lean/Sheaf/Paper/SfAlgebraicallyClosedCoefficients.lean:118–147, and its proof is sorry. The existing proof of sfScalarExtension_exact_triangulated at ScalarExtensionExactIntrinsic.lean:180–233 establishes an existential exact shift for the rational functor, not this normalized integral uniqueness statement, so it is not an attachment.

## WANTED

None. The relevant current blueprint, Stacks source, Bhatt–Scholze PDF, project source and pinned Mathlib source are locally readable.

## What was wrong and what changed

The imported node was explicitly PROVISIONAL and its statement ended in a truncated Lean quotation, although its lean.statement field contains the complete declaration. I replaced that provisional transcription with the full mathematical assertion, including D, the prime distinct from D.p, the algebraic closure, both finite coefficient stages, arbitrary Y, the actual integral transition, and its normalization for every integer and object. This completes the requested transcription, rather than weakening or changing the attached declaration. There is no false-statement dispute or new geometric hypothesis.

The normalization is stronger than the mere existence of some exact structure: it uses the fixed ordinary-to-completed comparison. The proof therefore conjugates the specified ordinary derived shift, and does not pick the shift from the rational exactness existential. In particular, the direction is e = chi inverse, and the last factor before rearranging is beta inverse. The final equation has beta, not its inverse, on the left.

The ancestry command reports blueprint.from.node = None. The parent lem-general-algebraically-closed-coefficient-stages was created for the module Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients, not an existing DAG id, so its created.item chain ends there. I preserved that computed null and its via chain, filled a precise from.place, and recorded the actual source connection. The source docstring attributes the exact-transition clause to the retained def-weil-algebraically-closed-coefficients. The latest blueprint reorganizes the context into sec-six-functors-basics/sk-thm-sfb-qlbar-two-colimit, clauses (2) and (4). I read that latest unit; I did not substitute its current condensed coefficient categories for the intrinsic integral categories of the Lean signature.

## Searches and reuse

The mandated archive glob returned no directories for this item, including other groups. The active sandbox had no node or report, only dispatcher markers, so I copied the live item before editing. No repair note exists for this item.

I searched the whole DAG for the exact comparison declarations and for fully faithful/shift/composite formulations; inspected the existing normalized comparison, intrinsic constructibility, scalar preservation and exact-derived factorization nodes; and ran blueprint_refs.py search with shift, faithful, commutation, fully faithful, fully+shift and scalar+shift. The only fully+shift blueprint hit was def-amb-vector-integration, whose statement concerns affine bundle integration and is unrelated. There is no generic fully faithful composite shift node in the DAG. I searched the project Lean source separately before creating the leaf.

The required msearch calls cover LeanFinder, Loogle, LeanSearch and source grep. The first generic LeanFinder and LeanSearch queries found ofComp; source grep then located ofComp at line 563, OfComp.map_iso_hom_app at line 539 and ofComp_compatibility at line 580. I read the full hypotheses, construction and component formula at lines 520–588. An unqualified Loogle name was unknown; the qualified query returned the CommShift family, and that outcome is retained in the log. A second concrete integral-scalar phrasing produced only unrelated semantic hits, while the concrete-name grep had no Mathlib hits. The new node is a Mathlib leaf; the concrete item also needs the specific intrinsic categories, fixed comparison and uniqueness argument and is not itself a direct Mathlib attachment.

## Not duplicates

lem-pur-fully-faithful-composite-shift vs def-fd-integral-scalar-shift-structures: the existing node defines fixed shifts for a different ambient pbc integral setup with Noetherian finite-dimensional hypotheses; the new leaf is the general categorical lifting result with an arbitrary fully faithful functor and an arbitrary comparison e.

lem-pur-fully-faithful-composite-shift vs lem-pur-coefficient-scalar-shifts: that node constructs counit-normalized shifts on universal derived scalar presentations; it does not lift through a fully faithful composite or state this component equation.

lem-pur-fully-faithful-composite-shift vs lem-weil-pbc-exact-functor-derived-factorization: that existing Mathlib leaf constructs the shift of the exact termwise derived functor. The new leaf assumes H and I already have shifts and constructs the shift on F from I F isomorphic to H.

lem-pur-fully-faithful-composite-shift vs def-amb-vector-integration: the blueprint search hit concerns vector-bundle integration, not lifting coherent functor shifts. No same-tag new-node pair occurs: the new leaf is a Mathlib result and introduces no Stacks tag.

## Review by NB

For the item I read the complete signature and proof docstring in SfAlgebraicallyClosedCoefficients.lean:108–147, the exactness construction in ScalarExtensionExactIntrinsic.lean:180–233, the definition of the restricted integral transition in IntegralScalarExtensionConstructibleIntrinsic.lean:99–115, the definition of the ordinary termwise derived scalar functor in IntegralScalarExtension.lean:270–307, and the normalized comparison and its construction in SfScalarExtensionComposition.lean:728–806. For the only new node I read the pinned Mathlib ofComp hypotheses, its two coherence proofs and its component formula, not just the search snippets. For the supporting literature I read the latest qlbar two-colimit unit, Stacks derived.tex lemma-right-derived-exact-functor (015F) and lemma-additive-exact-homotopy-category (014X), sites-cohomology.tex lemma-derived-base-change (06YY), and the Bhatt–Scholze descriptions in Proposition 3.5.1 and Lemma 6.8.2. The blueprint and source docstrings are agent-written, so proof_origin.by is agent.

Step 1 uses the statement of lem-weil-integral-constructible-triangulated for inherited shifts and the exact inclusion, the statement of def-weil-derived-complete-integral-detailed for the fact that the intrinsic category is full, and the statement of lem-weil-integral-scalar-extension-constructible for the restricted functor. All have the stated prime and finite-extension hypotheses, and each allows arbitrary Y. Fullness/faithfulness is immediate because these Hom sets are precisely ambient Hom sets. The restriction-inclusion identification has identity underlying components by the definition of restriction, not a new scalar comparison theorem. I corrected the notation for lambda so its target is explicitly the ambient completed functor composed with I_E.

Step 2 uses the actual finite-free clause of lem-weil-finite-free-completed-scalar-comparison, not just its completion-isomorphism clause. A finite basis makes the forgotten ordinary tensor functor a finite direct sum; kernels and cokernels are then computed coordinatewise. This proves the exactness hypotheses needed by the existing Mathlib leaf lem-weil-pbc-exact-functor-derived-factorization. I checked that leaf states the natural isomorphisms for every integer and their compatibility with the exact-derived localization comparison. Thus h is the specified termwise ordinary shift used by the source, rather than an arbitrary coherent comparison. The inclusion structure is the one already supplied by step 1. No dimension, Noetherianity, flat-resolution bound or finite-field structure on Y is introduced.

Step 3 uses the data defined in def-zl-normalized-integral-scalar-comparison: a specified natural isomorphism from ordinary derived extension to completed extension on the intrinsic category, with the quotient-completion normalization. It does not ask that definition node to prove compatibility of that comparison with some preselected completed shift. The new Mathlib leaf is applied with I = I_L, H = G after I_E, and e = chi inverse. The source and target of each of its four factors agree: I_L F(K[n]) goes to H(K[n]), then H(K)[n], then I_L F(K)[n], then I_L(F(K)[n]). Its zero and addition laws are supplied by the Mathlib construction. Multiplication by beta gives precisely the requested equation. The source liftCompιIso is identity on underlying arrows, explaining why the Lean signature writes .hom and HEq without an extra lambda factor.

Step 4 uses only the full-subcategory inclusion specified by def-weil-derived-complete-integral-detailed. Both candidates have the same fixed right side in the equation; cancellation of the invertible beta gives equal underlying forward components. Equality in a full subcategory is equality of underlying arrows. Inverses, natural transformations and the structure then agree by inverse uniqueness, component extensionality and proof irrelevance. This is an elementary cancellation/extensionality argument, and no separate uniqueness lemma is needed.

I checked B1–B10: the new node contains a self-contained statement, no proof or hidden proof dependencies, explicit meanings of the functors/full faithfulness/coherent shift data, TeX with single mathematical escapes, the exact Mathlib declarations and lines, genuine recorded searches, and complete blueprint fields. For C1–C8 I opened every cited node statement; citations.json has a verbatim passage for each step/node pair; no step uses a theorem hidden in a dependency's proof. The only new proof dependency is a Mathlib leaf and no off-unit unsolved tool is needed. For D1–D5 the new leaf contains no integral coefficients or normalized chi and no uniqueness claim, so it is a reusable categorical input rather than a renamed clause of the item. The item itself writes the specialization, normalization and uniqueness argument. For E1–E7 I checked all functor domains, the inverse direction of chi, the beta cancellation, and arbitrary Y. There is no SGA source. All steps are below 2000 characters.

For small cases, E = L remains valid: chi can still be the fixed completion comparison, so I did not incorrectly replace it by an identity. The zero object and n = 0 obey the same equation via the unit law supplied by ofComp. Negative shifts use the existing full integer-shift structures, not an unsupported induction from positive n. For the leaf, taking I the identity recovers conjugation by e, and taking F,H,I identities with e identity gives identity comparisons. Empty/zero categories give vacuous component equations and the same logical proof. I found no counterexample or missing hypothesis.

## What remains unfinished

No mathematical part of this one-level split remains. No Lean was written or compiled. The server checks and direct delivery are the required remaining validation steps; their final results will be recorded below.

## Validation

The server check_dag returned OK with no finding introduced by this sandbox. The first delivery dry run required the Mathlib line as a structured mathlib_match.line field, even though the declaration and lines were already in how. I added line = 563 after reading the pinned source. I also clarified that the qualified Loogle query found the CommShift family, while the exact ofComp match came from LeanFinder, LeanSearch and source grep.

The final full dry run exited 0: `OK (not pushed) deliver/NB/lem-route-integral-transition-comm-shift-exists-unique at 48f31434d95: preflight passed`. This includes the server preflight, DAG and split checks. The only post-dry-run edit is this validation-result sentence; the two node files and citations are unchanged. The delivery contains one new node, which is one Mathlib leaf.
