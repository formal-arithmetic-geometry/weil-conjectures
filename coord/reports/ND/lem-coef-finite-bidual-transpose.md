# Stage-1 delivery: lem-coef-finite-bidual-transpose

## Files written

- dag/nodes/sec-six-functors/lem-coef-finite-bidual-transpose.json: statement, split into six steps, no Mathlib match; statement unchanged.
- citations.json: one verbatim statement excerpt for every dependency cited by every proof step.
- report.md: this report. searches.jsonl records the seven search commands actually run.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. The exact blueprint tag and key notion were searched throughout lean/WeilConjectures. A close existing formal core is CategoryTheory.MonoidalClosed.map_toIhomIhom_comp_dualComparison, WeilConjectures/SixFunctors/Etale/Derived/DoubleDual.lean:215, with the isomorphism consequence mapToIhomIhomArrowIso at line 237. I read their full declarations and proofs. They apply to a specified lax braided functor and its canonical dualComparison, not directly to arbitrary evaluation-preserving h_T on arbitrary ringed-site derived categories. Instantiating the scalar functor's symmetric monoidal structure and identifying the given h_T with dualComparison by the adjunction are additional steps. Thus this is partial formal coverage, not an exact attachment. The nearby HomComparison.lean theorem only has geometric/constructible hypotheses and contains sorry; it is not an attachment either.

## WANTED

None. All sources used are present locally.

## Corrections and scope

The item was unsplit, with no proof. Its statement is well-typed and true and needed no correction. The new proof retains the tensor comparison t in every expression, so evaluation preservation is always used in precisely its stated normalization. No naturality of the family h_T is assumed or used; only the two given evaluation identities are needed. No hypothesis of constructibility, perfectness, invertibility of delta, or flatness was introduced.

The nearest blueprint ancestor is cor-coef-finite-verdier. I read its current main-20261015 proof sentence about transposing evaluation, together with the item's chapter and unit. This split expands that sentence and stays on its route. The unit record is not the item's statement and was not edited. The imported Mathlib records are preserved, and the current command-log records are appended with their exact queries.

## Searches and duplicate check

I searched all DAG filenames and statements for double transpose, evaluation-preserving comparisons, tensor-Hom adjunctions, derived closed monoidal structure, and signed symmetry. Blueprint searches for bidual, double-dual compatibility and evaluation-preserving found no other blueprint statement of this item; same_as remains empty. No new node is necessary: the general closed symmetric monoidal theorem and the ringed-topos symmetric monoidal comparison theorem already state the tools required here. I also checked that neither dependency has a transitive path back to this item.

The seven msearch commands include two LeanFinder phrasings, two Loogle patterns, LeanSearch, and greps in CategoryTheory/Monoidal and LinearAlgebra/Dual. I read their results, then the actual Mathlib sources: CategoryTheory/Monoidal/Closed/Functor.lean:39-105 assumes CartesianMonoidalCategory, so expComparison_ev is not the general tensor assertion here. LinearAlgebra/Dual/Defs.lean:80,92,177 defines ordinary module evaluation/transpose and proves eval_naturality; it does not involve derived internal Hom, arbitrary dualizing complexes, or scalar extension. The rigid tensor-Hom results require dual objects. No exact or one-line specialization states the entire item. All services answered successfully.

## Not duplicates

No new nodes were created, hence no new/existing pairs require disambiguation.

## Review by ND

I checked delivery-errors B through E with the item, every cited statement and the sources open. For the item I read the current blueprint proof of cor-coef-finite-verdier. For its formal tools I read Stacks sites-cohomology.tex, Tag 08J9 (lemma-internal-hom, its proof and the preceding H0 computation), Tag 0FPT (lemma-symmetric-monoidal-derived), and Tag 07A4 (lemma-pullback-tensor-product and its K-flat total-complex construction). Stacks omits some symmetric coherence details; those are supplied here by the already existing DAG theorem, not silently inferred from a definition. No new-node sources need review and no prohibited SGA route is used.

Step 1 uses the full statement of lem-sf-ringed-derived-closed-symmetric-monoidal for its bijection, its evaluation normalization and natural symmetry, and lem-sfb-ringed-derived-monoidal-comparisons for compatibility of the specific canonical pullback tensorators with symmetry. That statement expressly allows unbounded complexes and nonflat structural maps. I specialize the geometric morphism to the identity and the ring map to A to B, then identify its pullback with S using lem-pur-derived-change-of-rings. The hypotheses hold because the site is small in the module universe and both ring sheaves are commutative. These are generic tools, declared in split_report.tool_uses, rather than changes to the unit's argument.

Step 2 uses exactly the adjunction bijection and inverse-transpose formula in the closed symmetric monoidal theorem. X=SK and Y=S(D_AK) give the common target D_BY and the common uncurried source X tensor Y. I checked all four types; in particular D_B(h) goes from D_B^2X to D_BY, not in the reverse direction.

Step 3 uses the supplied evaluation identity at T=D_AK, naturality of t from the symmetric monoidal comparison theorem, and the adjunction equation defining delta. The resulting map is u followed after S(ev_K composed with tau_{K,D_AK}) and t_{K,D_AK}^{-1}. I checked the inverse tensorator directions explicitly.

Step 4 uses naturality in the tensor parameter of the same stated adjunction. I wrote out why the precomposition map D_B(h) has the displayed evaluation identity: it is the inverse transpose under that natural bijection, not an extra unnamed theorem. The remaining equalities are tensor bifunctoriality, the defining transpose equation for delta_B, symmetry naturality, and the hypothesis at T=K. This step needs no compatibility at any third object. Every operation is between morphisms of the derived category; there is no unsupported inference from equality of cohomology groups or representatives.

Step 5 uses the symmetry-compatible tensorator equation explicitly stated in the comparison theorem and the injectivity of the adjunction bijection stated in the closed theorem. I checked the order of the two inverse t's and verified that substitution makes the two expressions identical. Its sign observation follows from the actual Koszul symmetry specified in both cited statements: extension is additive and degree-preserving, so (-1)^(ij) is unchanged.

Step 6 uses only the functoriality in the first variable stated in def-pur-derived-internal-hom: applying it to the two inverse equations for h proves the inverse equations for D_B(h). Cancellation gives exactly the displayed identification. It does not use the false assertion that all complexes are bidual-reflexive. The preceding formal steps are elementary substitutions into the cited bijections and coherence equations; Step 1 records the substantive structural results as non-elementary. The longest step has 983 characters, so none hides an argument in a step over 2000 characters.

I tested the calculation at K=0, Omega_A=Omega_B=0, u=0, at A=B with identity comparisons, and on shifted objects with odd degrees (the negative symmetry factor occurs on both sides). The first equality allows zero and noninvertible h; only the final conditional assertion uses their invertibility. A nonflat map such as Z to Z/2 also meets the structural theorem's hypotheses: the calculation is in derived tensor, so it never replaces derived tensor with ordinary tensor. These checks expose neither a missing hypothesis nor a statement dispute.

I generated citations.json from exact substrings of the current node statements and checked membership programmatically. No citations use facts available only inside the proof of a cited node. All existing-node fields outside the split-owned set are retained.

## Unfinished work

None in the stage-1 split. The delivery dry run and push are performed after writing this report; their terminal result is the delivery evidence.
