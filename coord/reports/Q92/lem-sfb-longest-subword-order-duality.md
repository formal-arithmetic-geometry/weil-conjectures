# Stage-1 worker report: lem-sfb-longest-subword-order-duality

Group Q92; 2026-10-24; direct delivery, with self-review and the maintainer's independent review to follow.

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-longest-subword-order-duality.json`: item, statement unchanged, four proof steps, status split.
- `dag/nodes/sec-six-functors-basics/lem-sfb-root-length-inversion-count.json`: new statement-only node; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-root-subword-reflection-chains.json`: new statement-only node; no Mathlib match.
- `citations.json`: one verbatim statement quote for every proof-step citation.
- `searches.jsonl`: actual msearch.py searches; the detailed search output was read during this session.
- `work/write_split.py`, `work/small_cases.py`: sandbox-only preparation and finite-example checks; neither is project source or a delivery node.

## Attachments

None. Searches for the exact blueprint tag and for Bruhat, subword, longest and Coxeter in `lean/WeilConjectures/` found no declaration stating the item. The occurrences of “longest” concern chains in commutative algebra. No Lean was written and no compiler, Lake or build command was run.

## WANTED

WANTED: Brion--Kumar, *Frobenius Splitting Methods in Geometry and Representation Theory*, Section 2.1, printed pp.61--63, for the item and its root-inversion prerequisite. The author's PDF was read online: https://www-fourier.univ-grenoble-alpes.fr/~mbrion/fbook.pdf . The local literature path recorded by the creator is absent.

WANTED: Björner--Brenti, *Combinatorics of Coxeter Groups*, Definition 2.1.1 (p.27), Lemma 2.2.1 and Theorem 2.2.2/Corollary 2.2.3 (pp.33--34), Corollary 2.3.3/Proposition 2.3.4 (p.37), and Lemma 4.4.3/Propositions 4.4.4--4.4.5 (pp.102--104), for the item and the two new nodes. Read online from the university-hosted text: https://sites.math.washington.edu/~billey/classes/reflection.groups/references/EntireBook.pdf . The local path `literature/bjorner-brenti-combinatorics-coxeter-groups.pdf` is a wanted reference, not a claim that a download exists. No document was downloaded or written to the repository. The item's proof is consequently marked `proof_origin.by = agent`, with the precise source and the explicit finite-root-system adaptation.

## What was wrong or incomplete

The item had an empty proof. Its mathematical statement is correct, including rank zero; no STATEMENT-DISPUTED correction is needed. Its source annotation incorrectly described conjugation by the longest element as reversing order. Conjugation preserves Bruhat order (Björner--Brenti Proposition 2.3.4(ii)); it is left or right multiplication that reverses it (part (i)). I corrected that source annotation, while retaining the item's statement and original source document. The proof below implements left multiplication as the statement requires.

The source's opposite-cell paragraph is geometric. It cannot establish this item's abstract root-system assertion without extra realization machinery, and citing the parent Schubert-geometry result would create a cycle. The split instead makes the numerical inversion count and the purely combinatorial subword theorem explicit, then gives the chain reversal itself. Neither new node mentions a longest element or asserts any order-duality conclusion.

The `blueprint_refs.py ancestor` command reports None for this item's current ancestry. I retained the null `from.node` and the existing explanatory place and via chain, and extended them for the two new nodes rather than inventing an imported ancestor. The latest blueprint's constructible-stability material has moved into `sec-six-functors/sk-thm-sf-kunneth-verdier/`; its current proof was read as context. This low-level combinatorial prerequisite neither changes the chapter nor replaces a unit step.

## Not duplicates

lem-sfb-root-length-inversion-count vs lem-sfb-longest-subword-order-duality: the new node counts sign-changing roots for every element; it has no longest element and no order relation. It is a numerical input, not the conclusion or a clause of the item.

lem-sfb-root-subword-reflection-chains vs lem-sfb-longest-subword-order-duality: the new node identifies two descriptions of comparability, with no longest element. The sign complement and reversal of each edge are proved in the item.

lem-sfb-root-length-inversion-count vs lem-sfb-root-sign-word-deletion: the existing node deletes one letter when a word makes a positive root negative; its statement does not identify the number of such roots with minimum word length. It will be relevant when the new count is itself split.

lem-sfb-root-subword-reflection-chains vs lem-sfb-root-sign-word-deletion: a one-letter deletion under a sign hypothesis does not state the two-way subword/chain criterion, notably the increasing-chain construction from a chosen reduced subword.

lem-sfb-root-length-inversion-count vs lem-sfb-simple-root-reflection-generation: generation proves existence of simple words, not their minimum length or a root count. The generation node is reused in the item.

lem-sfb-root-subword-reflection-chains vs lem-sfb-root-chamber-simple-transitivity: uniqueness of an element carrying one chamber to another does not characterize non-simple reflection chains or arbitrary reduced subwords.

lem-sfb-root-length-inversion-count vs lem-sfb-schubert-closure-cell-geometry: the existing geometric cell-dimension assertion has algebraic-group hypotheses and is an ancestor depending on this item; it is not the abstract real-root length formula.

lem-sfb-root-subword-reflection-chains vs lem-sfb-schubert-closure-cell-geometry: the existing result asserts expression independence and geometric closure relations but not the abstract right-root-reflection-chain equivalence, and it depends on this item.

Before creating either node I searched the whole DAG's statements and source text for Bruhat, subword, Coxeter, inversion sets, exchange conditions, lengths versus positive/negative roots and reflection chains. I opened the relevant root-generation, sign-deletion, chamber and Schubert statements. Whole-blueprint searches through `tools/blueprint_refs.py search` for Bruhat, Coxeter and subword gave no match; reflection, length and root returned unrelated imported nodes. No equivalent imported blueprint node exists. No Stacks tag is asserted: these facts use the cited root/Coxeter textbook sources, not an invented algebraic-geometric tag.

## Review by Q92

I read Brion--Kumar Section 2.1 at printed pp.61--63 in the author's PDF. Equation (1) supplies the inversion-root description and distinctness, and the subword paragraph and opposite-cell paragraph explain the role of the item. I read Björner--Brenti Definition 2.1.1, the proof of Lemma 2.2.1, the proof and statement of Theorem 2.2.2, Corollary 2.2.3, and the finite-case discussion through Proposition 2.3.4. For the count node I also read Lemma 4.4.3 and Proposition 4.4.4 with its induction, and Proposition 4.4.5 for the root/reflection correspondence used in the chain node. Finally I read the local Milne PDF, Appendix C.8--C.11 and C.19--C.22 (pp.609--612): these state the raw reflection formula and root-base hypotheses and the Coxeter presentation for this finite real-root setting. The new nodes are explicit specializations to these raw hypotheses; neither silently identifies a given geometric group with a reflection group.

In step 1 I reopened the entire statement of `lem-sfb-simple-root-reflection-generation`; it asserts exactly the equality of the root-generated and simple-generated subgroups under this item's hypotheses. This is the sole group identification used. The new count node is stated for that simple-generated subgroup, with the same base and the same minimum-word definition, so it applies to every element of W, including w0 and its inverse. Its conclusion is exactly the count step 1 uses, as the quote in citations.json records. Complementing signs requires only that each element permutes the roots and that roots have one of the two signs, which follows directly from the root hypotheses and the base definition. The inverse of a sign-swapping bijection also swaps signs. This proves both displayed length-complement formulas; neither formula is merely asserted by a citation about some other length.

In step 2 the new chain node supplies an increasing chain starting at a and ending at b, using right multiplication by root reflections. I checked that this is precisely its condition (ii), and not a hidden appeal to its future proof. The displayed formula for y_j uses the same right reflection, because the original edge can be reversed using its involution. Reflection involutivity is direct substitution into the orthogonal-reflection formula, not a new lemma. Applying step 1 reverses the strict inequality. The other direction of the very same cited node changes the constructed chain back into the item's existential reduced-subword relation. Every object remains in W.

In step 3 I separately checked the reverse implication, using w0 inverse rather than silently assuming w0 squared is one. Given a chain from w0 b to w0 a, reversing it and multiplying by w0 inverse starts at a and ends at b. The inverse complement formula already proved in step 1 reverses the lengths. The chain criterion again says exactly what is taken from it. Step 4 only handles empty chains and the trivial group forced by V=0. No assertion of expression independence, transitivity, Coxeter presentation or geometric flag realization is used uncited in the assembly.

For both new nodes I checked the B1--B10 requirements: only statements, no proof sketches or proof dependencies; every object and root-system hypothesis is introduced; simple-word length, reduced words and the subword subsequence are defined inline; finite-dimensionality cites its existing definition; ordinary TeX escapes appear once. Each has a precise source, a complete blueprint place and actual logged searches. These statements are substantive theorems, requiring the inversion/exchange argument and the subword theorem respectively, rather than elementary two-line consequences. They are not Mathlib leaves: the source hits for RootPositiveForm.rootLength at RootPositive.lean:170--175 count a squared norm, and CoxeterSystem.IsRightInversion at Inversion.lean:127 only defines a single decreasing edge. I read those lines and the deletion identity at Inversion.lean:349 and its reduced-word consequence at line 373. None states either new result, even for an abstract Coxeter system, let alone the raw real-root formulation. Both node-specific questions were searched with LeanSearch, LeanFinder, Loogle, grep and a second LeanFinder phrasing, with exactly the issued query strings preserved. Services answered successfully.

I checked the C and D failures against each step: all non-elementary inputs occur in uses and proof_deps; the quotes are verbatim from statements; no proof of an existing node is mined; neither the parent geometry nor any descendant is cited. The independent data in the two new nodes are numerical length and a combinatorial characterization; the entire opposition argument stays in the item. No off-unit tool is used. All four step texts are shorter than 2000 characters (708, 590, 507, 268), so no long step conceals an extra comparison theorem.

For E1--E7 I checked that spanning and reducedness are retained, no nonempty-root or positive-rank hypothesis is introduced, and the reflection is on the right throughout. I checked zero roots, A1, equality of endpoints, and the smallest nontrivial rank-two examples. The sandbox's pure-Python enumeration checked the subword/chain equivalence, the length complement and the desired equivalence for every ordered pair in A0, A1, A2, A3 and I2(2), I2(3), I2(4), I2(6); the type-A cases also checked inversion counts. All checks passed (877 ordered pairs total across the eight examples). These are finite sanity checks, not a replacement for the proof. The source-annotation error about conjugation was the only mathematical wording corrected.

## Unfinished work

No part of this one-level split remains unfinished. The two new statement-only nodes deliberately remain unsplit for future items. Repository/launcher files were not edited, no git command was run in the shared repository, and all writes are confined to the authorized sandbox. Dry-run and push results are recorded below when the delivery tool exits.

## Delivery validation

The required `deliver.py Q92 lem-sfb-longest-subword-order-duality --no-push` exited successfully and printed `OK (not pushed)` at 4e122d7e747. The server preflight, including the DAG and split checks, passed. The dry run had fully exited before the push invocation. The only following report edit is this validation record; the node files and citation quotes are unchanged.
