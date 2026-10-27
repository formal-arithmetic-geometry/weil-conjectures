## Worker report

1. Files written: `dag/nodes/sec-trace-formula/lem-trf-finite-scalar-power-common-kernel.json` (statement, now split; Mathlib verdict: no match), `citations.json`, and this report. No new nodes and no Mathlib leaves. The search command produced `searches.jsonl`.
2. Attachments: none. Searches in `lean/WeilConjectures/` for the exact blueprint tag, common kernel/annihilator, scalar powers and joint injectivity found no declaration stating this item. The scalar-power torsion bound in `AlgebraicGeometry/Morphisms/PuncturedPrincipalEventualScalarImage.lean:39` assumes Noetherianity and bounds one scalar's torsion; it is not this theorem. The finite-dimensional common-kernel argument and tensor-product detection results also have different statements.
3. WANTED: none. The proof source is present.
4. The imported statement is correct and is unchanged. The missing proof is now the converse induction of Stacks Tag 0565, expanded to make both decreases of the induction measure explicit. No statement dispute or unit-route departure was found. The unit's current blueprint text differs from the historical unit record, but this auxiliary algebra calculation stays on its inherited provenance chain and changes neither unit nor chapter.
5. Unfinished mathematics: none for this one-level split. No Lean was written and no compiler/build was run. Delivery checks follow this report.

## Sources and searches

I read `literature/stacks-project/algebra.tex:4405` (label `lemma-when-injective-covering`, Tag 0565, checked in `tags/tags:6698`), including its full statement and converse proof. It permits an arbitrary module over a commutative ring, assumes joint injectivity only, and proves the positive-exponent assertion by induction. No finite generation, Noetherianity, reducedness, unit-ideal condition or individual scalar injectivity is needed.

I read the chapter and unit records and the current blueprint at `literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/` (`latest` points to `main-20261024`), including `_section.md` and `lem-trf-local-term-locality.md`. I also read the parent affine schematic-density split: its first step uses this item for M=A. The inherited ancestor, precise place and via chain are preserved. This is not the unit's key node, so no unit realization field is edited.

Whole-DAG searches for Tag 0565, common kernel, common annihilator and positive powers, and `blueprint_refs.py search` for `common kernel`, `scalar power` and `0565`, found no duplicate of the item. Engel's matrix theorem is about a Lie algebra of nilpotent operators and a nonzero common kernel; regular-sequence power lemmas concern successive quotient modules. Neither states the present joint-injectivity assertion. There are no newly created nodes requiring duplicate comparisons.

The inherited Mathlib search records were retained and their results read. New searches used the required `msearch.py` command, with exact queries recorded in the item's `mathlib_searches` and in `searches.jsonl`: LeanFinder for finite commuting scalars with zero common kernel; LeanSearch for joint injectivity of positive powers; Loogle `IsSMulRegular.pow`; and two grep searches in `Algebra/Regular` and `RingTheory`. These give two semantic phrasings before the no-match conclusion. All services returned successfully. The old query `Submodule.annihilator, pow` was invalid (unknown identifier `pow`), as its inherited results already explain; it is not evidence of absence.

I read `IsSMulRegular.pow` and `pow_iff` at `Mathlib/Algebra/Regular/SMul.lean:150,158`: these require a single scalar to act injectively. That hypothesis does not follow from joint injectivity. `Ideal.iInf_ker_le` at `RingTheory/LocalProperties/Basic.lean:555` concerns all prime localizations, not powers of finitely many scalars. The Fitting decomposition at `RingTheory/Artinian/Module.lean:326` assumes additional chain conditions and concerns one endomorphism. The other returned types concern generalized eigenspaces, individual iterates, linear independence or preservation of already-vanishing iterates, not this theorem.

## Review by Q03

I checked the item and all four steps against Tag 0565's converse proof, rather than using the localization equivalence as a black box. The statement keeps n=0 and arbitrary positive exponents. Its inline module axioms provide the identities used below; its sole statement dependency actually defines the finite direct sum.

Step 1 cites `def-weil-pbc-direct-sum-modules`. I opened that node's statement: it defines finitely supported coordinate families with componentwise addition and scalar action. This gives the zero tuple and the one-element empty sum directly; it does not assert an uncited injectivity theorem. Taking the image of z equal to the image of zero turns the assumed injectivity into the zero-common-kernel hypothesis. For n=0 the same assumption forces every element to be zero. The quote in `citations.json` is copied verbatim from that definition.

Step 2 sets up strong induction uniformly over every tuple and every module element, with measure sum(e_i-1). Nonnegative summands show that measure zero means all exponents equal one, so the base case is precisely Step 1. Only finite-sum arithmetic and the hypothesis are used; no citation is hidden.

Step 3 chooses e_k>1, whose existence follows from the positive measure. With z=f_k m, decreasing the kth exponent by one keeps it positive and decreases the measure by one. I checked separately the kth equation and every j different from k. The latter uses exactly commutativity and action associativity: f_j^{e_j}(f_k m)=f_k(f_j^{e_j}m)=0. Thus the first induction application is legitimate for the same ring, module and original jointly injective scalar family. It gives f_k m=0 without cancelling f_k.

Step 4 applies the induction hypothesis a second time, now to m with kth exponent replaced by one. The newly proved equation supplies its kth hypothesis; all other equations are unchanged. The measure decreases by e_k-1, which is positive. This is the final inference omitted by a loose phrase such as “decrease the exponent”; it is written in full. Steps 2–4 use no cited nodes and are elementary induction, arithmetic and module identities. No step exceeds 2000 characters and none conceals a comparison or other non-elementary lemma.

For small cases I checked n=0, M=0 (including the zero ring), all exponents one, and n=1 (the usual repeated cancellation argument). For A=Z/6Z, M=A and scalars (2,3), neither scalar is individually injective, but their common kernel is zero; positive powers have the same joint property, illustrating why the single-scalar Mathlib lemmas are insufficient. In the dual numbers k[epsilon]/(epsilon^2), the singleton (epsilon) fails the hypothesis and is correctly excluded; adjoining the scalar 1 makes the hypothesis and conclusion hold. Unequal exponents are covered because both induction applications change only the chosen coordinate.

Against delivery-errors B–E: no new statement-only task, duplicate or restatement is introduced; TeX is encoded once; the source is the verified tag and label; the only cited statement says exactly what Step 1 uses; every remaining inference is explicitly elementary; the proof follows the source and has an actual base and two strictly decreasing induction applications; no extra hypothesis, affine-geometric identification, transport, or circular dependency is used. No repair of the mathematical statement was necessary. I expanded the source's two induction applications and explicitly handled the empty family.

## Not duplicates

No new nodes were created, hence there are no new/existing-node pairs to compare.
