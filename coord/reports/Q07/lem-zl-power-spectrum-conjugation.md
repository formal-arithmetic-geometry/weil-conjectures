## Worker report

Files written: `dag/nodes/sec-deligne-laumon-general/lem-zl-power-spectrum-conjugation.json` (statement, split), `citations.json`, and this report. The sandbox initially contained only dispatcher brief markers, with no item, report, search log or running delivery process. There was no prior split to preserve or interrupted delivery to repeat. The repository item was copied without changing its statement, creation history, source or statement dependencies.

## New nodes

None. No new Mathlib leaves. Existing `p-linear-triangular` supplies an invariant flag and existing `lem-weil-pbc-block-triangular-determinant` supplies the determinant identity over any commutative ring, including K[T]. The diagonal-product identity is a three-line induction from that two-block identity, not another node.

## Attachments

No attachment for the item. Searches of `lean/WeilConjectures/` for the item tag, characteristic-polynomial powers, triangularization and conjugation found no declaration stating every clause. `Module.End.exists_complete_invariant_flag` and `Module.End.exists_basis_isUpperTriangular_toMatrix` in `WeilConjectures/Mathlib/LinearAlgebra/Eigenspace/Triangularizable.lean` belong to existing `p-linear-triangular`; the module contains no sorry. This delivery cites that existing node and does not edit its attachment. `LinearMap.conj_trace_pow_of_charpolyRev` concerns traces of powers, not the item's characteristic-polynomial and multiplicity clauses.

## WANTED

None. The blueprint and the source of every existing tool used are available locally. No SGA source is used.

## Findings and route

The item is true as written, including characteristic dividing n, singular operators and zero dimension. Its source is the current blueprint's `sec-deligne-laumon-general/sk-i-dl-general-real/thm-zl-real-mixed-by-curves.proof.md`, paragraph 1 final two sentences. I read this paragraph and the full proof, the chapter record, and the unit `sk-i-dl-general-real`: this is precisely the elementary powering calculation needed to preserve reality under constant extension. The imported item had no proof. Its seeded definitions were already the right ones. No statement dispute or source correction was needed.

The sources read for the tools were the full node statements; `sec-trace-formula/sk-p-linear-triangular/p-linear-triangular.md` and its unit (which explicitly assumes an algebraically closed field); and the live project triangularization module, with the complete-flag and triangular-basis declarations. The block determinant node is a generic Mathlib leaf: its Stacks place is smoothing.tex, Tag 07EY, label lemma-standard-smooth-include-generators, whose proof uses the block Jacobian. I read that passage; it is motivation rather than a claimed Stacks statement of the generic identity. Mathlib's matrix determinant source was also inspected. These are generic linear algebra tools, not replacements for a geometric unit route. The invariant-flag tool use is declared in split_report; the determinant citation is already a Mathlib leaf.

Whole-DAG keyword searches and whole-blueprint searches (`triangular`, `upper triangular`, `diagonal entries`, `determinant`, `conjugation`, `power spectrum`, `powers of`) found the existing triangularization and determinant nodes. No duplicate was created. All current Mathlib searches were run through msearch.py; their exact queries and actual hits are preserved in searches.jsonl and appended to the item's earlier search history. Two phrasings for the item found eigenvalue-power results and trace/nilpotence or Hermitian special cases, which do not give algebraic multiplicities for an arbitrary endomorphism. Searches for the auxiliary determinant identity found `Matrix.det_of_isUpperTriangular` (Mathlib/LinearAlgebra/Matrix/Block.lean:337), but the already-existing two-block node suffices, so no extra leaf was introduced.

## Not duplicates

No new nodes; no same-tag pairs to justify. The existing lower-block determinant node is reused rather than duplicated by an upper-triangular or diagonal-product node.

## Review by Q07

I checked the split against delivery-errors B–E with the source and every cited node open. There are no statement-only nodes to audit under B, and the unchanged item's objects and three notion references are self-contained. All seven per-step node citations have complete verbatim statement quotations in citations.json. No proof text of a cited node is used as its interface.

Step 1 takes exactly a full invariant flag with one-dimensional graded pieces from p-linear-triangular. The ambient field is algebraically closed, as its source unit and the live closed declarations require. Choosing one vector outside each preceding flag member and reversing the basis are elementary dimension and coordinate arguments, explicitly written. The flag citation is not used to claim diagonalizability.

Step 2 takes precisely the lower two-block determinant product from lem-weil-pbc-block-triangular-determinant, with p=1, q=s-1 and coefficient ring K[T]. The step states the base s=0 and the induction. The characteristic polynomial definition explicitly permits its computation in any basis as det(TI-B). The root multiplicity definition counts the maximum power of T-c dividing a nonzero polynomial. After collecting equal diagonal factors, the remaining factor evaluates nonzero at c, so cancellation and evaluation prove that maximum exactly; there is no appeal to geometric multiplicities or an uncited eigenspace theorem.

Step 3 uses only the two characteristic-polynomial definition nodes; their concrete matrix formulas are exactly the two determinants computed. Its sum over intermediate indices proves closure under multiplication and the diagonal formula, with the induction starting at B^0=I. It then applies the already-proved determinant induction from Step 2, not an unrecorded theorem about powers of spectra. Matrix multiplication represents composition by its coordinate definition. Reindexing products by the root multiset from Step 2 gives the stated formulas for the given enumeration.

Step 4 uses the root multiplicity node again for the monic product established in Step 3. The nonzero value of the residual product ensures maximality of the counted power. Its finite sum is over the distinct original eigenvalues with a^n=beta, so it includes all collisions and introduces no infinite summation. No separability of the power map is assumed.

Step 5 is an elementary occurrence-permutation calculation, not a citation of a reality definition that might lack the required implication. Equal multiplicities give a bijection of occurrences with their conjugates. The step displays the compatibility of powering with the field isomorphism and conjugation, then conjugates the full polynomial product and compares coefficients. A complex coefficient a+bi fixed by conjugation has b=0. Thus the step proves both powered multiset stability and the real coefficient assertion directly.

For E I tested V=0, n=1, A=0, a nonsemisimple Jordan block, eigenvalue collisions diag(1,-1) at n=2, and characteristic p with n=p. The formulas do not divide by eigenvalues, use diagonalizability, or assert injectivity of powering. At zero eigenvalues the reverse factor is 1 while the ordinary characteristic polynomial still counts the zero root. Empty determinant and product conventions give 1 in dimension zero. For conjugation, conjugate pairs and repeated real values satisfy the displayed occurrence argument; the existence of the isomorphism to C automatically restricts that final clause to characteristic zero.

No new lemma merely restates a clause (D1–D2), there is no dependency on a proof interior (C3–C4), and no step assumes an unstated hypothesis. Each step is below 2000 characters. I initially considered a new triangular determinant Mathlib leaf, but removed that plan after finding the existing two-block determinant node: its elementary induction is now written in Step 2. The detailed source proof is marked agent-written because the blueprint gives only the powering sentence, not this linear algebra argument. Nothing remains unfinished in the split; the required dry run and push follow this review.
