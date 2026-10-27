# Stage-1 worker report

1. Files written: `dag/nodes/sec-trace-formula/lem-trf-tensor-base-change-ideal-power-quotients.json` (statement, split; not itself a Mathlib leaf), `citations.json`, and this report. `searches.jsonl` was produced by msearch.py. New nodes: 0. New Mathlib leaves: 0.
2. Attachments: none. Searches of live `lean/WeilConjectures/` by the blueprint tag and by ideal-power quotient, congruence and tensor/base-change terminology did not find a declaration giving all the item's hypotheses and conclusions. Existing completion-specific results do not give the arbitrary scalar-congruence statement.
3. WANTED: none.
4. The imported statement is retained verbatim. Its empty proof is replaced by an explicit inverse construction and the kernel calculation on pure tensors. Its statement dependencies gain the existing algebra/ideal-power/quotient definition, which actually defines these notions. The blueprint ancestor is `lem-trf-local-term-locality`, through the inherited completion branch; latest blueprint text does not state this algebraic lemma explicitly. No unit or chapter route is changed. The underlying algebra is proved here, rather than attributed to a nonexistent exact Stacks theorem.
5. Unfinished work: none at stage 1. This is a natural-language split only; no Lean was written and no compiler or build was invoked.

## Sources and searches

Read `literature/blueprint/latest/blueprint/sec-trace-formula/_section.md`, `sk-i-curve-zero/_section.md`, and `sk-i-curve-zero/lem-trf-local-term-locality.md` and its proof. The branch under (1) and (2) is specialization to the normal cone. Read the actual tensor construction in `literature/stacks-project/algebra.tex`, Tag 00CX (`lemma-tensor-product`), including its bilinearity relations and proof that pure tensors generate. Checked Tag 00CX against `tags/tags`.

The specific finite-congruence argument is agent-written; Tag 00CX supplies the tensor construction, not the whole conclusion. The existing Mathlib leaf `lem-weil-pbc-algebra-tensor-pushout-universal-property` supplies the ring structure, structure maps and the universal mapping property. Read its entire statement, its dependency `def-weil-pbc-algebra-hom-quotient`, and the module-tensor definition. No external source or SGA route is used.

Repeated the item's Mathlib searches through msearch.py: LeanSearch, Loogle, two different LeanFinder phrasings, and two Mathlib grep patterns, all recorded verbatim in the item and in searches.jsonl. Read the returned hits and the relevant source: `Mathlib/RingTheory/TensorProduct/Quotient.lean:51,61,66` identifies tensoring with an actual quotient, while `Maps.lean:810,816,822,829` constructs tensor algebra maps and `Basic.lean:353,363` gives extensionality. None alone specializes in one line to the kernel-congruence calculation for arbitrary B and larger J. The corresponding existing DAG leaves are reused instead of duplicated. Searched the whole DAG by Tag 00CX and tensor/quotient/universal-property terminology, and blueprint_refs.py for tensor quotient, scalar congruence and ideal-power quotients; no imported blueprint node states the item in another form. Existing quotient-base-change and tensor-pushout nodes have been opened and read.

## Review by Q32

I checked every step against the cited statements, with the node files and Stacks tensor construction open.

Step 1 uses `def-weil-pbc-algebra-hom-quotient`, which explicitly defines ideal multiplication and powers and says quotient projections are surjective ring/algebra maps with the prescribed kernel. Expanding I^n into sums of products proves rho(I^n) is contained in J^n from the actual hypothesis IC contained in J. This verifies the representative formula for bar-rho and does not assume injectivity of rho or equality IC=J.

Step 2 uses `lem-weil-pbc-algebra-tensor-pushout-universal-property`, clause (1) for the two structural ring maps and clause (2) for h(c tensor b)=[c]g(b). I verified the inputs q and g have exactly the same R-structure: g(iota(r))=[rho(r)], using pi iota equal to the quotient map. The target E is a commutative R-algebra. There is no hidden flatness, Noetherian, finite-type or local hypothesis. The full verbatim cited clause is in citations.json.

Step 3 uses the algebra/quotient definition again. The two descended maps are not merely asserted: every generator f(k)d of KD is killed by h, and f(K) is contained in KD; preservation of ring operations follows on representatives. This quotient-descent check is elementary and is written out. No sheaf quotient notion is substituted for an ordinary ring quotient.

Step 4 uses `def-weil-pbc-module-tensor-product`, whose statement explicitly supplies bilinearity and generation by pure tensors. Choosing r representing pi(b) gives b-iota(r) in the specified kernel I^nB. The proof expands it as a finite sum of ideal multiples and balances each scalar across the tensor product, showing its image lies in KD. This is the key computation, retained in the item rather than restated as a new lemma. The products are in the stated commutative tensor ring, not an unidentified tensor module.

Step 5 uses the same tensor-definition statement specifically for generation by pure tensors. The two composites are evaluated on their actual generators, with Step 4 proving the second identity. The formula for the inverse follows from the constructed h, so the formula clause is established along with bijectivity. Every cited node's verbatim statement is included for each individual step in citations.json; no step borrows an uncited node's proof.

For small cases, if I=0 the hypotheses make pi:B to R an isomorphism and the formula reduces to ordinary scalar cancellation. If J=C, both quotient rings are the zero ring, so the same unital formulas apply. If I=R then IC=C forces J=C and again both quotients vanish. For B=R with pi the quotient map, the result reduces to the identity of C/J^n. For a nontrivial congruence kernel, take R=Z, I=(p), B=Z/p^n, C=Z and J=(p): D=Z/p^n and alpha is the identity. These checks confirm the exponent and inverse formula; no assumption of a proper ideal is needed. Surjectivity of pi is retained, although the identity pi iota=q already implies it.

I reviewed delivery-errors B through E, including both copies in the file. There are no new nodes, no unsplit nodes carrying proofs, no restated clauses, and no duplicate-node obligation. Each of the five proof steps is under 500 characters, so no step exceeds the 2000-character long-step threshold. The only non-elementary construction is the tensor algebra universal property and is cited as its existing Mathlib leaf; all remaining quotient and balancing calculations are explicitly written. I corrected the missing definition dependency and made the proof origin explicitly agent-written, preserving all inherited metadata.

## Not duplicates

No new nodes were created. The existing tensor universal-property leaf and the existing algebra/quotient and tensor definitions are cited directly.
