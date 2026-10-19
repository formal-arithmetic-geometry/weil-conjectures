# Worker report: lem-pur-quasi-regular-prefix-quotient

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-quasi-regular-prefix-quotient.json`: statement; split into eight steps; no Mathlib match.
- `citations.json`: a verbatim statement quotation for every step/dependency pair.
- `searches.jsonl`: actual Q20 search-command log, retained alongside the item’s earlier Q16 searches.

New nodes: 0. New Mathlib leaves: 0. No unit record changed (this item is not its unit's key node).

## Attachments

None. Searches in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the exact blueprint tag, item identifier, quasi-regular terminology, `061R`, and prefix-quotient terminology found no declaration. The upstream Lean-name index also had no candidate. Upstream master is not used as evidence of a completed proof.

## WANTED

None. All sources used are present locally.

## Corrections and scope

The statement is unchanged. It is Stacks Algebra Tag 061R (`lemma-truncate-quasi-regular`) with M=A, with the hypothesis and conclusion expanded using 061P (`definition-quasi-regular-sequence`) and the canonical map of 061N (`equation-quasi-regular`). Read `algebra.tex` lines 16855–16893 and 17026–17057. There is no statement dispute. The source's expression involving n−1 is used only for n≥1; the degree-zero map and the empty-sequence cases are handled separately.

The imported node had no proof or Lean audit. The proof now spells out why an element outside J^(n−1) has an initial form at one of the finitely many degrees 0,…,n−2. This avoids incorrectly requiring J-adic separatedness to use the source's last sentence. The proof does not assert that f_1 is a nonzerodivisor on A and does not use the later Noetherian-local regularity node (which depends on this item).

The inherited unit is `sk-prop-a1-kummer`. I read its record and the chapter record and left all route metadata unchanged. The blueprint ancestry is `lem-pur-divisor-class`, opening proof sentence “Use the frame class of [def-pur-frame-class]”, through the smooth-pair local-equation and relative-regularity chain listed in `blueprint.from.via`. I read that sentence in the current main-20261015 blueprint. This is a generic algebraic input to that construction, with no cohomological-route substitution and no SGA citation. The associated-graded structure theorem from `sk-thm-p1` is declared in `split_report.tool_uses` as a generic multiplication/scalar tool; the unit offers no separate theorem supplying these operations.

## Searches and reuse

Before deciding on nodes I searched the whole DAG for 061R, 061P, 061N, quasi-regular and associated-graded terms, and ran `tools/blueprint_refs.py ancestor` and `search` for the item, quasi-regular, associated graded and the combined truncation terms. There is no blueprint node with this statement. The “associated graded” blueprint hit is an exact-couple morphism statement, not this algebraic result. The nearby regular-sequence polynomial and quasi-regular flat-quotient base-change nodes are different assertions; the first assumes regularity and the second assumes coefficient-ring flatness not present here. Neither can supply this truncation argument. No duplicate or restated-clause nodes were created.

Mathlib searches were made through the prescribed msearch.py command and their output read. LeanFinder was tried with both quasi-regular truncation and the polynomial associated-graded quotient phrasing. LeanSearch returned Rees, internal gradings and finite-type quotient statements. The initial Loogle pattern had an unknown `Ideal.Quotient` identifier; that diagnostic is recorded as an invalid query, and the successful `MvPolynomial, "quotient"` search was then run. I read RegularSequence.lean:21, 135–147, 228–258, ReesAlgebra.lean:14–45 and Polynomial/Quotient.lean:198–272. Weakly regular truncation already assumes the injectivity this item's hypothesis does not state, and the polynomial quotient theorem quotients a coefficient ideal. None is an exact match or a one-line specialization. The earlier searches on the item are retained rather than rewritten as Q20 work.

## Review by Q20

I compared the unchanged statement with 061R for arbitrary commutative A and every prefix, including all its quotient and coefficient identifications. No local, Noetherian, proper-ideal or nonzero-ring hypothesis has been introduced. I opened all four dependency files: `def-weil-pbc-algebra-hom-quotient`, `def-weil-pbc-mv-polynomial-ring`, `def-weil-pbc-associated-graded-ring`, and `lem-weil-pbc-associated-graded-ring-structure`. The last is a theorem, rather than a definition standing in for the needed multiplication theorem. Its clauses (1)–(3) explicitly provide representative multiplication, graded ring structure and the coefficient action. The quotation file copies these actual statements, not their proofs.

Step 1 uses the algebra/quotient definition: surjectivity, kernel and ideal powers. Expanding generators shows q(J^n)=K^n, and a representative calculation gives B/K=C. There is no appeal to a base-change or flatness assertion.

Step 2 uses the polynomial definition’s coefficientwise monomials, the associated-graded definition’s components, and the structure theorem’s homogeneous product. Multiplication by a variable shifts exponents injectively even over a ring with zero divisors. Thus the nonzero initial class of y gives a nonzero class of ty. The map Φ is supplied by the item's hypothesis; no claimed stronger regularity is used.

Step 3 uses only the ideal-powers definition and Step 2. The least failed filtration level is chosen in a finite nonempty set when y is outside J^(n−1); its predecessor exists because J^0=A. The contradiction uses n≥m+1. I checked n=1 separately, so no negative ideal power occurs. This proves the intersection equality within the item, in a short explicit argument, rather than creating an elementary helper node.

Step 4 uses the quotient definition to describe every kernel class by representatives, the associated-graded definition for the direct sum, and all three structure-theorem clauses to check the induced graded algebra map. A representative z in J^(n+1) exists by Step 1, and x−z is indeed in both J^n and tA. The converse is checked as well. This does not invoke an uncited quotient-comparison lemma.

Step 5 combines that explicit kernel description with the intersection equality already proved and the structure theorem's homogeneous product. Under Φ every such kernel class is multiplication by T_1 on a degree-(n−1) polynomial. The inverse Φ has the required degree because Φ is the assumed graded isomorphism. Degree zero is the identity of C.

Step 6 uses exactly the polynomial node's finite monomial description. It separates a homogeneous polynomial into the terms with first exponent zero and the other terms, visibly factors the latter by T_1, and compares disjoint exponent supports for injectivity. This proves both directions without citing a polynomial quotient theorem or presuming C is a domain.

Step 7 uses the polynomial node's existence and uniqueness clauses to identify the constructed algebra map with the canonical one. It uses the associated-graded node's finite-component description to assemble degreewise bijections, and gives the elementary inverse-homomorphism check. Thus it proves a graded C-algebra isomorphism, not merely an additive bijection.

Step 8 applies the already proved one-generator assertion in an explicit induction whose invariant is the item's canonical polynomial isomorphism for B_i. The iterated quotient identifies with B_(i+1) by the representative a mod I_(i+1), and its kernel and coefficient identification are checked from the algebra/quotient definition. This is an induction on i with a stated base, not a circular citation of the item. The polynomial and graded definitions supply the no-variable and zero-ideal endpoint checks.

All steps are marked elementary because each is an explicit short coefficient, quotient-representative, or finite-degree argument from the displayed hypothesis, the cited definitions, the associated-graded multiplication theorem, and preceding steps. The source cites no additional non-elementary lemma. In particular there is no hidden Krull intersection, flatness, regularity, exact tensor or general filtered-quotient theorem. Every step is shorter than 2000 characters; no long step conceals a comparison lemma. The generic tool citation is declared, proof_deps is exactly the union of uses, and no edge points to the parent or any descendant of the item.

Small cases checked against the actual proof: b=0 gives A=A in degree zero; i=0 is the hypothesis; i=b gives C with all positive degrees zero. The zero ring has zero polynomial and graded rings and all coefficient arguments still hold. For A=k[x,y] with (x,y) and i=1, the calculation gives gr_(y)(k[y])=k[T_y]. Over C=Z/4 the coefficient shift remains injective although C has zero divisors. If J=A (for example f_1=1), C=0 and every graded piece is zero, so both sides are zero. The non-quasi-regular example A=k[ε]/(ε²), f_1=ε fails the hypothesis in degree two, as required; the proof never purports to fix that failure. These checks cover B–E's hypothesis, object, and empty-case pitfalls. There are no new statements needing an independent small-case audit, and the item was not weakened or moved to another node.

## Unfinished work

None in this one-level split. No delivery push was made; the second reader is to inspect and deliver the accepted sandbox.

## Second reading by Q20

The special recovery condition is false for this item: its stage-1 item JSON exists, and the named stage-2 packet directory does not exist. I therefore independently read the stage-1 packet, preserving the original report and its `## Review by Q20`. No Lean was written or compiled, no agent was started, and no shared repository file was changed.

Statement: PASS against Stacks Algebra 061R (`lemma-truncate-quasi-regular`), 061P (`definition-quasi-regular-sequence`), and 061N (`equation-quasi-regular`), algebra.tex:16855–16893 and 17026–17057. Specializing M=R turns the source's polynomial-module map into the stated canonical polynomial-algebra map, with the same degree-zero coefficient ring and multiplication. The arbitrary commutative ring, arbitrary finite sequence, canonical-map hypothesis, every prefix 0≤i≤b, coefficient identification, and canonical graded-algebra conclusion match. No properness, Noetherian, locality, separatedness, or nonzerodivisor hypothesis is needed or added. The statement is unchanged.

- Step 1: PASS against 061R's quotient ideal and `def-weil-pbc-algebra-hom-quotient`: surjectivity and the quotient kernel give B/K=C; images of finite sums of generator products give the equality of ideal powers, also at n=0.
- Step 2: PASS against the monomial coefficient description in `def-weil-pbc-mv-polynomial-ring`, the components in `def-weil-pbc-associated-graded-ring`, and clauses (1)–(2) of `lem-weil-pbc-associated-graded-ring-structure`. Exponent shift is injective over every coefficient ring; its image is the actual class of ty, without cancelling t in A.
- Step 3: PASS against 061R's intersection assertion, the ideal-power definition, and Step 2. The least failed level is in a finite nonempty set and its predecessor exists since J^0=A; n≥m+1 gives the contradiction. The n=1 case is separate. This supplies precisely the argument compressed into the source's last sentence, without an infinite-order valuation assumption.
- Step 4: PASS against the quotient kernel, the graded direct-sum definition, and clauses (1)–(3) of the structure theorem. Every kernel class has a lift z in J^(n+1), so x−z is in both J^n and tA; the reverse direction follows by applying q. The scalar map is the specified identity of C.
- Step 5: PASS against Step 3 and the structure theorem's homogeneous product: the kernel is [t]_1 G_(n−1); applying the graded inverse of Φ identifies it with multiplication by T_1 in degree n. The degree-zero kernel is zero.
- Step 6: PASS against the polynomial node's unique finite coefficient expansion. Splitting by first exponent gives surjectivity, and the disjoint exponent supports give injectivity. Neither flatness nor a polynomial quotient theorem is concealed here.
- Step 7: PASS against the polynomial universal property's existence and uniqueness and the graded definition's finite support. The map fixes C and sends precisely the remaining generators to their initial forms; degreewise bijectivity assembles to a bijective graded algebra map, and the inverse preserves the operations by the displayed calculation.
- Step 8: PASS after making the associated-graded identification explicit. The induction invariant is the canonical polynomial isomorphism for B_i; the base is the hypothesis. The quotient isomorphism u carries the remaining ideal and each power onto the specified ones, so [x]_n↦[u(x)]_n and the inverse induced by u^(-1) identify the graded rings with their coefficient actions. Uniqueness on polynomial generators identifies the induction conclusion with the stated canonical map. The endpoint and b=0 arguments are valid.
- New nodes: none. There is no elementary helper, duplicate, Mathlib assertion, or restatement of an item clause to remove; B1–B7 impose no new-node work. The existing four dependency statements were opened and checked directly, rather than borrowing their proofs. All 16 step/citation pairs have verbatim statement quotations, checked independently against the shared files, and the union of `uses` is exactly `proof_deps`.

Independent edge checks: b=0 and i=0 are the original map; i=b leaves the zero ideal in C, with C in degree zero and zero in positive degrees. At b=1 the quotient is exactly C. The zero ring and J=A give zero coefficient rings and zero graded components, so the finite-degree and coefficient arguments still work. The example A=k[x,y], (f_1,f_2)=(x,y), i=1 gives gr_(y)(k[y])=k[T_2]. Replacing k by Z/4 tests the exponent-shift argument with zero divisors. A=k[ε]/(ε²), f_1=ε fails the assumed polynomial isomorphism in degree two and is correctly excluded. No field, domain, characteristic, or nonzero-ring assumption was used.

Independent reuse checks: searched the DAG for 061R, `truncate-quasi-regular`, and prefix-quotient terminology, and searched the source checkout and upstream name index for the item, quasi-regular terms, and 061R. There was no completed declaration for this item. Fresh prescribed msearch queries used the filtration/intersection formulation (LeanFinder), `"IsWeaklyRegular", "mod"` (Loogle), and `quasiregular|QuasiRegular|associatedGraded|associated_graded` (grep). All three succeeded; their actual output digests remain in searches.jsonl and were appended to the item's search records. I read RegularSequence.lean:135–147,228–258 and Filtration.lean:389–391: the former assumes successive injectivity, and the latter is Artin–Rees with Noetherian and finite-module hypotheses and an existential filtration offset. Neither states this result. The grep hits concern quasiregular elements in quasispectrum, a different notion. No new Mathlib leaf is justified.

Route and changes: read the unit and chapter records and the current main-20261015 divisor-class statement and proof (under sk-prop-an), confirming the recorded opening frame-class ancestry. The inherited unit metadata was preserved. The existing structure theorem now has `lean_audit.slopmaster2.state = closed`, so it is already an admissible tool under stages/1-dag.md §6; I removed the worker-added `split_report.tool_uses` entry, which was unnecessary and contrary to delivery-errors C8's maintainer-ownership rule. In Step 8 I expanded the induced map on each ideal-power quotient and checked the canonical-map equality. I added the independent search evidence and this reading. The statement and all 16 quotations remain unchanged. Backups of the pre-reading node and report are retained as .bak files.
