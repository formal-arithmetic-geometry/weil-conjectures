# Q36: lem-trf-koszul-derived-quotient

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-koszul-derived-quotient.json`: statement split in five steps; Mathlib verdict no match. No new nodes, no Mathlib leaves.
- `citations.json`: one verbatim statement excerpt for each of the eleven step/node pairs.
- `searches.jsonl`: six actual msearch results, retained with their exact queries and result digests.

## Attachments

None. I searched the project source under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the exact blueprint tag and for Koszul and regular-sequence terminology. The project has Koszul sign conventions and the projective-line Koszul short exact sequence, but neither states this polynomial derived-quotient comparison for arbitrary finite Koszul-regular sequences. The upstream master source is reference material, not proof evidence. No Lean was written and no compiler or Lake command was run.

## Wanted literature

None. All mathematical sources used are available in `literature/stacks-project/`.

## Corrections and observations

The item was a correct unsplit supporting statement of the already-reviewed cotangent-quotient node. I retain its original statement and add only the explicit convention that the tensor is derived extension of scalars in D(R), computed by a K-flat resolution over P, together with the corresponding existing-node citation. This makes the coefficient category and the derived-tensor operation explicit; it adds no hypothesis and changes no conclusion.

The new proof expands the first paragraph of Stacks Tag 08SJ (cotangent.tex, lemma-mod-regular-sequence). Its sentence saying that Koszul-regularity exactly means the derived equality is now the outcome of a resolution computation and a canonical augmentation check, not a black-box restatement of the item. No definition, target, chapter, unit, or other worker's node was changed.

I read the chapter record sec-trace-formula, the unit record sk-i-curve-zero, and the current main-20261015 ancestor lem-trf-local-term-locality proof. The item's inherited ancestry records the semistable-alteration supporting branch. This split supplies only its existing commutative-algebra prerequisite; it substitutes no geometric route. Four off-unit generic tools are declared in split_report.tool_uses: regular sequences give Koszul acyclicity; bounded-above flat module complexes are K-flat; mixed derived tensor is computed by a K-flat resolution in D(R); Koszul complexes commute with scalar extension. The unit has no separate statement of any of these four algebraic tools.

## Not duplicates

There are no new nodes. Searches of the entire DAG and blueprint (blueprint_refs.py ancestor and searches for Koszul, derived tensor, and the item terminology) found the exact existing general tools used. In particular lem-sc-koszul-base-change-iso already gives scalar extension without flatness, and lem-weil-pbc-regular-sequence-koszul-regular already has the successive-injectivity hypothesis. I did not create nodes for polynomial-variable injectivity, finite-free flatness, H_0 as the quotient, or the augmentation: these are the explicitly written elementary parts of the proof. The whole-blueprint matches mentioning Koszul completion concern towers and reconstruction, not this finite polynomial augmentation; same_as remains empty.

## Review by Q36

I checked the delivery-errors B--E requirements with the item, the cited statements, and the Stacks source open. The item source is cotangent.tex Tag 08SJ (lemma-mod-regular-sequence), first proof paragraph. For the auxiliary statements I read more-algebra.tex Tags 0623 (definition-koszul-complex), 062E (definition-koszul-regular-sequence), 062F (lemma-regular-koszul-regular), the first identity in the proof of 062H (lemma-koszul-regular-flat-base-change), 064K (lemma-derived-tor-quasi-isomorphism), and the construction and lemma at 06Y6 (lemma-derived-base-change). No new-node source needs checking because no new node is introduced. No prohibited SGA source is used.

Step 1 is a coefficient argument: evaluating the first i variables at zero kills exactly the monomials divisible by those variables, and multiplying by the next variable shifts its exponent injectively. This proves the hypotheses used next, without citing an unstated polynomial-regularity lemma. It also identifies the final polynomial quotient with the integers.

Step 2 uses the actual statement of lem-weil-pbc-regular-sequence-koszul-regular, which assumes exactly the multiplication injectivity proved in step 1. Its M=P case gives positive Koszul homology vanishing. The statement of def-weil-pbc-koszul-complex supplies the finite free wedge bases, degree bound, K_0=P, and d_1(e_i)=x_i. That displayed d_1 makes H_0=P/J directly. The augmentation therefore is a quasi-isomorphism; def-weil-abstract-derived-category supplies the cochain and quasi-isomorphism conventions. This step does not assume that R is flat over P.

Step 3 uses the same finite free terms, whose flatness is checked by coordinatewise exactness of a finite direct sum, and the actual bounded-above module assertion lem-pc-module-bounded-flat-kflat. I checked that the bound is above in cochain degree (0), not below. Clause (2) of lem-pc-derived-tensor-second-factor-functor then applies with its base ring=P, algebra=R, E=Z[0], N=R[0], and F=K_P. Its statement gives the computation in D(R), for arbitrary P-algebra R, including the canonical model comparison. As a left-derived-functor comparison the derived-to-ordinary map is the resolution augmentation tensored with the identity. No replacement of R by a P-flat module and no identification with a different coefficient category is used.

Step 4 uses the full statement of lem-sc-koszul-base-change-iso, which explicitly needs no flatness or regularity. Its source 062H is phrased for flat maps only for preservation of regularity; the complex identification used here is the first identity of its proof, valid for every ring map. I checked the normalization on wedge bases using the differential formula in def-weil-pbc-koszul-complex: replacing x_i by f_i leaves all alternating signs the same. The ordinary tensor identification is proved using the mutually inverse formulas z tensor a maps to z times the class of a, and the class of a maps to 1 tensor a; the latter kills every f_i by P-balancing. Hence it is the specified canonical augmentation, not just an arbitrary isomorphism between the objects.

Step 5 uses precisely clause (3) of def-weil-pbc-koszul-regular-sequence for the sequence in R, not regularity of that sequence. The d_1 formula in the Koszul definition gives the degree-zero quotient, on which the augmentation acts identically. All other homology groups vanish by the hypothesis; the localization definition in def-weil-abstract-derived-category then inverts this augmentation. This is an elementary use of the definitions and the already-computed model, not a new lemma carrying the item's conclusion.

For B1--B10 there is no new statement-only node or Mathlib leaf to validate; the existing fields, source, and ancestry are retained. For C1--C8 I read every cited statement, checked all eleven quotes verbatim, computed proof_deps from the uses union, and declared each off-unit theorem as a tool. For D1--D5 the proof carries the actual resolution, base change, and cohomology argument, rather than applying a new node restating the item. For E1--E7 I checked the ring maps, the cochain sign/index convention, and the augmentation normalization explicitly. No elementary step invokes an uncited substantial theorem. Every step is shorter than 2000 characters.

Small cases: r=0 gives P=Z, K_P=Z[0], I=0 and the identity of R. For r=1 the derived model is [R --f_1--> R] and Koszul-regularity says exactly that f_1 has zero annihilator. The zero ring is permitted and gives zero complexes on both sides. A unit among the f_i is allowed whenever the stated Koszul-regularity holds; the augmentation then maps an acyclic Koszul complex to B=0, and no proper-ideal hypothesis has been inserted. As a negative test, R=Z and f_1=0 is excluded: H_1 of the displayed two-term complex is Z, so omitting Koszul-regularity would make the assertion false. R=Z/2 with f_1=1 is an admissible non-flat P-algebra test with B=0; the Koszul differential is the identity. These checks confirm that neither Noetherian nor nonzero/proper-ideal assumptions were accidentally used.

The six Mathlib search commands were actually run through msearch.py and their outputs read. Both LeanFinder phrasings returned naive cotangent and Kahler differential declarations, not this derived computation. Loogle's Koszul query returned no declarations. The RingTheory grep and then the whole-Mathlib grep found only the regular-sequence TODO at Regular/RegularSequence.lean:21, a local-cohomology TODO mention, and an unrelated differential-geometric Koszul connection. LeanSearch returned ordinary regularity, quotient and algebraic-independence declarations. These do not specialize in one line to the item. Original inherited search entries remain intact, and the six Q36 entries reproduce the exact logged query texts.

## Unfinished work

None in the requested one-level split. The existing supporting nodes remain under their current independent statuses. Server dry-run and delivery results are recorded below after they complete.
