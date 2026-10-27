# Worker report: lem-sfb-polynomial-field-ufd

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-polynomial-field-ufd.json: statement, Mathlib leaf. Confirmed `MvPolynomial.uniqueFactorizationMonoid` at Mathlib/RingTheory/Polynomial/UniqueFactorization.lean:130 and `MvPolynomial.instIsDomainOfIsCancelAdd` at Mathlib/Algebra/MvPolynomial/Basic.lean:204, with variables `Fin n` over the field `k`.
- citations.json: empty list, because a Mathlib leaf has no proof steps or proof-node citations.
- report.md: this report. searches.jsonl is the unmodified log produced by msearch.py.

New nodes: 0. Mathlib leaves delivered: 1 (the item itself). No Lean written, no compiler run.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag, polynomial factoriality/UFD terminology and the multivariate UFD declaration. The existing project uses of unique factorization do not state all clauses of this item as a project declaration. Mathlib declarations are recorded as leaf matches, not project attachments.

## Wanted literature

None.

## Corrections and scope

The statement and its two statement dependencies are unchanged. The source is correct: Stacks Tag 0BC1, algebra.tex, lemma-polynomial-ring-UFD, explicitly says that a polynomial ring over a UFD is a UFD, and in particular that k[x_1,...,x_n] is a UFD for a field k. The reviewer-added item supplied a strong candidate but left it unsplit. This delivery confirms that candidate rather than making an artificial split.

Read the chapter and recorded unit, SETUP.md's three levels, GOAL.md, and the current latest blueprint's sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability-direct-images.proof.md. The stored historical ancestor chain returns None from blueprint_refs.py ancestor. Its already-specific from.place and historical via are preserved. The current blueprint reduces (3) through proper base change and the open direct-image input; the algebra item is supporting material below that route, not a proposed replacement of a unit step. No unit record was changed.

Historical mathlib_searches from the live node are retained as inherited evidence, not claimed as searches run by me. Fresh searches with the exact item question are appended from the actual msearch.py log. All four services worked. The first file-only grep exposed only its first hits, so a directory grep then supplied the actual multivariate instance and line.

## Not duplicates

No new node was created. Whole-DAG searches for 0BC1 and MvPolynomial.uniqueFactorizationMonoid found the already-existing broader Mathlib leaf lem-per-polynomial-ufd-prime-quotient: it assumes a PID coefficient domain and additionally asserts prime quotients. A field is a PID, so it includes this item's UFD conclusion; this is acknowledged rather than creating another supporting node. The assigned item is already live and is independently certifiable directly by the two Mathlib instances; neither the existing broader node nor any other existing node is modified. Whole imported-blueprint searches for polynomial UFD, factorial, and unique factorization found no equivalent blueprint statement (the latter returned a categorical coextension node using the words in a different sense); direct latest-blueprint search likewise found no equivalent item. same_as remains [].

## Review by O1

I read Stacks algebra.tex at lemma-polynomial-ring-UFD (Tag 0BC1), both its statement and its proof. For this leaf, the authoritative local Mathlib source was then read at each declaration named in mathlib_match. The instance at UniqueFactorization.lean:130 takes an arbitrary variable type and a commutative coefficient ring with unique factorization. With sigma = Fin n and D = k it has exactly the desired ring. Field.toEuclideanDomain (Field.lean:25), EuclideanDomain.to_principal_ideal_domain (PrincipalIdealDomain.lean:287), and PrincipalIdealRing.to_uniqueFactorizationMonoid (same file:371) discharge its inferred coefficient hypotheses. I checked the source context for the latter, including its domain and PID assumptions.

The UFD class alone does not assert a nonzero ring, so I separately checked the IsDomain instance at Algebra/MvPolynomial/Basic.lean:204. It requires cancellative addition and an integral domain in the coefficients, both supplied by a field. This covers the nonzero, commutative, no-zero-divisors clause without adding a hypothesis. In Defs.lean:133-137 Mathlib explicitly identifies the combination of IsDomain and UniqueFactorizationMonoid as a UFD. I also read UniqueFactorizationMonoid.exists_prime_factors (Defs.lean:152-155) and prime_factors_unique (Basic.lean:73-98): the first supplies prime factors up to a unit, and the second matches their multisets up to associates. A nonunit cannot have the empty multiset of factors; absorbing the overall unit into one factor preserves primality. Thus the wording about prime products and uniqueness agrees with the standard class, rather than silently changing irreducibles into primes.

There are no proof steps and no newly created nodes, so C1 and C4 require no quoted proof-node citations; citations.json is empty. I opened both statement dependencies: def-weil-field defines a nonzero commutative field, and def-weil-pbc-mv-polynomial-ring defines precisely the finite-support polynomial algebra used here. No definition is used as evidence for a theorem. B's standalone-node and source requirements are met by the unchanged complete statement and the verified file/line match. D's relabelling and circular-split failures do not arise because the item is a genuine Mathlib leaf and no nodes are introduced. No long proof step is hidden.

For E, I checked n=0: MvPolynomial (Fin 0) k is the coefficient field and every nonzero element is a unit, so the nonunit clause is vacuous. For n=1 the usual polynomial UFD applies; n=2 gives k[x,y], a UFD without any claim that the polynomial ring itself is a PID. Finite fields, including F_2, satisfy all hypotheses; no characteristic or infinitude assumption is used. The zero ring is excluded by the definition of a field. No source or statement dispute was found, and no SGA source is used.

The first server dry run exited without pushing and requested a nonempty proof_origin record even for a Mathlib leaf. I supplied the unchanged Stacks source and its tag; no mathematical content or proof step changed.

## Unfinished work

None in this stage-1 item; independent maintainer review remains part of delivery acceptance.
