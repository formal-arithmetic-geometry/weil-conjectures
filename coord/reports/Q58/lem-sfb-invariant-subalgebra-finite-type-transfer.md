# Stage-1 report: lem-sfb-invariant-subalgebra-finite-type-transfer

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-invariant-subalgebra-finite-type-transfer.json — statement, split into seven proof steps; not a Mathlib leaf as a whole.
- citations.json — five verbatim statement excerpts for all five step/node citation pairs.
- report.md — this report. searches.jsonl is the unmodified output log of the prescribed search command; write_split.py is sandbox-only preparation code.

New nodes: 0. New Mathlib leaves: 0. All non-elementary ingredients already have nodes.

## Attachments

None. Searched the live lean/WeilConjectures library for the exact blueprint id, Artin–Tate and invariant/fixed-subalgebra finite-type concepts. No declaration there states every clause of the item. The Mathlib integrality and finite-dimensional fixed-field results are ingredients, not project attachment candidates.

## Wanted literature

None. All mathematical sources used are in literature/stacks-project/.

## Problems found and corrections

The item statement is unchanged; no statement dispute was found. Its proof was empty. In particular, finiteness over a general C must not be deduced by a Noetherian-submodule argument over C, since C need not be Noetherian. The proof instead passes to C'=u(C), establishes C'-finiteness of R by writing the coefficients, applies Artin–Tate to C' inside R, and only then uses Noetherian-submodule finiteness. Finally it lifts the finitely many coefficients from C' back to C. No injection of C into R is asserted.

The stored blueprint ancestry ends in null. The prescribed blueprint_refs.py ancestor command confirms None. I retained that inherited metadata and its precise from.place; I did not edit other workers' ancestry. Blueprint searches for invariant, Artin.Tate and invariant subalgebra, plus a source-text search of the current and older snapshots, found no blueprint statement of the full item. The named det-thm-sf-ctf-stability-direct-images proof is not a file in either available snapshot; its inherited route description and the reviewed parent's proof/report specify the algebra ingredient. The actual proof is marked agent-written and sourced to the available Stacks statements, not attributed to a nonexistent blueprint file.

## Not duplicates

No new nodes were created. Existing nodes reused: lem-dl-a1-finite-invariant-prime-orbits-residues (integrality clause), lem-per-artin-tate-subalgebra-finite-type (Artin–Tate), lem-wf-affine-noetherian-components (Noetherian ring clause), and lem-weil-pbc-noetherian-submodule-finite (finite submodules). They are all Mathlib leaves, so these generic tools do not replace a unit route. There are no new/existing same-tag pairs to compare.

## Review by Q58

I read the item, its chapter and unit records, the worker contract, the three blueprint levels, GOAL.md and delivery-errors B–E. The assigned algebra lemma stays below the alteration/quotient ingredient of the existing direct-image route. I read the source in algebra.tex: Tag 00IS, lemma-Artin-Tate (including its proof), Tag 00GM, lemma-characterize-integral (the bounded monomial proof), Tag 02JJ, lemma-characterize-finite-in-terms-of-integral, Tag 00FN, lemma-Noetherian-permanence, and Tag 00IK, lemma-Noetherian-basic. I also read more-algebra.tex Tag 0BRI, lemma-one-orbit, especially its initial orbit-polynomial integrality argument, and verified the tag/label mappings in tags/tags. There are no new-node sources to audit.

Step 1 uses exactly the integrality sentence of lem-dl-a1-finite-invariant-prime-orbits-residues, whose full statement I opened. It assumes a finite group acting on an arbitrary commutative ring, not a domain or tame action, and so applies to R. The hypothesis that the automorphisms are over e makes A an e-subalgebra. The node's unrelated prime and residue clauses are not used.

Step 2 is an elementary calculation from the monic equations obtained in Step 1, not an uncited assertion that integral finite-type maps are finite. Each leading power is replaced by smaller powers, producing the finite spanning family with bounded exponents. Every polynomial is a linear combination of these monomials. No Noetherian assumption enters. For an empty algebra-generator family the monomial is 1.

Step 3 uses the actual statement of lem-per-artin-tate-subalgebra-finite-type with base e, B=R and intermediate A. I checked all its hypotheses: e is Noetherian by the displayed two-ideal argument; R is finite type by hypothesis; A is an e-subalgebra by Step 1; R is A-finite by Step 2. Its conclusion is exactly the finite-type clause. I read fg_of_fg_of_fg in Mathlib/RingTheory/Adjoin/Tower.lean at line 145 to confirm the existing leaf's interpretation.

Step 4 proves reducedness directly by injectivity of A into R. No theorem about reducedness or invariants is hidden in it.

Step 5 proves the base change to the image by an explicit expression r=sum u(c_i)x_i. The map u being an e-algebra map, rather than merely a ring map, is essential: C' contains the image of e and is an e-subalgebra. This step neither assumes nor needs u to be injective.

Step 6 applies that same Artin–Tate statement with intermediate C', and all its hypotheses were already verified in Steps 3 and 5. I opened the full statement of lem-wf-affine-noetherian-components: its first ring clause explicitly says a finite-type algebra over a field is Noetherian. We instantiate its scheme X as Spec C'; none of its topological clauses is needed. Its Mathlib match Algebra.FiniteType.isNoetherianRing and the supporting Stacks 00FN require exactly the available hypotheses.

Step 7 uses the full statement of lem-weil-pbc-noetherian-submodule-finite. Here its base is C', its finite module is R, and its submodule is A, closed under C'-multiplication since C' is contained in A. Thus its conclusion is precisely finite generation of A over C'. The final lifting of finitely many coefficients from the image gives finite generation over C without adding a hypothesis. All five uses are covered by literal excerpts in citations.json; no citation is to a definition in place of a theorem or to another node's proof.

For the B–E audit, every object is introduced in the unchanged statement and its four statement dependencies supply the named notions. No new node is elementary, duplicate, a restatement of a clause, or a missed Mathlib match, because no new nodes were needed. Each step contains its argument and source place, proof_deps is exactly the union of uses, all citations are existing unmerged Mathlib leaves, and no step exceeds 2000 characters. The item has genuinely been proved by a sequence of arguments, not moved into a new node.

I checked small cases: R=e and the trivial or nonfaithful action; R the zero algebra (all modules are zero and the empty generator case is allowed); a nonreduced finite-type R (only the conditional reducedness clause is claimed); characteristic dividing |H| (no division or averaging occurs); C with an arbitrarily large kernel, e.g. C=e[x_i : i in an infinite index set] mapping all x_i to zero in R=e (C itself can fail to be Noetherian, but C'=e and the proof applies). Taking H trivial gives A=R and is consistent with both transfer conclusions. No field embedding into the zero ring was assumed: “contains e” in the proof always means contains its image.

Mathlib searches used only the prescribed msearch.py, with two semantic phrasings plus Loogle, grep and LeanSearch. I read the returned hits. Invariant integrality matches the existing node; FixedPoints finite dimensionality is for fields, and Galois.lean lines 128 and 149 concern residue/fraction fields under extra separability/maximality hypotheses. They cannot prove the full item. The second semantic phrasing returns general finite-type towers and coefficient-subalgebra constructions, which still require the explicit argument above. All new search records are copied from the actual searches.jsonl fields; the item's older Q22 search history is preserved.

## Unfinished work

None in the mathematical split. Server dry run and direct delivery follow this report; their final status is reported by the delivery command.
