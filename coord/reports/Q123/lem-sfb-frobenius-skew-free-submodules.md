# Stage-1 report: lem-sfb-frobenius-skew-free-submodules

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-frobenius-skew-free-submodules.json: statement, split; statement and statement dependencies unchanged, five proof steps, one new algebra prerequisite.
- dag/nodes/sec-six-functors-basics/lem-sfb-frobenius-skew-left-multiple-division.json: statement, unsplit; no Mathlib match, after LeanFinder, LeanSearch, valid Loogle name search and source grep, with two semantic phrasings.
- citations.json: one verbatim statement quotation per dependency cited in each of the item's proof steps.

There is one new node and no new Mathlib leaf. No Lean file, repository file, unit record or launcher script was written. The work/ directory contains only the sandbox preparation script.

## Attachments

None. Searches of lean/WeilConjectures by both node ids and by Frobenius/skew-polynomial terminology found no declaration stating either result. SemilinearFrobenius.lean:49 explicitly says its Lang-Steinberg proof avoids the skew-polynomial structure theorem; its surjectivity result is not this item. The item's current record has no Lean declaration or audit to follow.

## WANTED

WANTED: Berrick and Keating 2000, Theorem 3.2.10 and Lemma 3.3.5, for lem-sfb-frobenius-skew-free-submodules. Milne Proposition 14.50 refers to those arguments rather than supplying the proof. No such document is listed in literature/LIST.md. The coordinate induction in this delivery is supplied by the agent; proof_origin.by is therefore agent. Milne's actual division statement is available and was read, so the new prerequisite has an obtained source.

## Corrections and source audit

No statement dispute or correction is necessary. Milne, Algebraic Groups, printed p.296 (PDF p.308), asserts precisely division f=qg+r without assuming k perfect, followed by Proposition 14.50 on left ideals and free finite-rank ambient modules. The last paragraph of that page adds perfectness for f=gq+r. Calling the input "division by left multiples" makes the multiplication order explicit without reversing Milne's right/left division terminology. The existing two-sided division node requires sigma to be an automorphism, so it cannot be applied over an imperfect field.

I also read Theorem 16.58, printed p.345 (PDF p.357), which uses Proposition 14.50 on an ambient free module with a monomial basis. Finite generation of M in this item makes that use finite by taking the finite union of its generators' supports. The imported statement is thus valid exactly as written.

The latest blueprint's lem-sc-lang-steinberg.proof.md mentions a skew ring over an algebraically closed field but states a different conclusion. Searches via tools/blueprint_refs.py for skew, division, Euclidean, Frobenius, and free module, and a direct scan of latest/blueprint for skew-polynomial and 14.50 text found no standalone duplicate. The ancestor command returns None, as in the current item's blueprint.from.node. The delivery retains that inherited null ancestry and the existing full via chain; the new node adds this item to the chain and gives its precise supporting place. No unit-level route or statement is changed.

## Not duplicates

lem-sfb-frobenius-skew-left-multiple-division vs lem-sfb-skew-polynomial-two-sided-division: the existing node assumes a coefficient automorphism and proves both f=q_L g+r_L and f=gq_R+r_R; the new node assumes only an arbitrary characteristic-p field and proves f=qg+r. Frobenius on F_p(t) is not surjective, so the existing hypothesis is unavailable.

lem-sfb-frobenius-skew-left-multiple-division vs lem-sfb-left-principal-finite-submodules: the existing leaf assumes principality of left ideals in a general ring and proves finite generation of submodules; it proves no skew-polynomial division algorithm.

lem-sfb-frobenius-skew-left-multiple-division vs lem-sfb-perfect-skew-polynomial-cyclic-decomposition: that node assumes every element of k is a p-th power and concludes a decomposition of modules, not the arbitrary-field one-sided ring division algorithm.

lem-sfb-frobenius-skew-left-multiple-division vs lem-sc-lang-steinberg: the existing blueprint statement is surjectivity of F-1 on a finite-dimensional vector space over an algebraically closed field. A paragraph inside its proof mentions division, but its statement does not supply the new node's assertion.

lem-sfb-frobenius-skew-left-multiple-division vs lem-sfb-frobenius-skew-free-submodules: the new node is only an arithmetic remainder theorem in A, with no submodule or freeness conclusion. The item's proof still carries principality, finite-support reduction and the actual construction and independence of a finite basis.

The other search hits for ordinary polynomial division, monomial division and Tate-algebra division have different rings; the existing matrix-diagonalization node assumes two-sided division and asserts a matrix conclusion. Neither supplies this arbitrary-field input. No Stacks tag is shared: the substantive source here is Milne, not a Stacks theorem for commutative PIDs.

## Review by Q123

I read Milne pp.296-297 and p.345, and compared the five proof steps with the exact statements of all three cited nodes (including the new one). I checked delivery-errors B-E against the node files and those sources. The new node introduces its field, characteristic, ring operations, degree and all quantified variables; it is statement-only, has empty proof and proof_deps, and has genuinely run searches copied from searches.jsonl. I read every search's hits. In particular I opened Mathlib/LinearAlgebra/FreeModule/PID.lean at lines 98 and 280: Submodule.nonempty_basis_of_pid assumes CommRing, which the current ring need not satisfy. I read SkewPolynomial/Basic.lean's ring definition and the grep hits; its operations and coefficient lemmas are not division or freeness. Polynomial.div and the OreLocalization search results have different multiplication or different objects. One Loogle pattern containing div was invalid; its record says so, and I repeated it using the valid quoted SkewPolynomial name pattern. No unavailable service was treated as absence.

Step 1 uses precisely the generating-set assertion of def-weil-finitely-generated-module. I checked that scalar multiplication cannot enlarge the coordinate support and that restriction/extension by zero are inverse left-linear maps. The finite index set is the union of generator supports, not the union of all possible ambient supports. This is an elementary reduction, not another node.

Step 2 uses def-weil-field's inverses and nontriviality to show a product of nonzero leading coefficients is nonzero. The leading coefficient of ab is a_r b_s^(p^r), and no other pair of degrees contributes to degree r+s. Thus the no-zero-divisors conclusion used later is proved here, rather than silently assumed from a commutative-domain theorem.

Step 3 cites exactly the new node's f=qg+r statement. The hypotheses agree: k is an arbitrary characteristic-p field, g is nonzero, and the same multiplication is in use. Since q multiplies g on the left, the remainder belongs to the left ideal. Least nonzero degree then forces that remainder to vanish. The zero ideal is explicitly handled. This is the only non-elementary external input; its verbatim quotation is in citations.json.

Step 4 states the stronger inductive claim for EVERY submodule of A^n, supplies n=0, and invokes induction only for a submodule of A^(n-1). This prevents a hidden use of Noetherianity or finite generation of K. The first-coordinate image is a left ideal because the projection is left linear. Deleting its zero coordinate gives an actual linear bijection of K with the tail submodule. These are direct coordinate checks from the definitions, so no new projection/kernel lemma is needed.

Step 5 treats separately zero and nonzero projection image. In the latter case a lift x of the generator g exists by definition of image. The explicit subtraction y-ax proves spanning. Projecting a relation gives ag=0, and step 2 then gives a=0; independence in the kernel gives all remaining coefficients zero. The displayed map A^(e+1) to N is left linear by associativity, with coefficients acting on the left throughout. This proves the bijection and closes the induction, rather than citing an abstract free-submodule theorem. The step is elementary relative to the proved earlier steps and the induction hypothesis; it has no concealed standard theorem or comparison lemma.

For the new division statement I tested f=0, a nonzero constant divisor, degree f less than degree g, and a positive-degree divisor. The leading-term subtraction for f of degree n >= m=deg g is t=(a/b^(p^(n-m)))F^(n-m), where a and b are the nonzero leading coefficients of f and g. Then f-tg is zero or has smaller degree, so induction gives the asserted remainder. This verifies the new statement independently without requiring a p-th root or surjectivity of Frobenius; it remains a statement-only node, not recursively split here. Over F_p(t), dividing by left multiples of F causes no difficulty, whereas a general f=gq+r algorithm would need p-th roots of coefficients. I also checked the item when I is empty, M=0, I is infinite but the chosen generators have finite support, and n=1, where the proof gives an ideal freely generated by its nonzero least-degree generator. No statement weakening, new unproved freeness clause, cycle, off-unit citation, or SGA source occurs. Every step has fewer than 700 characters, so the long-step audit has no candidate.

## What remains

The sole new prerequisite is intentionally unsplit for the next stage-1 worker. Nothing else in the assigned item remains unfinished. Required server dry-run and push results are recorded below when available.
