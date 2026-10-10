# lem-weil-pbc-nonzerodivisor-if-maximal-not-associated

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-nonzerodivisor-if-maximal-not-associated.json`: split into three steps following Stacks 00LL for the maximal ideal.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-noetherian-module-zerodivisors-union-associated-primes.json`: new unsplit statement for Stacks 00LD; Mathlib has a union theorem and a separate theorem equating its radical-based associated-prime notion with the statement's annihilator notion.

## Attachments

None.

## Wanted

None. The Stacks source was read from the local source clone; the project citation path `literature/stacks-project/algebra.tex` is absent in this machine's worktree but is the same source file.

## Findings

The original node had no proof. Stacks 00LL uses finite associated primes (00LC), prime avoidance (00DS), and zero divisors as the union of associated primes (00LD). Existing DAG leaves state the first two. The existing 00LD leaf states the ring-only case, so the new node states the module case actually used here. Mathlib's union theorem is at lines 227-228 in the project's pinned checkout; its radical-based associated-prime notion agrees with the statement's annihilator notion by a separate theorem at lines 114-116. Under B8 this is an unsplit node with both declarations recorded as candidates. The empty associated-prime case is handled by choosing zero, which is regular only because the module is then zero.

## Unfinished

The new 00LD module node remains unsplit for its own Stage 1 item. The present item is split. No Lean was written or built. `review_split.py` passes. `check_dag.py` reports zero cycles and seven unrelated existing reachability warnings, with none involving this item or its new node.

## Review by F1

I read Stacks Algebra 00LL (lemma-ideal-nonzerodivisor), its cited 00LC and 00DS lemmas, and 00LD (lemma-ass-zero-divisors), and compared the public statements of the existing finite-associated-primes and prime-avoidance nodes. The item is precisely the 00LL implication from absence of the maximal ideal in Ass(M) to an element of that ideal regular on M. The new 00LD node states the module version of the zero-divisor union, introduces its ring, module and prime-annihilator convention, and is strictly smaller than the item. Its source tag and label, definition citation, three search types and statement-only unsplit state satisfy B1-B7; I searched the DAG for the module version and found only the existing ring case (C5, D1-D2).

Step 1 uses the finite-associated-primes node under the Noetherian and finite-module hypotheses and observes that every proper prime lies in the unique maximal ideal. Step 2 uses the cited finite prime-avoidance statement with J=m; its explicit nonempty-list hypothesis is why the empty set is handled separately. Step 3 uses exactly the new 00LD statement to turn avoidance into injectivity of multiplication. If Ass(M) is empty, 00LD says even zero is regular, forcing M=0; the edge case is legitimate (C1-C4, E1-E6). No proof of a cited node is imported or route changed.

I sent B6 back because the worker's initial Mathlib line numbers were wrong; pinned v4.33.1 places the union theorem at line 227 and isAssociatedPrime_iff at line 114. I then sent B8 back because that second theorem is needed to reconcile Mathlib's radical-based notion with the node's annihilator convention. The worker corrected the lines and changed the helper to an unsplit candidate. I verified both declarations in the pinned source, reran the split review, and found no new DAG cycle. The seven reachability warnings are unrelated (A, F).
