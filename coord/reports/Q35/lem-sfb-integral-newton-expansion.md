## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-integral-newton-expansion.json: existing statement, now split with seven proof steps; no statement change.
- dag/nodes/sec-six-functors-basics/lem-sfb-integer-falling-factorial-divisibility.json: one new statement node, Mathlib leaf, factorial divisibility for arbitrary integer arguments.
- citations.json: a verbatim statement quote for every step citation.
- searches.jsonl: actual searches executed with the required msearch.py command. write_split.py is sandbox-only preparation material.

## Attachments

None. Searches of lean/WeilConjectures by blueprint id, Newton, binomial basis, binomial polynomial and falling factorial found no declaration giving the item. WeilConjectures/Mathlib/Algebra/Group/ForwardDiff.lean gives univariate facts, not this multivariate expansion and integrality criterion. No compiler or Lean build was run.

## WANTED

None. The Stacks source paragraph is present. Its assertion is univariate and does not supply the proof of the stronger multivariate statement; that argument is explicitly agent-written, rather than attributed to Stacks.

## Findings and corrections

The original item had no proof. Its statement is true, including the asymmetric integer-value hypotheses (nonnegative tuples suffice for integral coefficients, and integral coefficients give values at all integer tuples). No STATEMENT-DISPUTED correction was needed.

The latest blueprint (ef6f9619fdbffa59e88528fb56483d76c70258c8), its basic-six-functors chapter and ctf-stability unit, and the direct-images proof were read. This arithmetic item supports the already chosen Kostant integral PBW input deep below that unit; the six-functor route is not changed. The inherited provenance chain has blueprint.from.node = null, and blueprint_refs.py ancestor reports None. I retained the detailed inherited place and via chain and extended them for the arithmetic leaf rather than claiming a fictitious imported ancestor. Whole-blueprint searches for binomial, factorial, triangular, falling factorial and factorial divisibility found no equivalent statement.

The DAG already has lem-weil-pbc-triangular-change-of-basis. I reused its full statement in step 1 instead of creating another general triangular-basis result. It is declared in split_report.tool_uses as a generic tool outside this unit. The polynomial-ring definition gives finite coefficient representations and coefficient uniqueness, which directly exhibit the bounded monomial basis. No additional polynomial-basis theorem is used without citation.

Mathlib searches found Ring.descPochhammer_eq_factorial_smul_choose at Binomial.lean:390, with Int.instBinomialRing at line 259. The falling product is identified by descPochhammer_eval_eq_prod_range at Pochhammer.lean:458, and eval_eq_smeval at Algebra/Polynomial/Smeval.lean:69 identifies evaluation notations. These statements were opened and read. Together they give the new arithmetic leaf by taking the witness Ring.choose z n. In particular this is integer subtraction, and works when z is negative. The leaf is not falsely matched to the natural-number descending factorial with truncated subtraction.

## Not duplicates

lem-sfb-integer-falling-factorial-divisibility vs lem-sfb-integral-newton-expansion: the new leaf is the scalar arithmetic divisibility of one falling product at an arbitrary integer. It has no multivariate polynomial expansion, degree bound, uniqueness, forward-difference coefficient formula or integer-valued polynomial criterion. It is a Mathlib arithmetic input, not the item's conclusion moved into another node. These are the only two nodes whose source field contains Tag 00JX in the read repository.

Other related nodes were read: lem-sc-coordinate-differences-polynomial and lem-trf-rational-sequence-polynomial-forward-difference construct a polynomial from prescribed differences; lem-sfb-polynomial-difference-deformation-retract concerns internal condensed modules and a backward-difference contraction; lem-sfb-polynomial-rank-one-difference-model concerns l-adic translation representations; lem-sfb-banach-mahler-coordinates concerns continuous functions and Banach-valued infinite expansions. None states the arithmetic divisibility leaf or the finite rational multivariate item. The existing triangular node is used directly. Searches of the whole DAG for the exact arithmetic declaration, factorial divides and falling factorial found no duplicate leaf.

## Unfinished work

None in this one-level split. There are no new unsplit nodes. The only new node is a Mathlib leaf with no proof steps, no proof dependencies, no proof origin and a complete statement.

## Review by Q35

I read Stacks algebra.tex lines 13820–13839, Tag 00JX, definition-numerical-polynomial and the following paragraph. It asserts the motivating univariate integral binomial expansion but does not provide the multivariate argument. I therefore recorded the item's proof as agent-written. For the new node I read the integer binomial-ring instance and the factorial identity in Mathlib/RingTheory/Binomial.lean, the descending-Pochhammer product in RingTheory/Polynomial/Pochhammer.lean and the evaluation comparison in Algebra/Polynomial/Smeval.lean. No unavailable search was recorded as a negative result; all recorded queries actually ran.

In step 1 I checked the statements of def-weil-pbc-mv-polynomial-ring and lem-weil-pbc-triangular-change-of-basis. The former explicitly gives finite coefficient representations and unique coefficients. The latter applies to a finite free module over a commutative ring with triangular coordinate matrix and unit diagonal, in either orientation. Here the module is exactly the rational span of the finitely many monomials of degree at most D, ordered by total degree. Expansion of each product B_b has precisely one term of degree |b|, a nonzero rational multiple of X^b; every other monomial has smaller degree. Thus the required triangularity, finite indexing, and unit diagonal really hold, including D=0 and r=0. The statement quotes in citations.json contain precisely those assertions; the proof of the cited triangular node is not used.

Step 2 cites no theorem: I checked the factored identity F_j(X+1)-F_j(X)=jF_(j-1)(X), separating j=0 from j>=1 and dividing only by nonzero rational factorials. Factors in the other variables are constant with respect to this difference. In step 3 the commutation is the literal equality of coordinate substitutions; linearity and repeated use of step 2 give zero when a exceeds b in any coordinate, and B_(b-a)(0) otherwise. Evaluation then singles out b=a. This proves the coefficient formula rather than assuming it from an uncited Newton theorem. Step 4 is an induction on the finite number of differences; shifts never leave the nonnegative grid, so each subtraction preserves integral values. No density or polynomial-identity theorem is used.

Steps 5 and 6 use exactly the new factorial-divisibility statement, whose complete statement was quoted separately for each step. Casting its integer equality to Q and cancelling the nonzero factorial proves the integrality of each rational binomial value for every integer input. Products and finite integer sums prove the converse. For the affine substitution, every affine value is an integer even for negative parameters, and a product of t affine factors has no monomial above total degree t. Applying the expansion and coefficient argument already proved gives the final clause. It does not require that the affine coefficients be nonnegative.

I checked the small cases r=0, D=0, the zero polynomial, t=0, z=0, and negative z: n=0 gives the empty product 1, while z=-1 gives (-1)^n n!, consistent with the leaf. For P=X_1 X_2 the coefficient at (1,1) is 1 and the degree is 2; for P=X_1^2 the expansion is 2 B_(2)+B_(1), consistent with the formula. Step 7 explicitly treats the empty variable set as a singleton evaluation domain and an empty product basis. No non-elementary step is longer than 2000 characters. I checked sections B–E: the new node is self-contained and statement-only, its arithmetic notions are explicit, every non-elementary input is a cited statement, no hypothesis or clause was dropped, no cyclic dependency is introduced, and no clause of the item has been repackaged as an unsplit node.

The first dry run requested an explicit notion dependency in the arithmetic leaf. I made its falling-product polynomial F_n in Z[T] explicit and cited the existing definition def-weil-polynomial-ring, which I opened and checked. This is the same factorial-divisibility statement and the same Mathlib specialization, now with its polynomial notation bound. I updated both verbatim citations accordingly.
