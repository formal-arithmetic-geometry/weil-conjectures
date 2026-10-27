# Q17 stage-1 delivery: lem-sfb-associative-jacobson-identities

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-associative-jacobson-identities.json`: existing statement, now split into six complete steps; statement and `stmt_deps` unchanged. All inherited searches, source and provenance retained.
- `dag/nodes/sec-six-functors-basics/lem-sfb-commuting-binomial-expansion.json`: new statement, Mathlib leaf. `Commute.add_pow`, `Mathlib/Data/Nat/Choose/Sum.lean:34`, specializes from semirings to associative unital algebras in one line. No proof or proof dependencies.
- `citations.json`: full verbatim statement quotes for both citations (steps 1 and 2).
- `searches.jsonl`: actual msearch output records, retained by the search command. `math_check.py` and `write_split.py` are sandbox-only working files.

One new node, one Mathlib leaf. No Lean files written or compiled. No repository or launcher file modified and no manual git command used.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact item tag, Jacobson identities/formulas, restricted Lie terminology and iterated commutators, and read the relevant Lie/representation search results. No project declaration states both clauses. `LieAlgebra.ad_pow_lie` is Mathlib's iterated Leibniz rule on a bracket; it is neither the first clause nor the second. The Jacobson–Noether results require a division ring with algebraicity assumptions and have a different conclusion.

## WANTED

None. The needed source is present: `literature/milne-algebraic-groups_iAG2017.pdf`, §10k, Proposition 10.38, printed pp.205–206 (PDF pp.217–218). Read the preceding definition and examples and the whole proof, including its left/right multiplication calculation, permutation identity (71), binomial congruence and word-counting conclusion. No SGA source is used. This is not a Stacks result, so the new source is Milne with the exact proposition/page rather than an invented Stacks tag.

## Corrections and scope

The live item was unsplit with empty proof; the sandbox initially had no node or report, and no repair note exists. No statement correction or dispute is needed. The inherited source expresses the sum terms as iterated-adjoint word sums. The item uses the coefficient convention for ad(ta+b)^(p-1)(a). The proof verifies that exact convention directly; it does not cite the source's differently indexed word definition as an unexplained identification. Part (a) follows Milne's operator proof. Part (b) uses an agent-supplied finite-polynomial derivative and coefficient calculation in place of the source's permutation counting, so `proof_origin.by` is `agent`.

Read the chapter and unit records, the current blueprint unit section and `sk-thm-sf-ctf-stability-direct-images.proof.md` in `literature/blueprint/latest/`. This algebra input supports the inherited restricted-enveloping/differentiation chain below direct-image proof (3) and does not replace a unit step. `tools/blueprint_refs.py ancestor` returns None: the existing ancestry chain is broken upstream. I retained the item's null `from.node`, retained its precise long `from.place`, and gave the new node the same computed null ancestor with this item prepended to `via`. `same_as` is empty after whole-blueprint searches for Jacobson, commutator, binomial, binomial expansion, binomial theorem and commuting elements.

No unfinished work in the mathematical split. The first dry run required a notion citation in the new leaf. I stated it for associative unital algebras over a field (the exact application here) rather than bare rings, added def-weil-field, and defined the algebra structure explicitly. The general Mathlib theorem still specializes directly. citations.json was regenerated for the revised statement. The preliminary server review_split passed; the full dry run is repeated after this repair.

## Not duplicates

lem-sfb-commuting-binomial-expansion vs lem-pur-commutative-ring-binomial-expansion: the existing statement requires the entire ring to be commutative; this new statement requires only that the two selected elements commute in an arbitrary associative unital F-algebra. The proof needs the noncommutative ring End_F(B), so the existing statement does not apply.

lem-sfb-commuting-binomial-expansion vs lem-sfb-associative-jacobson-identities: the new leaf is the ordinary binomial theorem for a commuting pair, over any field and at any exponent; the item proves identities for arbitrary noncommuting elements in prime characteristic. The item contains the coefficient argument; the leaf does not restate either clause.

lem-sfb-commuting-binomial-expansion vs lem-sfb-formal-class-two-exponential: that node concerns formal exponentials in characteristic zero with central brackets, not powers of a commuting pair in arbitrary rings.

lem-sfb-commuting-binomial-expansion vs lem-sfb-unipotent-exponential-construction: that node constructs exponentials for unipotent group schemes in characteristic zero; its commuting-exponential clause is not a finite binomial expansion.

lem-sfb-commuting-binomial-expansion vs lem-sfb-integral-newton-expansion: the latter expands rational polynomials in a binomial-polynomial basis and characterizes integer-valuedness; it is not an identity of powers in associative rings.

lem-sfb-commuting-binomial-expansion vs lem-sfb-integer-falling-factorial-divisibility: the latter states a divisibility property of integer falling factorials, not an algebra-valued binomial theorem.

No existing node sharing a Stacks source tag is relevant: this leaf's source is Milne rather than Stacks. DAG searches by statement words and `Commute.add_pow`, and project-source/whole-blueprint searches, found no general ring version. The nearby existing scalar divisibility leaf was read: it is unnecessary because the scalar factorial recurrences are proved in step 1.

## Review by Q17

I read delivery-errors B–E in full and reviewed the six proof steps against the source and the actual statements of every cited node. I also read the source statement of `Commute.add_pow` at lines 28–36 and its proof through line 65. The new leaf has its own four actual searches: LeanFinder, Loogle, LeanSearch and grep. Grep over `Data/Nat/Choose` gave the full file and line 34; the earlier single-file grep printed the filename incorrectly as a line number, so the node uses the subsequent directory grep and the verified source line. The full item has two semantic phrasings plus Loogle/grep, and keeps all inherited searches. Results requiring commuting inputs are not recorded as matches for the item.

Step 1 uses only `def-weil-field`, whose statement says every nonzero field element has an inverse. Characteristic p is an item hypothesis, so 1,...,p−1 are nonzero. The two integer factorial recurrences are written explicitly, and give the vanishing p-row and signed (p−1)-row by cancellation and induction. The p=2 sign is handled separately. This also makes the item’s definition of each s_i unique and well defined. There is no uncited divisibility theorem hiding in this step.

Step 2 uses only `lem-sfb-commuting-binomial-expansion`, whose statement gives the entire displayed binomial sum under exactly xy=yx in an associative unital F-algebra. I checked these hypotheses for L_z and −R_z in End_F(B): their commutation is explicitly evaluated on c, and their powers are identified by the stated induction. Symmetry of binomial coefficients is the displayed factorial definition with factors interchanged. End_F(B) is an associative unital F-algebra under scalar multiplication and composition and need not be commutative, which is why the old commutative-ring leaf does not suffice. This is the sole non-elementary cited theorem. The whole proof of that theorem is already in Mathlib.

Step 3 substitutes n=p into step 2, applies the scalar vanishing from step 1, and checks both endpoints and equality on each input. It uses earlier proved steps and introduces no further lemma. It proves the first clause directly rather than citing a newly renamed version of that clause.

Step 4 substitutes n=p−1 into the same expansion in B=A[t]. A[t] has a central indeterminate even when A is noncommutative. The two signs multiply to 1, producing precisely the ordered insertion sum, with a in the middle. No order of noncommuting factors is exchanged. Its only inputs are the earlier formulas, already proved for an arbitrary B.

Step 5 defines D on finite coefficient lists and proves the noncommutative product rule by comparing the coefficient weighted by r+s; the coefficient product u_r v_s stays in that order. It then supplies the base and induction step for the derivative of z^n. This is an elementary finite-sum calculation, not a citation of commutative-polynomial differentiation for a noncommutative coefficient algebra. It does not assume that derivation-zero means constant in characteristic p.

Step 6 removes both the constant and leading terms before comparing derivatives. Distributivity makes Q supported in degrees 1,...,p−1, so multiplication by i is invertible in every coefficient that must be recovered. Coefficient comparison gives q_i=s_i exactly in the item's convention. Evaluation at 1 is justified by finite Cauchy multiplication; there is no use of infinitely many field values or any infinite-field assumption. Both clauses retain the full hypotheses of the item, including infinite-dimensional and noncommutative algebras.

The field definition and the binomial theorem are quoted verbatim in `citations.json`; they say exactly what these steps take from them (C4). All other arguments are written finite-sum, factorial, associativity or coefficient calculations, so no non-elementary input is unrecorded (C1). No new unsplit statement contains a proof sketch, no new node repeats a clause of the item, and no proof step exceeds 2000 characters (lengths 723, 660, 330, 446, 582, 842). No off-unit proof tool or new cycle is introduced: the sole new proof leaf has no proof dependencies and only the existing Mathlib field definition as a statement dependency.

Edge cases: p=2 gives s_1=[b,a]=[a,b] and the usual square expansion in characteristic 2. For p=3 the coefficient calculation gives s_1=[[a,b],b] and 2s_2=[[a,b],a], agreeing with Milne's displayed examples. For commuting a,b the iterated adjoint on a is zero, so the formula reduces to the commuting pth-power identity. Zero algebras, a=0 and b=0 are allowed; no cancellation in A or nontriviality of End_F(A) was used. The new leaf permits n=0 (both sides 1), the zero algebra and arbitrary field characteristic. Its restriction is commutation of x,y, not commutation of the full ring.

Independent finite computations in sandbox-only `math_check.py` passed 7017 matrix-pair Jacobson tests: every pair of 2×2 matrices over F2 and F3, plus 100 sampled pairs each over F5 and F7. The adjoint identity was checked for every a over F2 and F3 on all four matrix units. The new binomial leaf was checked for n=0,...,6 for every 2×2 matrix x with y=x+1 over Z/mZ, m=2,3,4,5, including composite characteristic and noncommutative ambient rings. These support the edge-case review; the six written steps supply the general proof.

The new leaf also cites `def-weil-field` in its own statement; its field hypothesis matches End_F(B). The composite-characteristic computations test the more general Mathlib theorem rather than imposing a composite characteristic on this field-algebra leaf.
