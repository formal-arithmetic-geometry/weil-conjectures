# Worker report: lem-weil-similitude-pairing-reciprocity

## Files written

- `dag/nodes/sec-zeta-weil/lem-weil-similitude-pairing-reciprocity.json`: statement, eleven proof steps, exact dependency union, blueprint search result, provenance, searches, split report; status split.
- `citations.json`: seventeen entries, each copying the cited statement verbatim.
- `report.md`, `searches.jsonl`: report and actual logged Mathlib searches. `write_split.py` is a sandbox-only generation aid.

## New nodes

None. No new Mathlib leaves. In particular, determinant multiplicativity was found in the existing, more general Cauchy–Binet statement, and the scalar, transpose and coefficient-map formulas have short explicit proofs from the existing Leibniz definition. No clause of the item has been moved into a new node.

## Attachments

No exact attachment for the whole item. I searched WeilConjectures for the exact blueprint tag and the similitude/reciprocity notions, then read `WeilConjectures/ZetaLinearAlgebra/Pairing.lean` and its imported characteristic-polynomial interface. The source has substantial sorry-free component declarations: `LinearMap.injective_of_similitude` (111), `LinearMap.isUnit_det_of_similitude` (131), its right counterpart (139), `LinearMap.conj_toPerfPair_eq_smul_inverse_dualMap_of_similitude` (171), `LinearMap.det_mul_det_of_similitude` (194), `LinearMap.C_det_mul_charpolyRev_of_similitude` (204), `LinearMap.roots_map_charpolyRev_of_similitude` (220), `LinearMap.roots_map_charpoly_of_similitude` (255), and `LinearMap.natDegree_map_charpolyRev_of_similitude` (275). These are useful evidence for the algebra, but no project declaration states all the item's clauses under precisely the stated hypotheses; for instance the separate dimension equality is Mathlib's `Module.finrank_of_isPerfPair`, and the arbitrary-embedding factorization needs the reciprocal-factorization argument. I therefore did not claim a partial attachment. The old node's source line numbers are stale relative to this checkout; I retained its provenance rather than treating those numbers as verification.

## WANTED

None. I used the locally available sources; the expanded proof is marked agent-written because neither Milne nor the blueprint supplies these coordinate and polynomial details verbatim.

## Statement and blueprint audit

The statement is unchanged and true. Read: the chapter record `sec-zeta-weil`, unit record `sk-prop-reciprocity`, the current main-20261015 unit statement and `prop-duality-reciprocity.proof.md`, and Milne's locally held *Lectures on Etale Cohomology*, II §27, Remark 27.4(a), p.155 and proof of Theorem 27.12, p.158 (PDF pages 155–159). Milne compares adjoints and uses the inverse Frobenius; the blueprint's step 1 describes the transported dual operator, and step 2 takes its determinant. This split proves exactly that abstract algebra with c in place of q^d. The rank-one twist trivialization in the ancestor's step 4 explains the scalar-valued pairing but is not a hypothesis needed beyond the present statement. No source dispute or unit-route replacement was necessary.

Searches of the whole DAG and `tools/blueprint_refs.py search` for similitude, perfect pairing, determinant, det_mul and Cauchy found no blueprint node equivalent to this abstract statement. The cohomological statements `prop-poincare-pairing` and `cor-pod-reciprocal-eigenvalues` impose geometric/coefficient data and are not generic linear algebra tools for this item. The more specialized `lem-weil-perfect-pairing-line-equivariance` assumes a line and identity first operator and does not give reciprocity. Thus `blueprint.same_as=[]`. The original ancestor, place and via data are preserved. This is not the unit's key node, so its realized fields are not changed.

## Not duplicates

No new nodes were created. `def-weil-pbc-matrix-determinant` already gives exactly the permutation formula, including the empty matrix. `lem-weil-pbc-cauchy-binet` already gives the general product formula; using m=n leaves a single subset. Both were opened before deciding against a new determinant node.

## Review by Q144

I read the statement of every cited node, not its proof as an implicit interface. The source for the determinant definition is its explicit Leibniz formula; I also read Mathlib's `Matrix.det_apply` (Determinant/Basic.lean:63), `det_mul` (138), `det_transpose` (203), `det_smul` (272) and `RingHom.map_det` (318). For Cauchy–Binet I read Stacks `algebra.tex`, label `item-cauchy-binet`, Tag 0F0K, lines 282–288. Its arbitrary commutative-ring hypothesis applies both to K and to K[T]. No SGA source is used.

Steps 1–2 use `def-weil-finite-dimensional-subspace` (finite spanning family) and `def-weil-vector-space-dimension` (basis cardinality). The greedy finite-basis argument and the coordinate functionals are written out. The induced map J is the map the hypothesis makes bijective; preimages of the coordinate functionals give actual vectors w_j. Evaluating proves independence and spanning, so the dimension assertion does not hide a dual-dimension theorem. The construction is valid for the zero space.

Step 3 uses only the statement of `def-weil-pbc-matrix-determinant`: the signed sum over permutations. I checked the transpose indices, the inverse-permutation sign, the factor s^m in scalar multiplication, the identity term, and that ring homomorphisms preserve the finite formula. These are explicit short computations, not unproved appeals to determinant laws. They work over arbitrary commutative rings and include size zero.

Step 4 uses the statement of `lem-weil-pbc-cauchy-binet`, specialized to two square matrices: exactly one full-size subset occurs. Pairing the actual basis vectors gives A^t B=cI, with the correct transpose placement. The matrix determinant is the endomorphism determinant by `def-weil-endomorphism-determinant`; that same node explicitly states invertibility iff the determinant is nonzero. The nonzero multiplier makes the product c^n nonzero over a field. Step 5 uses that precise invertibility criterion and substitutes F^{-1}v in the original pairing equation to identify the specified J-conjugate of G. No semisimplicity, eigenbasis or algebraic closure is assumed.

Step 6 uses the permutation formula and `def-weil-reverse-characteristic-polynomial`, whose statement is det(I-TA) and includes the reversed characteristic polynomial identity. Each product has n factors; taking its n linear coefficients gives (-1)^n det A, and evaluation at zero gives 1. The preceding nonzero determinants justify full degree. I checked that degree is zero, not minus infinity, when n=0 because the polynomial is 1.

Step 7 again uses Cauchy–Binet's square case over K[T], not merely over the field. A^t(I-TB)=A^t-cTI and the step-3 identities give det A P_G=(-1)^n chi_F(cT). Transposition fixes the scalar matrix. In particular the sign is correct: the argument does not incorrectly substitute reciprocal roots for ordinary roots.

Step 8 uses exactly the degree and coefficient formulas of `lem-weil-coefficientwise-extension-degree`. Injectivity of iota is proved using xx^{-1}; hence the nonzero determinants and c stay nonzero. The coefficient calculation explicitly checks that substituting cT commutes with iota. Step 9 uses clauses 2 and 3 of `lem-weil-reciprocal-root-factorization`: existence of nonzero alpha_r, uniqueness up to reordering and their multiplicities. Its hypothesis P_F(0)=1 and its degree n were proved in step 6; the target field is algebraically closed as required.

Step 10 uses the reverse identity in `def-weil-reverse-characteristic-polynomial`. The Laurent expression U^n P(U^{-1}) is an actual polynomial; its coefficients give the polynomial identity without an evaluation at zero of U^{-1}. The top coefficient in step 6 identifies product alpha_r with iota(det F), so cancellation is by a nonzero scalar, not by a possibly zero polynomial. This proves the factorization in L[T] itself. Step 11 uses the multiplicity/uniqueness clause of `lem-weil-reciprocal-root-factorization` and the same reverse identity for G. Thus the maps on ordinary roots, reciprocal roots and characteristic roots are distinguished and carry all repetitions. `def-weil-root-multiplicity` gives the multiplicity convention. The last eigenvalue wording uses algebraic multiplicity, i.e. roots of the characteristic polynomial, not dimensions of eigenspaces.

I checked every citation quote against the delivered or current repository statement; `citations.json` stores the whole statement so no rephrasing passes as a quotation. The proof-dependency list is the exact union of uses. All eleven steps are below 2000 characters, and I separately checked that no routine step conceals a new non-elementary lemma. Determinant multiplicativity is the only substantive determinant theorem and is explicitly cited. Polynomial factorization and uniqueness are explicitly cited as well. Both off-unit generic statement tools are declared in split_report.tool_uses for the maintainer to assess; none replaces a step of the cohomological unit route.

Small cases checked: V=W=0 gives P_F=P_G=1, determinants 1 and c^0=1. In dimension one, beta(v,w)=dvw with d nonzero and F=f, G=c/f gives detF P_G=f-cT and (-1)chi_F(cT)=f-cT. In dimension two, diagonal A with repeated nonzero eigenvalue yields repeated reciprocal eigenvalues, and a nontrivial Jordan block gives the same formula without diagonalizability. In characteristic two (-1)^n=1 and the determinant computation is unchanged; no alternating-form or characteristic-zero input occurs. The excluded c=0 is essential: zero operators would otherwise defeat invertibility. Ring embeddings need not be surjective. The argument needs neither an algebra structure on L selected separately nor a chosen eigenbasis.

The initial item had an empty proof and only old grep records. I supplied the missing algebra and real logged semantic and Loogle searches, while preserving its statement and source metadata. I corrected no mathematical statement and introduced no axioms or hollow objects. Nothing remains unfinished in this split.

## Validation

Server-side check and final delivery results are recorded below when available.
