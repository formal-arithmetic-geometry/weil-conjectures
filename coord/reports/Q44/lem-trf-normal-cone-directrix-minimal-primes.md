# Q44: lem-trf-normal-cone-directrix-minimal-primes

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-normal-cone-directrix-minimal-primes.json`: statement item, now split into ten proof steps; statement unchanged; no Mathlib match for the whole assertion.
- `citations.json`: sixteen uses edges with the complete, verbatim statement of each cited node.
- No new nodes and no new Mathlib leaves. Five existing statement leaves are reused: finite-flat-local-free, infinite-field-top-form-direction, monic-polynomial-nonzerodivisor, krull-intersection-jacobson, and reduced-zerodivisors-union-minimal-primes.
- `searches.jsonl` is the unmodified output log made by msearch.py. `prepare.py` is a sandbox-only preparation script, not a delivery file.

## Attachments

None. Searching `lean/WeilConjectures/` for the exact blueprint tag, directrix, normal-cone/minimal-prime combinations, and minimal-prime usages found no declaration giving this item. The generic minimal-prime and regularity facts are not attachments for the full assertion. The item has no Lean declaration or Lean-audit open entry to assign.

## Wanted literature

None. The item's source is expressly an agent synthesis, not a theorem asserted to occur in a single Stacks tag. Its supporting Stacks sources and Mathlib polynomial statements are locally available and were read. No SGA source was used.

## Audit and corrections

The imported item had a complete statement but no argument. It named 00MH as support for finite flat modules over a local ring; 00MH is actually the more general local-map/free-fibre lemma. I now cite the existing 00NZ finite-flat-local-free node directly, with its hypotheses verified. For separation I use the existing 00IQ Jacobson-radical version, specializing to the local maximal ideal; 00IP is its local counterpart. These are source-pointer refinements, not statement corrections. There is no STATEMENT-DISPUTED issue.

The quotient by a minimal prime need not be flat over A, and I do not assume it is. Step 3 computes its actual graded residue fibre and kernel: the source degree is I^j/mI^j, the target is (I^j+p)/(mI^j+p), and representatives of the kernel can be chosen in p intersect I^j. This is stronger precision than a comparison of radical supports and is essential to the argument.

The proof follows the inherited filtered-algebra refinement below the Hilbert--Samuel component-rigidity node. I read that parent's statement and Step 2, its review, the chapter record and sk-i-curve-zero record. This subitem supplies the vertex containment its parent needs. It changes neither a unit statement nor the current contracting-correspondence unit route. No unit realization record is due for this created sublemma.

## Not duplicates

No new nodes were created, so there are no new/existing same-tag pairs. I searched the whole DAG by directrix, normal flatness, finite-flat/free local modules, Krull intersection, minimal-prime zero divisors, injective reduction, and monic polynomials, and used the existing nodes instead of recreating them. `tools/blueprint_refs.py search` was run for directrix, finite flat, Krull intersection, normal cone and minimal prime, and `ancestor` identifies lem-trf-local-term-locality. The blueprint matches for normal cones define geometric cones, and the minimal-prime match is a definition of curve branches; none states this kernel assertion. Text searches of both the current main-20261015 and older master blueprint found no exact counterpart. The item's same_as remains empty.

## Review by Q44

I read the item and all its statement-dependency statements. Standard graded here explicitly means B_0=k and no negative degrees; that is precisely what makes the highest T_1 coefficient a scalar. The tensor node supplies its bilinear quotient construction and functorial maps, not any assertion of flatness: Step 1 proves flatness of each summand directly from the assumed tensor-injectivity of G. The Noetherian node says every ideal is finitely generated, which supplies finite generators of I^j. The associated-graded node explicitly gives I^j/I^(j+1), its direct sum, and multiplication of initial forms, exactly the data used in Steps 1, 3, 4 and 8. No theorem is inferred merely from a definition's proof or pointers.

For Step 2 I opened the statement of lem-weil-pbc-finite-flat-local-free and Stacks algebra.tex, Tag 00NZ / lemma-finite-flat-local, lines 19223ff, and Mathlib RingTheory/LocalRing/Module.lean around free_of_flat_of_isLocalRing. It states exactly that a finite flat module over a local ring is free. A is local and the finite/flat conditions were checked in Step 1. Finite rank then follows from finite generation, including rank zero.

For Step 3 I checked each quotient against the actual associated-graded definition. Tensoring a quotient A-module with k is explicitly identified by mutually inverse formulas, so this step uses no unrecorded flatness or Tor theorem. The containment I^(j+1) inside m I^j follows from I inside m. A minimal prime is contained in the unique maximal ideal since it is a proper ideal of a local ring. Subtracting b in m I^j from x gives a representative in p intersect I^j; merely lifting to p without checking its I-order would have been insufficient.

Step 4 reduces to homogeneous kernel classes because q_p preserves degree; degree zero is k to k, the identity. For Step 5 I opened lem-trf-infinite-field-top-form-direction and Mathlib Algebra/MvPolynomial/Funext.lean, funext_set lines 57ff. Its statement supplies a nonzero evaluation vector for a homogeneous polynomial over an infinite field, exactly what is used. The characteristic-zero hypothesis gives an actual injection Q into k because nonzero rationals are units; it is not assumed that an arbitrary residue field preserves arbitrary subfields. The e=0 case is settled first, so the leaf's positive number-of-variables hypothesis holds. Extending v to a vector-space basis gives an invertible substitution with its inverse written as the inverse matrix.

For Step 6 I opened lem-weil-pbc-monic-polynomial-nonzerodivisor, Mathlib Algebra/Polynomial/RingDivision.lean at Monic.mem_nonZeroDivisors, and the supporting monic regular-sequence calculation in Stacks 07BV / lemma-colimit-syntomic. The statement applies to every commutative coefficient ring D, even with zero divisors. Homogeneity bounds every T-exponent sum by n. A B_+ coefficient forces a strictly smaller T-degree; therefore the coefficient of T_1^n after substitution is exactly H(v), with no B_+ correction. Scaling by its inverse makes a genuinely monic polynomial and the cited leaf proves injective multiplication. Undoing the explicitly invertible substitution preserves injectivity.

Step 7 is the actual finite-matrix computation, not a citation to a definition of flatness: lift a left inverse of the injective residue matrix, note that the determinant of the composite is 1 modulo the maximal ideal, and use its adjugate to obtain a left inverse. I also read Stacks 00ME / lemma-mod-injective; I only need its finite-free special case, whose entire determinant proof fits in three sentences here. This elementary calculation is not introduced as a separate node. No surjectivity of multiplication on G, completion, or analytic reducedness is used.

For Step 8 I opened lem-weil-pbc-krull-intersection-jacobson, Stacks 00IQ / lemma-intersection-powers-ideal-module part (2), the adjacent local version 00IP / lemma-intersect-powers-ideal-module-zero, and Mathlib RingTheory/Filtration.lean at iInf_pow_smul_eq_bot_of_le_jacobson. R is Noetherian, M=R is finite, and I lies in the sole maximal ideal, which is the Jacobson radical. Separation gives a finite I-order for every nonzero b. The associated-graded multiplication formula then says the initial form of ab is the image under the already injective U_r, giving the contradiction without assuming equality of orders in advance.

For Step 9 I opened lem-weil-pbc-reduced-zerodivisors-union-minimal-primes, Stacks 00EW / lemma-reduced-ring-sub-product-fields part (3), and Mathlib RingTheory/Ideal/MinimalPrime/Localization.lean at iUnion_minimalPrimes and disjoint_nonZeroDivisors_of_mem_minimalPrimes. Its statement explicitly turns a in a minimal prime of a reduced ring into ab=0 for some b nonzero. The reduced hypothesis is present. This contradicts precisely the nonzerodivisor conclusion of Step 8, not merely regularity on the fibre. Step 10 gives the descended map on representatives and checks its surjectivity, so the equivalent factorization clause is included.

I tested I=0 (only degree zero survives, so necessarily e=0), e=0 with arbitrary I, a domain (the sole minimal prime is zero), and R=Q[x,y,z]_(x,y,z)/(xy) with I=m and theta giving B=Q[x,y]/(xy), T=z. For the two minimal-prime quotients the kernels are (x) and (y) and both die under B_+; z maps nontrivially to the vertex and is indeed regular. In the same ring with I=(z), G=A[T] is A-flat and the component fibres have zero kernel, checking a centre other than m. Zero graded pieces and degree-zero kernel classes were checked separately. These tests exercise the matrix rank-zero case and do not require the quotient component to be normally flat.

Every step's uses entry has a verbatim quoted statement in citations.json. The five statement tools are already Mathlib leaves and may be used across units; the other citations are definition nodes. I reviewed delivery-errors B--E: there are no statement-only new nodes to check, no duplicated clauses delegated to new lemmas, no hidden source reference used instead of a proof, and no cyclic use of a parent. All steps are shorter than 2000 characters. The elementary steps are concrete tensor/retract, quotient, grading, matrix or factorization computations; the non-elementary free-module, polynomial, separation and zero-divisor facts are named citations. No Lean file, compiler, repository write or git command was used.

## Unfinished work

No mathematical step remains open in this one-level split. The server dry run and push are recorded by the delivery tool; independent maintainer review remains part of the project protocol.
