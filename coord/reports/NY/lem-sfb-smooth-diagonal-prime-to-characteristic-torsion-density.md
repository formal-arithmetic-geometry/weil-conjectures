# Stage-1 delivery: lem-sfb-smooth-diagonal-prime-to-characteristic-torsion-density

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-smooth-diagonal-prime-to-characteristic-torsion-density.json`: statement, now split into six proof steps; Mathlib searches found no exact match. The statement and its statement dependencies are unchanged.
- `citations.json`: a verbatim statement excerpt for each citation in each proof step.
- `searches.jsonl`: actual msearch.py records for this attempt. The item's previously recorded searches are retained, together with the newly run searches.
- `report.md`: this report.

No new nodes; no new Mathlib leaves. There is no unit-record change because this supporting lemma is not the unit's key statement.

## Attachments

None. I searched the project library under `lean/WeilConjectures/` for the exact blueprint tag and for diagonalizable groups, torsion and density. The matches concerned torsion sheaves, abstract Tate modules and the definition and functor of points of a torsion subgroup scheme. None proves this item's finite reduced kernels, their prime-to-characteristic orders and schematic density. The available project group-scheme files do not contain a diagonalizable-group density theorem. No source declaration containing sorry has been counted as a finished proof.

## WANTED

None. Milne's book and the relevant Stacks sources are present locally.

## What needed work

The item was unsplit, with empty proof and proof dependencies; there was no earlier sandbox item or report to resume. Its statement is correct, including the absence of connectedness. I supplied the argument rather than introducing nodes restating its finite-kernel or density clauses.

Milne 12.32 gives the correct smooth density theorem, but the sentence about the product of an etale factor with copies of G_m leaves the multivariable density argument implicit. I supplied it using the explicit coordinate quotient in 12.33 and a Laurent-support bound. Restricting an assertion of joint injectivity for all n to prime-to-characteristic n would not be justified by the unrestricted assertion alone. The proof instead chooses arbitrarily large n = d(1+kp), so all finite components are included and the Laurent exponent box survives reduction.

The existing CRT node `lem-pc-crt-ideal-quotient-product` has correct mathematical content but its source metadata calls the Chinese remainder theorem Tag 00U3. I checked `literature/stacks-project/tags/tags`: 00U3 is `algebra-lemma-etale-over-field`; the Chinese remainder theorem is 00DT, `algebra-lemma-chinese-remainder`. Our step cites the existing CRT statement and gives the correct 00DT source. I have not edited that dependency. Its statement gives a quotient by an intersection, so the step explicitly proves that the intersection of these comaximal linear ideals is their product before using it.

No statement correction or statement dispute was necessary. The existing null blueprint ancestor is retained: `tools/blueprint_refs.py ancestor` reports None for the inherited creation chain. The detailed from.place and via chain are preserved. I read the current `literature/blueprint/latest/` unit and its direct-images proof, including (3); this is the existing alteration/moduli/solvable-group supporting input, not a replacement of that unit's route. Whole-blueprint searches for diagonalizable, torsion density and group algebra returned no statement identifying this item with an imported blueprint node, so same_as remains [].

## What remains unfinished

No mathematical part of this stage-1 split remains unfinished. Lean writing and compilation are outside the authorized stage and were not performed. Server validation and delivery results follow below.

## Not duplicates

No new node is proposed. I reused `lem-sfb-diagonalizable-group-geometric-criteria` for both the product decomposition and its exact smoothness criterion, `lem-sbc-finitely-generated-abelian-group-structure` for the decomposition of M, `lem-sfb-split-binomial-root-torsor` for root cardinality and factorization, and the existing CRT, affine coproduct-spectrum, affine fibre-product and monic-quotient leaves. I also read `lem-sfb-torus-torsion-joint-injectivity`, whose statement concerns every n over an arbitrary coefficient ring. Its statement alone does not give the restricted prime-to-p family, so the finite-support specialization is proved in our steps 4–5 rather than claimed as an application of that statement.

## Review by NY

I read Milne, Algebraic Groups (2017), printed pp.231–234 (Examples 12.1–12.2, Proposition 12.3, Remark 12.5 and Theorem 12.9), pp.241–243 (the smooth density theorem 12.32 and the coordinate quotient in 12.33), and p.303 (the finite prime-to-characteristic kernels used in Proposition 15.3). I also read the actual Stacks CRT statement and proof in algebra.tex, Tag 00DT, the opening Kummer discussion in fields.tex, Tag 09I6, and the tag mappings for the affine fibre-product and closed-immersion results, 01I4 and 01QO. The proof_origin is agent because I spelled out and adapted the finite-support argument; it does not claim Milne prints those details verbatim. There are no new nodes requiring additional sources, and no SGA source is used.

For step 1 I opened the statements of the finite abelian group structure leaf and the diagonalizable geometric-criteria lemma. The first provides a finite free part and finite cyclic prime-power parts, allowing trivial cyclic factors. The second gives the actual group-scheme product and, in positive characteristic, exactly the absence of nonzero p-power torsion from smoothness. If p divides a cyclic order, the class d_i/p has order p, so smoothness forces every d_i, and their product d, to be prime to p. No connectedness criterion is used.

For step 2 I read the definitions of G_m and mu_n, affine spectrum, and closed immersion. The group equations yield the kernel over every commutative F-algebra, including algebras with nilpotents. Bezout with inverse powers proves equality of the two defining ideals in the Laurent ring. This checks a scheme equality rather than merely a bijection of geometric points. The step is elementary because its only additional operation is the displayed integer identity for the gcd.

For step 3 I read the full statement of the split-binomial-root lemma: it gives both the cardinality of mu_a(F) and the complete factorization when the exponent is invertible and the polynomial splits. Algebraic closedness supplies splitting by successive linear division. Its integer exponent is specialized to our a, and its separate binomial constant is specialized to 1. All a involved are positive and prime to p. I read the CRT statement, used its actual intersection quotient, and explicitly verified comaximality and intersection = product. I read the finite affine coproduct-spectrum leaf: it identifies the scheme, including the maps, with the coproduct of the factor spectra. The affine fibre-product lemma gives the tensor coordinate algebra; the algebra-tensor universal-property node gives the algebra maps. The two explicit maps between the tensor of finite products of F and the product indexed by pairs are inverse on the coordinate idempotents. This proves that the product kernel is a finite disjoint union of Spec F and counts its F-points as n^r times the product of the gcds. Every factor of that number is prime to p and positive.

For step 4 I read the affine fibre-product and monic-quotient statements. The coordinate algebra B contains all finite factors, and adjoining the torus variables gives the finite Laurent sums over B. When d divides n, every finite-factor coordinate already has nth power one, so the displayed quotient describes the actual kernel inclusion. In the quotient each torus coordinate has inverse its (n-1)st power; this gives both directions of the polynomial-versus-Laurent quotient identification. The monic-quotient leaf works over any commutative coefficient ring, not only fields, so it applies successively over B and then the previously adjoined variables. Its precise basis is the exponent box used next.

Step 5 is an elementary application of that basis. I checked the quantifiers: n is chosen separately for the given finite support, is a multiple of every finite cyclic order, and is prime to p because n=d(1+kp). Coordinate minima exist only for nonzero f, which is the case considered. Multiplication by the clearing monomial is invertible and shifts distinct exponents to distinct members of the basis box; no coefficient can disappear or combine with another. The proof does not use density of points on a general reduced variety, an implicit Nullstellensatz, or a claim that coprime integers are cofinal for divisibility among all integers.

For step 6 I re-opened the affine description in the closed-immersion definition and the contravariant affine-spectrum statement. They give Z = Spec(L/I), and factorization annihilates I in each coordinate quotient. Step 5 then kills I. The final pointwise consequence uses the already proved evaluation-product coordinate algebra for each D[n], so vanishing on H_n is exactly zero restriction to that whole finite scheme. This is valid because those schemes were proved reduced and split.

I tested M=0, a free M, a finite M, mixed free and finite M, trivial cyclic factors and empty products. For rank zero, D[d]=D and the quotient in the support argument is the identity; for M=0 every c_n is 1. For D=mu_2 in characteristic 3, n=1 sees only the identity but n=2 sees both components, agreeing with the gcd formula. For G_m times mu_3 in characteristic 7, n=2 has two kernel points and n=3 has nine; large multiples 3(1+7k) see every component. In characteristic zero p=1 and the sequence d(1+k) is unbounded. The excluded nonsmooth case mu_p has nilpotents and its prime-to-p kernels would miss them, confirming where the smoothness hypothesis is essential.

Against delivery-errors B–E: all existing definitions used in the statement were retained, every added non-elementary proof input is an existing cited statement that I opened, and every citation has its literal quote in citations.json. No new node is elementary, duplicated, a restatement or a missed Mathlib leaf, since there are no new nodes. The two nontrivial algebraic identifications are given by explicit maps or generators and cited universal properties. All proof steps are shorter than 2000 characters. Mathlib searches were run only through the prescribed msearch.py; both semantic phrasings, Loogle and grep returned results about other notions rather than this theorem, and their actual queries and outcomes are recorded. Nothing outside the sandbox was written and no compiler, Lake or build tool was run.
