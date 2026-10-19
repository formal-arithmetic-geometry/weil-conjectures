# Worker report

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-finite-graded-module-dehomogenization.json`: statement item, split into seven elementary steps following Stacks 07Z2(2). Mathlib searches find the algebra finite-type result and ordinary localized-module finiteness, neither of which states this item.
- `citations.json`: seven verbatim statement quotations, one for each step/node citation.
- `searches.jsonl`: actual searches recorded by the required msearch command.

No new nodes and no Mathlib leaves are delivered. The item statement is unchanged. The four definition dependencies remain exactly those of the original item. No unit record is changed: this auxiliary algebra lemma is not the unit's key statement.

## Attachments

None. Searched WeilConjectures in the read-only slopmaster2 source for the item id, dehomogenization, and graded-module / homogeneous-finiteness terminology. The project dehomogenization equivalences concern polynomial rings, not finite graded modules. ProjectiveSpectrum/Twist.lean explicitly still lists arbitrary graded-module sheafification as TODO. None of these is an attachment for this item.

## WANTED

None. The source used is available locally.

## Problems found and decisions

The imported item had no proof and no Lean audit entry. Its statement is faithful to Stacks algebra.tex, Tag 07Z2, label lemma-dehomogenize-finite-type, assertion (2), specialized to R=C_0 and nonnegative module degrees. No statement dispute or correction is necessary.

The source says "arguing as above" for modules. I expanded that phrase into projection to the degree of the numerator and Euclidean division of each monomial exponent. In particular, nonnegative module degrees imply that the reduced denominator exponent is nonnegative. This check would need modification for arbitrary integer-graded modules; the present item explicitly assumes nonnegative degrees. No nonzerodivisor assumption is needed, since the fraction identity is proved by identical numerators and identical denominators.

I searched the DAG by 07Z2, homogeneous generators, the Mathlib declaration exists_finset_adjoin_eq_top_and_homogeneous_ne_zero, and the monomial/exponent terminology. I also searched all imported blueprint nodes with blueprint_refs.py for dehomogen, homogeneous generators, and homogeneous. The finite-homogeneous-module-generator node lem-sc-p1-finite-homogeneous-generators has the extra restriction S=k[x_0,x_1]. It does not supply this item's general ring hypothesis. No general helper node is needed: replacing finitely many generators by their finitely many components is a direct argument from the direct-sum decomposition and is written in steps 1 and 2.

Mathlib GradedAlgebra.exists_finset_adjoin_eq_top_and_homogeneous_ne_zero, read in RingTheory/GradedAlgebra/FiniteType.lean lines 43--45, supplies homogeneous algebra generators. Its component argument at lines 30--40 is also exactly the elementary operation written in step 1, so a new leaf for this two-line operation would add no real mathematical subproblem. HomogeneousLocalization.Away.finiteType at HomogeneousLocalization.lean lines 1097--1098 supplies only algebra finite type. Module.Finite.instLocalizationLocalizedModule supplies finiteness over the full localization, which is insufficient for this item. Both semantic phrasings were searched and their actual outputs read. New searches are recorded as run, alongside the inherited searches retained from the original node; none was invented.

## Unfinished work

None within the requested one-level split. The required server dry run exited successfully: OK (not pushed) deliver/N1/lem-per-finite-graded-module-dehomogenization at 342ea6dca8; preflight passed. The direct delivery follows this successful dry run.

## Review by N1

I read the full statement and proof of algebra.tex Tag 07Z2 (lemma-dehomogenize-finite-type), including the first assertion's monomial reduction and the final paragraph establishing the module assertion. The seven steps follow precisely that argument. I also opened the chapter and unit records, the current blueprint proof of lem-per-artin-gabber-affine-curve, and the existing parent lem-per-finite-graded-proj-morphism. This is the local finite-generation input already named by that parent; it does not substitute a route for the perverse-unit argument or introduce an SGA source.

For step 1, def-weil-pbc-finite-type-algebra says that every algebra element is a polynomial in finitely many generators over the base. The finite support of each generator's direct-sum expansion proves directly that replacing the generators by their components preserves generation. For step 2, def-weil-finitely-generated-module says exactly that there is a finite spanning family. Its homogeneous replacement spans because it contains each original generator's sum. These statements require neither a field nor Noetherianity, so the restricted projective-line homogeneous-generator node was deliberately not cited.

Step 3 uses only the two generating families already constructed: expand each coefficient into monomials and project the resulting finite sum to M_(kd). The degree compatibility C_a M_b contained in M_(a+b), supplied in the item's statement, justifies the degree of every term; uniqueness in the direct sum discards all other degrees. There is no exactness-of-localization theorem being invoked implicitly.

For step 4 I read def-nagata-homogeneous-localization-degree-zero and def-sc-degree-zero-module-fractions. The first gives fractions with numerator degree md over f^m; the second gives the module's equal-degree fractions and says its operations are inherited from ordinary localization. Hence g_i^d/f^(a_i) is an actual scalar and every displayed candidate is an actual module element. The newer blueprint variant of the ring definition also permits nonhomogeneous f, but agrees with this special homogeneous positive-degree case. Step 5 uses only the finite box 0<=r_i<d and uniqueness of h from hd=A for d>0; it invokes no combinatorial finiteness theorem beyond a finite product of finite sets.

Step 6 cites the module-fraction definition for the inherited scalar multiplication. The Euclidean identities e_i=dq_i+r_i and kd=sum e_i a_i+b_j give d(k-sum q_i a_i)=sum r_i a_i+b_j. All terms on the right are nonnegative under this item's hypotheses, proving the remaining denominator is a natural number. Expanding the right-hand fraction gives exactly the same numerator and f^k denominator. Thus this step never cancels a potentially zero divisor. Step 7 uses the module-fraction statement for a representative and the finite-module definition for the conclusion; the intervening expansion is a finite distributive sum. Every used node was opened, and citations.json quotes its statement verbatim. There is no appeal to another node's proof.

I checked zero module and empty generating families, the empty algebra family C=C_0, d=1, positive weights other than one, and zero/nilpotent f. In C=C_0 with no positive components, a positive-degree f must be zero and localization is zero; the general formulas still hold without a separate nonzero assumption. For example with C=R[g,f], deg(g)=2, deg(f)=d=3, a module generator in degree 1 leaves only remainder exponents r with 2r+1 divisible by 3; this tests that omitted congruence classes supply no false generators. For d=1 every remainder is zero, leaving at most one candidate per homogeneous module generator. A nilpotent denominator may identify every fraction with zero but does not invalidate any identity or the spanning claim. Non-Noetherian C_0 causes no issue: the proof uses explicit finite lists, never finite generation of a submodule by Noetherianity.

Against delivery-errors B--E: no new statement-only nodes are needed, no duplicates or clause-restatement nodes are created, the statement is self-contained with its existing definition dependencies, and single TeX backslashes were preserved. Each external fact used is a cited definition; the remaining facts are the explicitly written finite-sum and integer calculations. Every step is below 2000 characters (the largest is 651), and none hides a standard comparison lemma. The proof dependency list is exactly the union of the seven uses lists. No fields owned by the maintainer, source checkout, live repository, or launcher script were edited.
