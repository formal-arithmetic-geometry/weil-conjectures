# Stage-1 report: lem-sfb-split-square-zero-divided-powers

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-split-square-zero-divided-powers.json`: item, statement, split by direct verification of the five axioms and uniqueness; Mathlib verdict: no match.
- `citations.json`: one verbatim statement excerpt for the ordinary divided-power definition cited in each of the seven steps.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0. Every calculation below is an elementary step from the existing ordinary divided-power axioms, not a new lemma awaiting proof.

## Attachments

None. Searches of `lean/WeilConjectures/` for the exact blueprint id and the concepts `DividedPowers`, divided powers, and split square-zero extensions found no declaration stating the item. The unrelated uses of `TrivSqZeroExt` in cotangent and dual-number modules do not construct divided powers.

## Literature wanted

None. WANTED: none.

## What needed repair

The item was unsplit and had no proof or project Lean declaration. Its statement is correct and is unchanged, including all hypotheses and the meaning of the integer coefficients. Stacks 09PH gives the same formula for the even part of adjoining an odd graded variable, but does not give the arbitrary-module verification. I wrote that verification explicitly and marked `proof_origin.by` as `agent`. I read dpa.tex Tag 07GL (`definition-divided-powers`, lines 36 onward), Tag 09PH (`example-adjoining-odd`, lines 1004 onward), and Tag 07GP (`lemma-check-on-generators`, lines 151 onward). The last is mentioned in the original source field but is not used as an unstated theorem: all five axioms are proved directly.

The existing blueprint ancestor is null (confirmed by `tools/blueprint_refs.py ancestor`); its provenance chain is retained. I read the current `literature/blueprint/latest/` unit and its direct-image proof, step (3). This supporting algebra lemma does not change the direct-image route or either higher level of the blueprint. The stored unit record describes an earlier version of the unit; this delivery does not edit it.

## Not duplicates

No new nodes, so there are no new/existing pairs to disambiguate. Whole-DAG tag searches for 07GP and 09PH and keyword searches for split square-zero divided powers locate the item and its parent `lem-sfb-divided-power-variable-adjunction`, not another statement giving the item. The parent uses this lemma, so citing the parent instead would create a cycle. `def-sfb-ordinary-divided-power-structure` is the definition, not the extension theorem. Whole imported-blueprint searches for `divided powers`, `square.zero`, and `split square` returned no matching blueprint nodes; a text search of the latest blueprint also found no divided-power extension theorem.

## Mathlib search review

The new Q113 queries and their unmodified returned records are in `searches.jsonl`, and copied into the item's `mathlib_searches`; the existing Q50 search records were retained. I ran LeanFinder twice with different descriptions, Loogle, LeanSearch, and source grep through the required msearch command. I read the resulting `OfSquareZero.dividedPowers` and `dpow_of_two_le` at RatAlgebra.lean:194-207 and the `DividedPowers` axioms at Basic.lean:78-92. The square-zero theorem requires the entire ideal to square to zero; here I need not do so. The rational-algebra result adds an unavailable hypothesis. Subideal and quotient constructors start with a larger existing divided-power structure, and do not supply this extension. Thus no exact or one-line specialized match was found.

## Review by Q113

I checked the statement against the odd-variable formula in Stacks 09PH and the ordinary five axioms in 07GL. Neither nilpotence of I, flatness of M, I annihilating M, nor characteristic zero is required, and none is introduced in the proof. Every proof citation is `def-sfb-ordinary-divided-power-structure`; I opened its JSON statement and verified that it explicitly gives all five axioms, gamma_0=1, and the interpretation of factorial quotients as integer coefficients. The quotations in citations.json are copied from that statement, not from its proof or source field.

For step 1 the definition supplies the axioms to be checked. The multiplication, ring laws, ideal closure, image membership and identity operation are written out. The module in the associativity computation is arbitrary. Step 2 uses only scalar compatibility to get gamma_r(0)=0 and the product axiom with indices 1,r-1 to obtain x gamma_(r-1)(x)=r gamma_r(x); r=1 is handled separately. This also checks the two requested restrictions.

Step 3 uses the scalar axiom for gamma and the explicitly derived identity from step 2. I verified the second coordinate for an arbitrary scalar (c,v) in B; checking only scalars (c,0) would have missed its term involving v. The power formula is its immediate induction under the displayed ring multiplication. The proof treats n=1 separately, so there is no negative exponent at c=0.

Step 4 uses the addition axiom twice, after the two distinct reindexings for the coefficients of u and v. The endpoint terms use delta_0=(1,0), not the positive-degree formula; n=0 and degree-zero gamma identities are treated explicitly. Step 5 uses the product axiom and Pascal's identity. The gamma_0 factors when n=1 or m=1 are products with 1 and require no positive-index axiom. Pascal's identity is justified by the elementary partition of subsets, not cited as an unstated ring theorem.

Step 6 uses the iteration and product axioms of the cited definition; these axioms apply because gamma_m(x) lies in I. For n>=2 both outer indices used in the iteration axiom are positive. The m=1 product with gamma_0 is explicit, and outer n=1 is separate. I expanded both integer coefficients: their factorial expressions agree in Q as integers, and hence act equally on any C-module. No denominator is cancelled in C. This is a two-line coefficient identity, so creating a separate combinatorial node would be the elementary-node fault in the brief. Step 7 uses only the addition and identity axioms for the competing structure. Only indices 0 and 1 on (0,u) survive; this forces the formula for every n>=2 and proves equality of all operations.

I checked B--E of delivery-errors against the actual files. No new nodes hide a clause, no cited proof is used in place of a statement, and no non-elementary theorem is smuggled in by a tag. Each step is a direct coordinate expansion, finite reindexing or elementary integer identity from the quoted definition; the proof does not use the nontrivial generator-check theorem 07GP. All seven steps are shorter than 2000 characters, with their calculations written out. There are no external-unit theorem uses and no SGA sources.

For edge cases, M=0 reduces to the given structure; I=0 gives delta_n(0,u)=0 for n>1; n=1 and m=1 satisfy the iterate coefficient q(1,m)=q(n,1)=1. The zero ring forces M=0 and also satisfies the formula. In characteristic 2, take C=F_2[t]/(t^2), gamma_1(t)=t and gamma_n(t)=0 for n>1. With M=C, delta_2(t,1)=(0,t), which illustrates why neither I M=0 nor zero higher operations on all K may be assumed. The product and iterate checks retain this nonzero term. The integer iteration coefficient was also checked for small positive n,m without arithmetic in C.

## Unfinished work

None in this one-level split. The independently reviewed maintainer delivery remains the next project stage.
