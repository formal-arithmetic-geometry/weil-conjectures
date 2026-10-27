## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-closed-translation-stabilizer.json`: the item, split in eight steps, statement unchanged.
- `dag/nodes/sec-six-functors-basics/lem-sfb-constant-source-closed-factorization-locus.json`: new statement-only node; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-product-integral-varieties.json`: new statement-only node; no exact Mathlib match established under these hypotheses. A geometric-integrality candidate is recorded with its missing hypothesis explained.
- `citations.json`: exact statements quoted for every node citation in every proof step.
- `searches.jsonl`: actual search-command records, retained in full. The sandbox also contains the writing script.

## Attachments

None. I searched `lean/WeilConjectures/` for the item tag, translation stabilizers, transporters and divisor-multiplicity/component-preservation terminology. The hits were abstract group stabilizers, Galois actions and unrelated equivariant transporters, not a project declaration giving this scheme functor and its Cartier assertion. No Lean was written and no compiler was run.

## WANTED

None. Both supporting sources are present in the read clone.

## Findings and changes

The item itself is mathematically sound. Its source correctly distinguishes Milne's transporter theorem from the additional agent-stated divisor assertion. I retained that distinction and the original statement. In particular, I did not replace a scheme-theoretic stabilizer by the stabilizer of rational points, and did not assert smoothness of the full stabilizer in positive characteristic.

Milne, Algebraic Groups (2017), printed pp.30–31, Proposition 1.79 and Corollaries 1.80–1.81, gives the inclusion-transporter/intersection route. I read that text and its supporting closed-functor argument, Theorem 1.105 with 1.100–1.104 on printed pp.36–38. The new factorization-locus node is that latter general input for an arbitrary family from a constant source; it is not a translation-stabilizer restatement. Equality is proved by intersecting the forward and reverse inclusion loci in the item's own step 2, and the group law and arbitrary base-change assertion are proved there as well.

The final assertion needs multiplicities, not only supports. I use the already present reduced-identity-component theorem, prove that the action fixes each support component using an integral scheme product, check every height-one order by a local-ring isomorphism, and use the existing affine normal-domain principal-divisor kernel to recover equality of Cartier ideals. The closed stabilizer of F itself then upgrades preservation on rational points to the universal action equality, because C is reduced. This avoids claiming that equality on closed fibres alone implies equality of arbitrary nonreduced families.

I read the current blueprint at `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`, especially paragraph (3), as well as the current chapter/unit records. The long ancestry already recorded in the item connects this geometric auxiliary to the alteration input on that route; the current paragraph contains no direct stabilizer argument to copy. The blueprint ancestor tool returns null for this already-null chain; I retain that value and extend its exact place/via data for the two new nodes. Blueprint searches for stabilizer, transporter, morphism functor, factorization, irreducible components, multiplicities, Cartier Weil, normal-c1-injective, connected group, product integral, product of varieties and 05P3 found no duplicate. Whole-DAG searches were also read; the available rigidity theorem and Hilbert-scheme statements do not supply these inputs.

## Not duplicates

lem-sfb-constant-source-closed-factorization-locus vs lem-sfb-closed-translation-stabilizer: the new node has no group or action; it represents factorization of any constant-source family into a closed subscheme. The item still constructs equality from two inclusion conditions, proves the subgroup/base-change clauses, and proves its divisor assertion.

lem-sfb-product-integral-varieties vs lem-sc-rigidity: the latter proves factorization of a morphism from a product when one slice is constant and one factor proper; it does not state integrality of products. The 05P3 occurrence in its proof is not part of its statement or source record. The new node states exactly the integral-product conclusion of Stacks 05P3.

lem-sfb-product-integral-varieties vs lem-sc-abelian-variety-characterization: the latter proves geometric integrality for complete group varieties; the other product factor needed here is a possibly singular support component, with no group structure.

## Review by Q28

I checked B–E with the node statements open. The two new nodes are self-contained, contain no proof or proof dependencies, introduce their objects, and cite definitions of scheme, field, finite type, separatedness (the common morphism-conventions node), closed immersion, products and integrality. Their blueprint fields inherit the item’s verified null ancestor and full via chain. I did not create nodes for the intersection calculation, subgroup identities, component-image argument, or nilradical argument: these are written in the item. No proof step is longer than 2000 characters.

For the first new node I read Milne 1.100–1.105, including the basis-coordinate construction of 1.102–1.103 and finite-affine-cover intersection in 1.105. Pulling Mor(Y,W) back along S → Mor(Y,X) gives the stated closed locus; its property is tested on every T, with no flatness or reducedness hypothesis on T. The finite-type/separated hypotheses on Y, X and S are within the algebraic-scheme setting of the source. The S' base-change clause is its universal property restricted to S'-schemes, so it includes bases S' outside finite type. Empty Y gives all of S; W empty gives the appropriate empty factorization condition, and a map already landing in W gives all of S. A nonreduced test ring retains the ideal equations, not merely their radicals.

For the second new node I read Stacks `varieties.tex`, Tag 05P3, `lemma-product-varieties`, including the affine tensor-product proof with a maximal ideal avoiding a nonzero coefficient product. Its hypotheses match nonempty integral separated finite-type schemes over an algebraically closed field. It does not claim the corresponding statement over arbitrary fields: Spec(C) times_R Spec(C) is a counterexample to that omitted hypothesis. Products with Spec(k) and products of positive-dimensional varieties satisfy the intended statement; the empty scheme is excluded by integrality, rather than silently treated as integral.

I ran and read semantic, Loogle and local Mathlib searches for the item and both new inputs, with second phrasings. Abstract `MulAction.stabilizer` does not represent this scheme functor. `IsClosedImmersion.lift` needs a supplied kernel-ideal containment and does not construct the parameter locus. `GeometricallyIntegral.isIntegral_of_isLocallyNoetherian` and the pullback instances were read in `Mathlib/AlgebraicGeometry/Geometrically/Integral.lean`, lines 91–114: they require geometric integrality, whereas Stacks 05P3 starts with integrality over an algebraically closed field. I have not claimed the missing upgrade as an inferred instance or as a one-line specialization. The candidate stays recorded rather than being mislabelled a leaf. The search queries in the new nodes are copied from searches.jsonl; all services used for these records answered, and no searches are invented.

Step 1 uses exactly the universal closed factorization locus. Its Y is Z, its parameter S is A and its target W is Z in A. Properness and finite type of A, and the closed immersion Z → A, give the separated finite-type objects required. No smoothness of Z or proper parameter-change assumption enters.

Step 2 is the two-inclusion calculation, plus the definition of closed subgroup scheme, whose statement I read. Translation of the reverse inclusion gives the missing inclusion. The equality functor at every S-scheme T is literally the restriction of the original functor; this proves arbitrary, not merely field, base change.

Step 3 cites the exact existing `lem-sfb-abelian-closed-subgroup-reduced-component`, which states that C is an abelian variety embedded as a closed subgroup. It also cites `lem-sc-abelian-variety-characterization` for integrality, and `lem-trf-smooth-geometrically-normal` (Stacks 056T, whose source paragraph I read) for normality of A. I checked that these statements apply to arbitrary characteristic, rather than using the characteristic-zero matrix-group version of Cartier's theorem.

Step 4 uses exactly 05P3 via the new product node. Its C is integral by step 3 and its D is a reduced irreducible support component, so both are nonempty varieties. The image closure contains D via the identity and is irreducible inside Z; maximality then forces D itself. Applying this to -c proves equality, not merely containment. This few-line topological argument needs the integral scheme product, not continuity for a product topology on C(k) × D(k).

Step 5 uses the complete statement of `lem-trf-normal-domain-principal-divisor-kernel`, including both the DVR assertion and the kernel = units assertion. I read its source record (Stacks 00PD, 031S, 031T, 02RL, 0BE3, 02RP) and the normal-divisor local argument in `divisors.tex` around `lemma-normal-c1-injective` as a check on the local unit criterion. Normal Noetherian domain affine charts of A meet its hypotheses. An automorphism fixing the generic support point preserves the normalized order because it preserves the maximal ideal of the DVR. Every height-one point where a local equation is nonunit is a minimal prime over that equation; this identifies exactly the support-component generic points needed. On all other height-one points both orders vanish. The cited kernel theorem then gives equality of actual ideals, not only equality of line-bundle or divisor classes.

Step 6 reapplies the already cited general factorization theorem to F. This is not a circular invocation of the item for F: it repeats the explicit construction of steps 1–2 from the new general input. Step 7 cites exactly the smooth-scheme density statement in `lem-pc-rational-points-dense`. It applies because C is smooth over the algebraically closed, hence separably closed, field. A closed subscheme containing that dense set has full support; reducedness then kills its entire ideal. Infinitesimal structure of H and K is retained throughout; only C is reduced.

Step 8 uses the universal point of K and the explicitly given automorphism τ, whose inverse is (x,c) ↦ (x-c,c). The cited `lem-pc-flat-pullback-effective-cartier-ideal` states exactly the preservation of a nonzerodivisor Cartier ideal by flat pullback; I read its statement and Stacks source record 02OO case (6). Projection p1 is a base change of C → Spec(k) and is flat. Thus both sides are defined as effective Cartier divisors, and the equation is equality of ideals after τ, not an isomorphism chosen fibre by fibre.

I tested the whole split on Z empty and Z = A (stabilizer A), on F = 0 (empty support, no height-one components), on a zero-dimensional abelian variety, on positive-characteristic nonreduced stabilizers, and on support components with unequal multiplicities. For F = 0 the divisor equation is immediate; the component argument is vacuous and the closed-locus conclusion still applies. Unequal multiplicities are preserved because C fixes each component, rather than merely permuting the support. The restriction to the reduced identity component is essential to this argument. No statement repair was needed. The generic off-unit tools are declared in split_report.tool_uses for the maintainer to judge; I set no maintainer-owned tool_uses field.

## Unfinished work

None for this one-level split. The two newly stated inputs are intentionally unsplit and join the stage-1 queue. No second agent was started, as required by the direct-delivery brief.
