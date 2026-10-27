# Q36: lem-sfb-pd-colour-profile-coefficients

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-pd-colour-profile-coefficients.json: statement, split into six explicit counting steps; not a Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-finite-permutation-cardinality.json: statement, exact Mathlib leaf Fintype.card_perm, Mathlib/Data/Fintype/Perm.lean:155-156.
- dag/nodes/sec-six-functors-basics/lem-sfb-finite-fibre-cardinality-sum.json: statement, exact Mathlib leaf Finset.card_eq_sum_card_fiberwise, Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean:985-987.
- citations.json: one verbatim statement quotation for every citation in every proof step.

## Attachments

None. Searched the project source under lean/WeilConjectures for the exact blueprint tag, colour/profile language, uniformBell and uniform partitions: no declaration states this item. The project uses finite fibre summation in LSeries.lean and other applications, but those specialized declarations do not state the generic counting lemma. Mathlib declarations are delivered as leaves, not project attachments.

## Literature wanted

None. This is an explicit elementary combinatorial refinement of the universal coefficient comparison already in the available source, not an invocation of an unavailable theorem.

## Problems and corrections

The original statement is correct and retained without change. Stacks dpa.tex Tag 07GP (lemma-check-on-generators), proof of (5) for x+y, identifies the universal coefficients using the rational polynomial ring, but does not itself state the red/blue profile identity. The item therefore has proof_origin.by=agent: its six steps give the missing counting argument rather than attributing it to Stacks. Its parent lem-sfb-pd-check-generators uses exactly the individual integrality and the profile sum proved here; the proof does not cite that parent, avoiding a cycle.

Nat.uniformBell_mul_eq and Nat.uniformBell_eq_div establish an uncoloured factorial quotient, not the profile coefficients or this convolution. Moreover Bell.lean explicitly lists the set-partition interpretation as a TODO. No such interpretation is used as a black box. Instead the map from ordered labels to partitions and its entire fibre description are given explicitly. The two new leaves supply only generic finite counting, and state neither a clause of the item nor a profile-specific surrogate.

Read dag/chapters/sec-six-functors-basics.json and dag/units/sk-thm-sf-ctf-stability.json, and the current literature/blueprint/latest unit and direct-image proof. The latest direct-image branch (3) is the inherited route this remote arithmetic input supports. The inherited ancestor command returns None; the item retains its null blueprint.from.node and existing via chain, and the two new leaves prepend this item to that chain. No source or target statement is weakened, and no chapter or unit file is changed.

## Unfinished work

None in the stage-1 split. The two new statement-only inputs are already exact Mathlib leaves; no further mathematical subproblem is deferred by this delivery.

## Not duplicates

A whole-DAG search for uniformBell, multinomial, factorial/permutation counts, the relevant Mathlib declaration names and fibre-cardinality identities found no node stating either new generic counting result. Blueprint searches for partition, cardinality, permutation(s), factorial and fibre found no equivalent blueprint statement. The fibre search returns geometric and categorical fibre statements, whose sets/maps and conclusions differ. Neither leaf cites a Stacks tag, so there are no same-tag new/existing pairs. The existing 07GP generator-criterion nodes are about divided-power operations, not generic finite-set counting, and are not duplicated.

## Review by Q36

I read coord/delivery-errors.md B through E in both its current and merged copies and checked this split against those examples. I read dpa.tex's full lemma-check-on-generators statement and proof, especially the last coefficient comparison for (5), and the parent node's complete statement and proof. The factorial denominators and the weighted profile constraints agree with the parent's arithmetic requirement. I read Mathlib/Data/Fintype/Perm.lean:155-160, including the decidable-equality context, for the first new leaf, and Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean:985-991 for the second. The first counts arbitrary finite permutations. The second assumes only that the map sends its finite source into its finite target; it allows empty fibres. Both hypotheses match their new node statements, with classical decidable equality available. The leaves have no proof sketches or proof dependencies. All their recorded searches actually ran through msearch.py; searches.jsonl retains the service outputs and query text.

Step 1 uses only the hypotheses and the definitions written there: n=0 forces a=b=0 and the unique zero tuple. For n>0, the block profile equations follow by counting disjoint blocks and red elements. Finite sets U and V can be the two tagged initial segments, so their existence requires no geometry. P is a subset of the finite power set of the power set of E, and each r_i is bounded by n.

Step 2 cites only the permutation-cardinality leaf. A reference order identifies orders of U or V with permutations, giving a!b!. The capacities sum to a and b because a+b=nm and the two profile constraints hold. Cutting gives disjoint m-element blocks, and m>=1 ensures distinct nonempty blocks when labels are forgotten. Thus the map really lands in P_r.

Step 3 again uses exactly the permutation statement to count assignments of slots to blocks of each type and orders within the red and blue parts. I checked both inverse constructions: cutting recovers each assignment and each internal order; concatenation recovers each list. There is one factor r_i!, not two: red and blue parts use the same assigned block. Even when i=0 or i=m, blocks remain nonempty, and the empty part has precisely one order. Multiplication counts independent choices; no orbit-stabilizer theorem or pre-existing block-profile theorem is hidden here.

Step 4 cites only the finite fibre-sum statement and substitutes the constant fibre size computed in step 3. Its source and target are finite and the map lands in its target by step 2; surjectivity is not an extra hypothesis of the leaf. D_r is positive as a product of positive factorials, so rational division is legitimate. This proves C(r)=|P_r|, not just that the total sum is integral.

Step 5 uses both leaves: the number of orders of E is (nm)!, and each fibre of the explicit consecutive-block map is bijective to a choice of block order and n internal orders. Nonemptiness of the blocks is essential and follows from m>=1. Fibre summation then gives |P| n! (m!)^n=(nm)! without assuming a Bell-number partition interpretation.

Step 6 uses only finite fibre summation for rho, with the target condition checked in step 1. Its fibres are P_r by their definition, so replacing their cardinalities by C(r) proves the convolution. Every cited node's complete statement was copied verbatim into citations.json for that step; no quotation was manufactured by joining text fragments. The proof-dependency list is exactly the union of uses. Both leaves inherit the unit and are Mathlib tools, so no off-route statement is used.

I tested the small cases exactly in rational arithmetic for every profile with 0<=n<=6 and 1<=m<=6, checking nonnegative integrality and the sum for every 0<=a<=nm. The proof also covers a=0, b=0, m=1 and n=1: pure colours give empty internal lists, singletons give one partition, and a single block has one profile. I checked the generic leaves on the empty set as well (one permutation, zero source cardinality for fibre summation). All six steps are under 1000 characters, and each is one explicit construction or a substitution into the cited counting theorem; there is no long-step hidden lemma. No SGA source, Lean edit, compiler, build tool or repository mutation is used.

Dry-run correction: the first preflight requested a cited definition for finite sets on both new leaves. I read def-sfb-finite-infinite-set in full; it defines Set.Finite and Set.Infinite, so I cited it in each leaf statement and added it to each stmt_deps. This introduces no new hypothesis or counting assertion. Updated every verbatim citation quote accordingly. The exact arithmetic audit comprised 3,424 profiles and 483 sum identities.
