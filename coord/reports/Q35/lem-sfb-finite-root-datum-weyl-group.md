# Stage-1 delivery: lem-sfb-finite-root-datum-weyl-group

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-finite-root-datum-weyl-group.json`: item, split into four proof steps; statement unchanged.
- `dag/nodes/sec-six-functors-basics/lem-sfb-root-lattice-coroot-separation.json`: statement, Mathlib leaf `RootPairing.exists_coroot_ne`, `Mathlib/LinearAlgebra/RootSystem/Finite/Nondegenerate.lean:181`.
- `citations.json`: one verbatim statement quotation for every node citation in every item step.

One new node, one Mathlib leaf. Search outputs and the actual `searches.jsonl` are retained in this sandbox, together with the writing script. They are audit material, not repository changes.

## Attachments

None. Searched the current project `lean/WeilConjectures/` for the exact blueprint tag, Weyl, root datum and RootPairing, and searched the project sources for the separation declaration and root-span concepts. There is no project declaration stating this item. The Sheaf root-datum lattice embedding module is a different result with a finite-Weyl hypothesis, so it is not an attachment or an input here.

## Literature wanted

None. The item's source and the new leaf's source are present: Milne, Algebraic Groups, Appendix C.37--C.46, printed pp.615--619 (PDF pages 627--631). No SGA source is used. The source references are Milne proposition/lemma numbers, since these root-datum results are not Stacks results.

## What changed and what was wrong

The item was an unsplit statement with five useful searches and no proof. It is true as stated; no statement correction or STATEMENT-DISPUTED is needed. The crucial issue is that finite root sets do not by themselves allow the ambient lattice to be replaced by their span. Assuming a faithful root action from spanning, or averaging a form over W before proving W finite, would be circular or add a hypothesis. The split uses the displacement argument of C.45--C.46 instead.

The inherited searches correctly note the TODO for faithful permutation action in Mathlib. They do not mean that the linear-algebra prerequisite is absent: the searches in this delivery located `RootPairing.exists_coroot_ne`. I made that prerequisite a Mathlib leaf, with its full hypotheses and the automatically inferred anisotropy instance recorded. No new unsplit theorem is introduced. I kept the item's imported statement, source and metadata and retained its original five search records.

The nearest-blueprint-ancestor command prints `None` for this long supporting branch. I retained the item's inherited null `from.node` and its via chain and gave the new leaf the same null ancestor with this item prepended to `via`. Its place specifies the Milne nondegeneracy input and the existing direct-image proof (3) branch. I read the current `literature/blueprint/latest/` unit and direct-image proof. This is a supporting abstract-root-datum prerequisite below the unit route, not a replacement of a unit step. The unit statement itself is not this item, so no unit realization fields are changed.

## Not duplicates

lem-sfb-root-lattice-coroot-separation vs lem-sfb-finite-root-datum-weyl-group: the new result is separation of arbitrary vectors in the integer root span by coroots, with no Weyl group in its statement. The item's argument still proves the dual-action correspondence, displacement membership, annihilation for elements in the permutation kernel, and injectivity/finiteness.

lem-sfb-root-lattice-coroot-separation vs lem-sfb-root-datum-lattice-embedding: the existing result assumes the reflection group finite and gives rational splitting and weight-lattice information; it cannot supply the prerequisite here without circularity. The new leaf assumes only the simultaneous reflection axioms, requires neither reducedness nor a finite reflection group, and states separation on the integral root span.

lem-sfb-root-lattice-coroot-separation vs lem-sfb-rational-root-coroot-span: the existing result says that roots span their entire rational ambient space if and only if coroots do. It does not assert nondegeneracy on the root span when neither family spans; the new leaf does, over the integers.

lem-sfb-root-lattice-coroot-separation vs lem-sfb-finite-spanning-reflection-uniqueness: that result compares two reflection functionals on a finite spanning set in a rational vector space; it does not separate root-span vectors by the prescribed coroots of a nonspanning datum.

lem-sfb-root-lattice-coroot-separation vs lem-sfb-torus-finite-character-separation: its searches mention `RootPairing.exists_coroot_ne`, but its statement concerns torus points avoiding finitely many character kernels. It does not state the root-pairing fact. Searches of all DAG statements and blueprint nodes found no existing node for the new leaf. Whole-blueprint searches for root datum, coroot, root span, coroots separate, root-lattice and coroot separation found no matching imported node.

## Review by Q35

I read Milne C.37--C.46 in the local PDF, including the sum-of-squares polarization, the root-span/coroot-span argument and the displacement proof. The new leaf records exactly the separation consequence of C.44, rather than a reformulation of faithfulness. For its Mathlib match I read `RootPairing`'s actual fields in Defs.lean:82--98, `IsValuedIn` and the self-valued instance at IsValuedIn.lean:62, the definitions of rootSpan at line 166 and coroot'In at lines 218--226, and the complete domain-algebra hypotheses and proof of exists_coroot_ne in Nondegenerate.lean:147--188. With R = S = integers the displayed simultaneous permutations are exactly the RootPairing fields, and the perfect pairing is exactly its IsPerfPair field. The integer-valued instance supplies crystallographicness, and Nondegenerate.lean:87 supplies anisotropy. Thus the lemma specializes directly; no base-change theorem, reducedness, root spanning, positive-characteristic assertion, or finite Weyl group is smuggled into the match. All four required search kinds ran and their actual outputs are recorded. The first semantic search found only related facts; Loogle and LeanSearch returned the exact declaration.

For step 1 I reopened the statement of def-sfb-pinned-split-root-realization. Its root-datum paragraph explicitly supplies the perfect integer duality, root-coroot value 2, finite sets and preservation of their correspondence under both reflections. Those are the only clauses used. Squaring the reflection gives the identity; evaluating a dual functional on s_alpha(m) gives the displayed dual reflection. Composition gives the equivariance for every word. These are calculations, not an uncited structural theorem about reductive groups. I do not use the definition's reducedness clause or any group-realization clauses.

For step 2 I reopened def-weil-submodule-span: its statement says precisely that the span is the smallest submodule containing the given set. This justifies root membership, integer scalar closure and additive closure. Step 1 already proves roots are permuted, which implies preservation of their span. The empty-word, generator and multiplication cases of the displacement induction are all written; there is no appeal to C.45 as an unnamed black box.

For step 3 the same root-datum paragraph explicitly states preservation of root-coroot correspondence. Equivariance from step 1 therefore turns fixing roots into fixing the corresponding coroots. The pairing evaluation is written with the inverse dual action; using the forward action at this point would reverse the covariance incorrectly. Each cited definition says precisely what is taken from it, and none is used as a substitute for a theorem.

For step 4 I read the new leaf's statement against the item before applying it. Set I equal to Phi, use the inclusion of roots and the bijective coroot map as the injective families, and use the simultaneous permutations. All its hypotheses are in the item. Steps 2 and 3 give respectively membership of the displacement in the integer root span and vanishing of every coroot evaluation. The leaf's existence conclusion contradicts a nonzero displacement. The final quotient-of-two-elements argument proves injectivity, and counting finite self-maps proves finiteness. These last deductions are elementary and are included explicitly. The single non-elementary input is named and cited; there is no hidden comparison theorem or sublemma in any long step (the longest step is 849 characters).

I tested empty roots in a nonzero lattice: their integer span is zero and the generated group is trivial, so both the leaf and item remain valid. Rank zero gives the same case. For a nonspanning rank-two test take M = Z^2, roots plus/minus (1,0), and coroots plus/minus (2,1) in the ordinary dual. The generator sends (x,y) to (-x-y,y), so central directions are tilted and are not simply the second coordinate summand. The displacement lies in Z(1,0), where evaluation by (2,1) is injective, exactly as the proof needs. For a nonreduced rank-one test take roots plus/minus 1 and plus/minus 2 in Z, with respective coroots plus/minus 2 and plus/minus 1; all generators are negation, and the proof remains valid. This checks why reducedness is unnecessary. Neither I nonempty nor roots spanning was assumed in the leaf's actual Lean theorem.

I checked delivery-errors B--E against the written files: the new node is self-contained and carries no proof; standard module and span notions cite their actual definition nodes; the source is a precise Milne lemma; every Mathlib query was actually run, its successful response read, and line numbers checked. The real smaller input is already a Mathlib leaf, so no unnecessary unsplit node, restated clause or elementary new node is added. The citation file quotes the actual statements verbatim. The new leaf depends only on free-module and span definitions, so this split introduces no route back to the item. The report records the nearby nonduplicates explicitly. All mathematical hypotheses used in the four steps have been accounted for above.

## Unfinished work

No mathematical split work remains. Stage 1 supplies a natural-language proof and the Mathlib leaf; no Lean files or compiler tools were used. The required server dry run and direct push are performed after this report is written.
