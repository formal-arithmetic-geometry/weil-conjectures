## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-dg-countable-subalgebra.json`: statement, now split. Mathlib verdict: no exact declaration; the logged semantic searches return truncations, K-projective complexes and ordinary countability, and the grep finds measure-theoretic subalgebras. No new nodes or new Mathlib leaves.
- `citations.json`: verbatim statements for every step/node citation.

## Attachments

None. Read-only searches of `lean/WeilConjectures/` for the exact id, countable subalgebra terminology, and DG/countable terminology returned no declaration stating this item. The item has no finished Lean declaration to attach.

## WANTED

None: the source is locally available.

## Corrections and scope

The original statement is correct and unchanged. Its proof was empty. I supplied the entire construction, including the countability of the generated DG subalgebras and the primitive-killing argument. The source's phrase “cochain ... which maps to zero in H” is made precise as a cycle which is a boundary in A; arbitrary noncycles have no cohomology class. This is clarification of a proof phrase, not a statement dispute.

I retained the inherited blueprint metadata. `tools/blueprint_refs.py ancestor lem-sfb-dg-countable-subalgebra` prints `blueprint.from.node = None`; following the created-item chain shows that the added prerequisite chain has null ancestors before the historical direct-images connection. No ancestor was invented. The historical place and via chain are preserved. I read the latest blueprint files `sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md` and `sk-thm-sf-ctf-stability-direct-images.proof.md`, and the stored chapter/unit records. This splits the assigned supporting countability argument, not the unit's own statement or its route. A whole-blueprint search for countable gave 27 results, none stating the DG subalgebra claim.

## Not duplicates

No new nodes. DAG searches for 0CRM, countable subalgebras/subrings, countable unions and countable closure found the existing telescope parent and the existing countable-unions leaf. The coordinate-submodule and directed-poset closure statements have different structures and are not used. I reused `lem-trf-countable-unions`, rather than creating countability nodes.

## Review by Q38

I read Stacks `dga.tex`, Tag 0CRM, `lemma-countable`, especially lines 7095–7116, with the item open. Its assumptions are countability of every graded cohomology group; its proof constructs a countable quasi-isomorphic DG subalgebra. The item's explicit coefficient ring Z permits closure under unit, sums and negatives to supply all required scalar operations. Nothing uses commutativity, connectivity, boundedness, or countability of the ambient algebra. The source's increasing-subalgebra construction is retained exactly.

Step 1 spells out homogeneous closure using the unit, all degree-tagged zeros, negatives, differential, same-degree sums and arbitrary homogeneous products. The maximum of two finite stages proves closure; the DG identities restrict from A. This is an elementary construction, not an appeal to an unrecorded DG-generation theorem. Step 2 cites the full statements of `def-sfb-countable-set` and `lem-trf-countable-unions`, both of which I opened. The former gives an injection into N and hence singleton/empty-set countability; the latter gives restricted countable unions, sequence unions and binary unions, all without countability of the ambient set. Unary images are restricted unions of singletons, and binary images are two nested such unions. Consequently no uncited image/product countability theorem is hidden in that step. These are the exact clauses quoted in citations.json.

Step 3 again uses the restricted-union and sequence-union clauses of the existing leaf: choose one cycle for each class in every H^i(A), count the singleton values, then enumerate integer degrees. This proves surjectivity without assuming that all cycles in A are countable. Step 4 restricts an injection of the countable B_n to the subset of cycles which bound in A, chooses a primitive only for those cycles, and applies the same leaf to the singleton primitive values and their union with B_n. The earlier explicit closure construction supplies B_{n+1}. The two kernel inclusions are proved by the chosen primitive and the inclusion into A, respectively. Thus it never applies a primitive selection to a noncycle or a nonboundary.

Step 5 uses precisely the sequence-union clause of the leaf for the underlying homogeneous set of A_0; the maximum-stage argument proves its DG operations close. Step 6 is an elementary elementwise quotient argument: every target class already has a cycle in B_1, and a source class in the kernel has a representative in some B_n and its primitive in B_{n+1}. This proves injectivity and surjectivity in each degree directly; it uses no unrecorded cohomology/filtered-colimit theorem. All cited facts in steps 2–5 are statements of the opened nodes, not their proofs. Proof dependencies are exactly their union. Each step is shorter than 2000 characters; none hides a comparison or a standard lemma.

I checked the edge cases of the zero DG algebra, an acyclic unital DG algebra (where 1 can be a boundary and its primitive is adjoined at the next stage), d=0 with already countable A, unbounded grading in both directions, and uncountable underlying A with countable cohomology. The choice of representatives can include a representative of the zero class; no nonzero or nonempty seed is required because zeros and the unit are adjoined separately. The construction does not require H(B_n) to inject into H(A) at any finite stage; killing those kernels at the next stage is exactly what ensures injectivity in the union.

I checked delivery-errors B–E: no new-node schema issues, no duplicate creation, no clause moved to a child node, no unproved closure fact, and no new hypotheses. The statement, source, created metadata and inherited blueprint fields are unchanged. The recorded Mathlib searches were run through msearch.py, with a second semantic phrasing; their actual log entries are included alongside the inherited searches. No Lean was written or compiled, no git command was run in the read clone, and only the sandbox was written.

## Unfinished work

None in the split. Independent maintainer review remains part of the delivery process.
