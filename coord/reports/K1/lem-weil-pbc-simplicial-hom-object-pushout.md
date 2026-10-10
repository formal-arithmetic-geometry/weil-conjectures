Files written:

- `dag/nodes/sec-curve-estimates/lem-weil-pbc-simplicial-hom-object-pushout.json`: statement node, split proof, no new nodes; Mathlib search verdict remains no match.

Attachments:

- None. No sorry-free declaration in slopmaster2 states this item.

WANTED:

- None.

What was checked or corrected:

- The item statement was checked against Stacks `simplicial.tex`, Lemma 017N (`lemma-hom-from-coprod`) and its use in `hypercovering.tex`, Lemma 01GM. It is the degree-0 Hom-object formulation, with the empty-base case explicitly retained.
- The source proof first constructs the fibre product of the Hom objects, then identifies maps into it by a sequence of representing-functor equalities. I wrote the degree-0 version as a natural bijection between D-families and compatible B/C-families, followed by the representing and fibre-product universal properties.
- The family-gluing step uses the pushout equation `i \\circ p = j \\circ q` and the simplicial-set pushout universal property degree by degree; this checks both existence and uniqueness and preserves all simplicial operator equations.
- The Hom-object representing property is cited through `def-weil-pbc-simplicial-hom-object` and `def-weil-pbc-representing-object`; existence and finite limits in `SR(X)` are supplied by the reviewed nodes `lem-weil-pbc-semi-representable-finite-limits` and `def-weil-pbc-semi-representable-object`.
- The empty-base case was checked separately: the compatibility condition is vacuous, the simplicial pushout is a coproduct, and the product is the fibre product over the final object supplied by the finite-limits node.
- I searched the DAG and blueprint for an existing node covering the needed pushout/family identity and found none. The existing Mathlib searches for the item report no direct Hom-object result; no new Mathlib or unsplit node is required because the degree-0 argument is exactly the source's universal-property calculation.

## Review by K1

I read Stacks `simplicial.tex` Lemma 017N from its statement through the proof (the Hom-object existence invocation, the representing-functor equalities, and the termwise pushout argument), and `hypercovering.tex` Lemma 01GM where the result is applied to the new simplex and to the empty boundary. I also checked the cited DAG nodes: `def-weil-pbc-simplicial-hom-object` supplies the universal families and restriction maps; `def-weil-pbc-representing-object` supplies the bijection between morphisms and families; `def-weil-pbc-simplicial-set` supplies simplicial sets, morphisms, and pushouts; and `lem-weil-pbc-semi-representable-finite-limits` together with `def-weil-pbc-semi-representable-object` supplies the fibre products, products, and final object in `SR(X)`. Step 1 uses the finite-limit construction to form the candidate pullback. Step 2 checks both directions of the family correspondence, including compatibility on A and all simplicial operators. Step 3 transports that correspondence through the representing properties and compares it with the categorical pullback universal property, yielding the required unique isomorphism with matching projections. Step 4 repeats the argument when A is empty, verifies the vacuous compatibility condition and coproduct pushout, and identifies the product as a pullback over the final object. I checked the admissibility hypotheses: all H-objects invoked in part (a) are admissible by the statement, while part (b) never invokes H(A). The Mathlib and blueprint searches found no existing statement of this Hom-object pushout result, so the split adds no duplicate node.
