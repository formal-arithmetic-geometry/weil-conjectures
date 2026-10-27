Files written:
- `dag/nodes/sec-six-functors-basics/lem-sfb-equivariant-module-sheafification-reflector.json`: statement split into five proof steps; no new nodes and therefore no Mathlib leaves.
- `citations.json`: verbatim citations for every node used by every proof step.

Attachments: none.

WANTED: an external reference stating the equivariant reflector in exactly this internal sheaf-of-groups/module form. The proof is agent-written from Stacks Tags 00WJ, 00WH, 00YR and 03CY.

The item was not already proved in the source repository: searching `lean/WeilConjectures` for the item tag and for equivariant sheafification found no declaration. The whole DAG and blueprint were searched for sheafification/action statements; existing ordinary module sheafification and sheafification-of-products nodes were reused. No new node is needed because every non-elementary ingredient is already stated by an existing node, while the action extension and equivariance checks are the item's assembly argument.

## Review by Q95

I read the item source and its inherited motivation in the six-functors blueprint, then read the statements of every cited node. Step 1 uses the existing module-sheafification interface for the underlying abelian sheaf and unit, the underlying-sets comparison, the finite-product preservation lemma, and the sheafification universal property; those statements provide exactly the product-unit and uniqueness facts used. Step 2 uses the same product comparison and universal property to extend the given action and proves uniqueness by its unit equation. Step 3 checks identity, associativity, additivity, scalar-linearity, and inverses after the presheaf unit; the module interface supplies the unit's linearity, and the product-preservation node supplies the required uniqueness. Step 4 applies the ordinary module-sheafification universal property to an equivariant map and compares the two action composites after the unit; the cited set-sheafification statement gives equality. Step 5 checks functoriality and the equivariant adjunction by the same uniqueness argument, and identifies the forgotten functor and unit with ordinary module sheafification.

I verified all hypotheses used in the cited statements: the site is small, the ring is a sheaf with trivial group action, the presheaf action is natural and module-linear, and the target is an equivariant module sheaf. I tested edge cases conceptually (trivial group, zero module, and identity action); all formulas reduce to ordinary module sheafification. The Mathlib searches recorded in `searches.jsonl` were run for the item: semantic searches returned only ordinary module sheafification declarations, Loogle and source grep found no equivariant reflector, so the item remains a project-level statement rather than a Mathlib leaf. I corrected the inherited unspecified blueprint place and supplied verbatim citations for every proof dependency.
