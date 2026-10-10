1. Files written:

- `dag/nodes/sec-proper-base-change/def-weil-pbc-sheaf-ext.json` — definition, no Mathlib match; marked split.

2. Attachments:

None. A search of both Lean source checkouts found no declaration tagged `(blueprint: def-weil-pbc-sheaf-ext)` or otherwise stating this definition.

3. WANTED:

None. The node cites the Stacks Project source `literature/stacks-project/cohomology.tex`, Tag 0BQP, and the existing internal-Hom source Tag 08DH.

4. Review findings and corrections:

The source definition was read in the item node and checked against the existing `def-pc-ext` split report, which identifies Tag 0BQP as the source of the sheaf Ext construction. I read each statement dependency: `def-pc-scheme` supplies schemes, `def-weil-sheaf-of-modules-category` supplies the module category, `def-weil-abstract-derived-category` supplies its derived category, `def-pur-derived-internal-hom` supplies the derived internal Hom and its well-definedness, and `def-weil-derived-cohomology-sheaves` supplies the cohomology sheaf. The statement uses each of those dependencies explicitly. Since this is a definition, it has no proof steps; consequently `citations.json` is the empty list and there are no hidden non-elementary proof facts to cite. I searched the whole DAG and blueprint for duplicate sheaf Ext statements and found none, so `blueprint.same_as` was corrected from `null` to `[]`. The item has no Lean declaration in either source checkout. The existing `import_flags: ["unreachable"]` and reviewed field were preserved.

5. What could not be finished:

Nothing. No new subordinate node was needed.

## Review by E1

I checked the definition's source and all five statement dependencies listed above. The source formula is exactly the cohomology sheaf `H^i(R Hom(K,L))` from Tag 0BQP, with the derived internal Hom supplied by Tag 08DH and the existing internal-Hom node. The module specialization `F[0], G[0]` and contravariant/covariant functoriality are part of the definition and require no separate proof step. Because the node is definition-only, there are no step citations or hypotheses beyond the explicitly introduced scheme, ringed sheaf category, derived category, and cohomology functor. I verified edge cases conceptually (`i=0` gives the degree-zero cohomology sheaf and the module specialization uses complexes concentrated in degree zero). I also corrected the blueprint duplicate field to the required empty list and marked the node split.
