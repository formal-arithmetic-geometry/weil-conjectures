1. files written

- `dag/nodes/sec-picard-framework/lem-sc-global-sections-left-exact.json`: item split into three proof steps; no new nodes.

2. attachments

None. The slopmaster2 source contains no declaration tagged `(blueprint: lem-sc-global-sections-left-exact)` and no sorry-free declaration with this statement.

3. WANTED:

WANTED: `literature/stacks-project/cohomology.tex`, Cohomology of Sheaves, Lemma Tag 01EZ, for `lem-sc-global-sections-left-exact`; the checkout is not present in this repository, so the proof origin records the cited Stacks place and the proof is written explicitly.

4. what was wrong in the node, blueprint, or brief

The imported node had an empty proof despite being the left-exactness input for the functoriality definition. I checked the existing definition node `def-weil-sheaf-of-modules-category`; its statement explicitly supplies an abelian module category and sectionwise kernels. The blueprint ancestor is `thm-sc-p1-duality`, and the item’s existing `from.place` identifies the functoriality step. No existing DAG node states the complete global-sections theorem, and no exact Lean declaration was found.

5. what I could not finish, and why

No mathematical part was left unfinished. Mathlib searches returned evaluation finite-limit generalizations but no exact additive left-exact global-sections declaration; LeanSearch was unavailable and is recorded as such. The required source text is absent locally, so the Stacks citation could not be opened directly.

## Review by C1

I checked the item statement against its source citation (Stacks Cohomology Tag 01EZ) and against the blueprint proof use in `thm-sc-p1-duality`. Step 1 cites `def-weil-sheaf-of-modules-category`, whose statement says the category is abelian and kernels are computed sectionwise; this gives the displayed equality of sections of a kernel. Step 2 uses that same exact clause and verifies the hypotheses for an arbitrary module morphism, so evaluation at the whole scheme preserves kernels. Step 3 uses the definition node’s clause that module morphism components are homomorphisms of abelian groups, together with `def-sp-left-exact-additive`, whose statement defines left exactness as additivity plus kernel preservation. The elementary portions are only the pointwise identification of the induced group maps and the final application of the definition.

I searched the whole DAG and blueprint for an existing global-sections left-exact statement and found no duplicate. I tested the statement on the empty scheme, where global sections is the zero group, and on `Spec k`, where it is the ordinary module evaluation and is exact. I also checked the Mathlib search hits: finite-limit preservation of sheaf-module evaluation is a useful generalization, but it does not state the required functor to `Ab`; the unavailable LeanSearch service is recorded verbatim in the node.
