Files written:

- `lem-pc-picard-functor-agrees-sc.json`: repaired statement and proof split; no Mathlib match.
- `lem-pc-fppf-affine-refinement.json`: repaired statement and source to Stacks Tag 021P.
- `lem-pc-fppf-affine-sheafification-restriction.json`: new statement-only comparison node; no Mathlib match.
- `citations.json`: verbatim citations for every item proof step.

Attachments: none.

WANTED: none.

The returned version used geometric integrality implicitly and treated the affine-site sheafification comparison as an uncited plus-construction argument. I added the missing geometric-integrality hypothesis and the dependency `lem-pc-fppf-affine-sheafification-restriction`, whose statement records the canonical restriction/sheafification comparison supplied by Stacks Tag 021V. The existing affine-refinement node is retained only as an ingredient of that Stacks result and is corrected to Tag 021P, including the finite index set in the statement.

## Source error (E7)

The imported item said only “smooth projective curve over $k$”, but `[def-sc-picard-functor]` requires the curve to be geometrically integral, and the right-hand functor is otherwise not defined. I changed the item statement and its dependencies to include `[def-pc-geometrically-irreducible]`; this is the same hypothesis used by the cited Picard/Jacobian results.

## Review by K1

I read the item blueprint and the project definitions `def-pc-picard-presheaf`, `def-pc-picard-functor`, `def-sc-picard-functor`, `def-pc-fppf-site`, and `def-pc-geometrically-irreducible`. The first proof step uses only the Picard-presheaf statement to identify the two presheaves on an affine object and their pullbacks. The second uses the new node’s exact statement: for the inclusion of affine objects, restriction of big-site fppf sheafification is canonically and functorially the affine-site sheafification. This is the content needed from Stacks 021V; the old refinement node is not cited by the item. The third step unfolds the two Picard-functor definitions and evaluates the canonical identification at `Spec(R)`.

For the new comparison node I searched the full DAG and blueprint for the statement and tag, then ran LeanFinder, Loogle, grep, and LeanSearch searches; only unrelated affine-Zariski results appeared, and LeanSearch was unavailable. For the refinement node I checked Tag 021P directly and corrected the former incorrect Tag 03WX source and omitted finiteness. I checked the edge cases `T = Spec(k)` and the identity covering: both sides use the same presheaf value and the comparison is canonical. Every citation quote is copied verbatim from its node statement, and the new hypothesis is carried in `stmt_deps` and named in the source-error section.

What could not be finished: the 021V comparison remains statement-only for the next stage because its proof is the nontrivial site/topos argument.

## Second reading by K1

- Item statement: checked against the blueprint node and Stacks Tag 021S context; geometric integrality is required by `def-sc-picard-functor`, so the repaired hypothesis is correct.
- Step 1: checked against `def-pc-picard-presheaf`; the affine restriction has the same values and pullbacks, and the step is elementary.
- Step 2: checked against the statement of `lem-pc-fppf-affine-sheafification-restriction` and Stacks Tag 021V; removed unsupported prose about cocontinuity/topos equivalence and retained exactly the cited sheafification comparison.
- Step 3: checked against `def-pc-picard-functor` and `def-sc-picard-functor`; unfolding both definitions and evaluating the canonical identification gives the claimed affine value.
- `lem-pc-fppf-affine-sheafification-restriction`: checked for self-contained hypotheses, definition-node dependencies, Tag 021V source, and recorded Mathlib searches; statement-only because the site/topos proof is nontrivial.
- `lem-pc-fppf-affine-refinement`: removed because it was not cited by any remaining step and was only an ingredient of the unproved comparison node.

Changes: deleted the unused affine-refinement node, tightened step 2 to match its cited node, and recorded these checks. Edge cases `T = Spec(k)` and the identity covering agree with the common presheaf description.
