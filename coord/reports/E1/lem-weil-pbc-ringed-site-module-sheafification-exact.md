# Stage 1 report: lem-weil-pbc-ringed-site-module-sheafification-exact

## Files written

- `dag/nodes/sec-curve-estimates/lem-weil-pbc-ringed-site-module-sheafification-exact.json`: filled the three proof steps, dependencies, Stacks provenance, blueprint realization, and `status: split`.
- `dag/nodes/sec-curve-estimates/lem-weil-pbc-ringed-site-module-sheafification-finite-limits.json`: new statement-only child; Mathlib search found only a specialization with extra site hypotheses, so the verdict is `generalization` rather than a Mathlib leaf.
- `citations.json`: verbatim statement quotations for every cited node in steps 1 and 2.

## Attachments

None. I searched both audited source branches for the item id, its title, and module-sheafification declarations; no sorry-free declaration states the item exactly.

## WANTED

None. The cited Stacks source is the available `literature/stacks-project/sites-modules.tex`, Section Tag 03CX and Lemmas Tags 03CN and 03CO.

## Corrections and checks

The imported item was a statement-only node with the correct arbitrary ringed-site hypotheses but no proof split. I searched the DAG for the exact tag and for finite-limit/finite-colimit sheafification statements. The existing exactness nodes cover constant-ring presheaves or scheme sites, so neither states this arbitrary ringed-site clause. I therefore created only the strictly smaller finite-limit child, rather than duplicating a stronger existing node or moving the whole target into a child.

Step 1 cites the child for the finite-limit conclusion and the module-sheafification definition to identify the functor. Step 2 cites that same definition for the left adjunction and writes the hom-set argument that a left adjoint preserves colimits. Step 3 is the one-line categorical definition of exactness from the two preservation conclusions and uses no hidden theorem. I read the statements of both cited nodes verbatim when writing `citations.json`; the quotes are exact substrings. The finite-limit child was searched with LeanSearch, LeanFinder, and a direct Mathlib grep. Mathlib's `PresheafOfModules.instPreservesFiniteLimitsSheafOfModulesSheafification` at `Mathlib/Algebra/Category/ModuleCat/Presheaf/Sheafification.lean:190` requires explicit `HasSheafify` and `WEqualsLocallyBijective` assumptions, so it was recorded as a generalization and not attached to the arbitrary-site statement.

I tested the statement on the one-object site with only the identity covering: module sheafification is the identity and both preservation claims are immediate. I also checked the zero presheaf and identity morphism cases. No Lean was written or compiled, as required for Stage 1.

## Review by E1

I reviewed `literature/stacks-project/sites-modules.tex`, Section 03CX, and the cited 03CN/03CO lemmas against the imported target. I checked the target's source and blueprint ancestor `lem-sc-ga-cohomology`, and verified that the new child's `from.node` and `via` reproduce the target's blueprint route. For step 1, the child statement literally says that the module sheafification preserves finite limits, and the cited definition literally identifies the same functor and its universal property. For step 2, the definition literally says that this functor is left adjoint to inclusion; the remaining colimit argument is the standard hom-set calculation written in the step. Step 3 only unfolds the definition of an exact functor between the abelian categories named in the item. I checked all statement dependencies exist and are unmerged, checked that every citation quote is verbatim, and tested the trivial one-object site and zero-object cases. I corrected malformed TeX escapes in the proof text and made the child's blueprint `via` list include the complete item route.

## Could not finish

The finite-limit child remains `unsplit` for a later stage-1 worker. No Lean declaration or compiled proof was required or available in this stage.
