# Stage-1 worker report

## Files written

- `dag/nodes/sec-picard-framework/lem-sc-point-tangent-cotangent-surjective.json`: split item.
- `dag/nodes/sec-picard-framework/lem-sc-rational-tangent-cotangent-duality.json`: statement-only, no Mathlib match.
- `dag/nodes/sec-picard-framework/lem-sc-dual-map-injective-iff-surjective.json`: statement-only Mathlib leaf, `LinearMap.dualMap_injective_iff`.
- `citations.json`: verbatim statement excerpts for both proof citations.

## Attachments

None. No declaration in the Lean source states the item exactly.

## WANTED

- `literature/stacks-project/varieties.tex`, Tags 0B2C and 0B2E, for `lem-sc-point-tangent-cotangent-surjective` and `lem-sc-rational-tangent-cotangent-duality`. The repository copy lacks the regenerated Stacks source; I read the public Stacks pages for both tags.

## Problems found

The item had no proof. Its existing `source` gives the tangent-space identification but does not explicitly mention naturality, which the proof needs. I made that precise in a separate statement. The existing locally finite type hypothesis is unnecessary for this linear-algebra argument, but is true in the application and was retained. The blueprint's point-and-tangent argument is consistent with this split.

## Unfinished work

None for this one-level split. The new duality node remains unsplit for a later item, and the Stacks source file needs regeneration by the maintainer.

## Review by M1

I read Stacks Varieties Tag 0B2E, `lemma-tangent-space-rational-point`, and Tag 0B2C, the definition by dual-number lifts. Tag 0B2E states the canonical isomorphism with the dual of the maximal-ideal quotient when the point and base have equal residue fields. With the base `Spec k`, both points have residue field `k`, so its denominator has no base-maximal-ideal term. The dual-number definition makes the map induced by `f` composition with the local-ring map, which is the dual of the map on maximal-ideal quotients. This is precisely the new duality node's statement, with no finite-type assumption. The linear-algebra leaf states the iff for arbitrary vector spaces over a field, exactly as Mathlib `LinearMap.dualMap_injective_iff` does at `Mathlib/LinearAlgebra/Dual/Lemmas.lean:928-936`; it needs no finite-dimensionality.

In step 1 I checked the new duality node's statement itself: the citation supplies both the canonical tangent/cotangent identifications and the specific functorial equality used. Step 2 takes the iff from the Mathlib leaf, so it does not infer surjectivity from a one-way theorem. The input hypotheses `f` a map over `k`, `y=f(x)`, and both residue fields equal to `k` meet the duality node's hypotheses. Its resulting $u$ is $k$-linear because the local maps respect the $k$-algebra structures. The Mathlib leaf applies with $V=\\mathfrak m_y/\\mathfrak m_y^2$ and $W=\\mathfrak m_x/\\mathfrak m_x^2$. Its statement cites `def-wf-lie-algebra-derivation` only for the dual-map notation explicitly used in that node's tangent-space paragraph.

Before adding nodes I searched the whole DAG for the tag and tangent/cotangent language, the whole blueprint with `tools/blueprint_refs.py search`, and the Lean source for the item id and related declarations. `def-wf-lie-algebra-derivation` overlaps only in the finite-type affine setting; it does not state the general scheme-level naturality used here. LeanSearch returned HTTP 500. Loogle, LeanFinder and source grep found no Mathlib scheme-level match; Loogle and direct source reading identified the linear-duality leaf. Both new statements survive small cases: for `X=Y=Spec k` the cotangent spaces vanish; for `A^1_k` under `t\\mapsto t^2` at zero both maps are zero, so neither injectivity nor surjectivity is incorrectly inferred; for the identity on `A^1_k` both maps are identities. I corrected the missing naturality and proof citations; I found no false statement in the item or in the two new nodes.
