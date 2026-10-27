# Q06 stage-1 report: lem-pur-relative-kummer-site-normalization

## Files written

- dag/nodes/sec-smooth-purity/lem-pur-relative-kummer-site-normalization.json: existing statement, now split in six steps; Mathlib verdict no match. Its statement is unchanged. Added lem-amb-kummer-any-base to statement dependencies to make arbitrary-base Kummer exactness explicit.
- citations.json: one verbatim statement quotation per cited node per step.
- report.md: this report. Existing searches.jsonl was retained and its five actual search records reused.

No new nodes; no new Mathlib leaves; no Lean files or compiler invocations.

## Attachments

None. The blueprint-id search in lean/WeilConjectures gives no declaration for this item. Searches for Kummer and comparison led to the existing EtaleCohomology/Purity/Smooth/KummerBoundaryComparison.lean and GmRelativeKummer.lean, and the ProEtale/Comparison sources. These contain useful partial interfaces but no project declaration proving every clause, including arbitrary schemes, the scalar-forgetting normalization, edge sections and the specified pro-etale exchange. In particular an etale Kummer theorem does not state this combined etale/pro-etale comparison assertion.

## WANTED

None. All sources used are available locally.

## Problems found and changes

The item was statement-only, not a completed split. Its statement already insists on the actual comparison maps, rather than unrelated isomorphisms, so the proof now checks their normalizations explicitly. The historical def-sc-kummer-sequence statement mentions curves; its current blueprint_update permits arbitrary schemes, and the proof separately cites lem-amb-kummer-any-base for exactness on every k-scheme. This avoids applying curve hypotheses to arbitrary T. No statement dispute or route change was necessary.

The datum's special coefficient ring A_{E,n} and its twist identification occur only in the last specialization. None of its special ramification assumptions is used as an input for arbitrary finite free A. For general A the sheaf on the pro-etale site is, as the item says, the comparison pullback L^p=C_TL^e. The coefficient identifications are those stipulated in the item. The proof of arbitrary pullback for roots is the elementary factorization into distinct roots over k, not an appeal to a coefficient theorem restricted to finite-type schemes.

I searched the whole DAG for scalar forgetting, cohomology pullback, edge comparisons, mate units and exchange cubes, and read the relevant statements before using them. Blueprint ancestor gives prop-pur-gm-relative-kummer. The whole-blueprint searches for comparison, scalar forgetting, Kummer, and module/cohomology found no second blueprint node stating this full normalization. Existing lem-pur-site-comparison-edge-section, lem-pur-mate-unit-compatibility, lem-pe-left-module-derived-evaluation-forget and lem-weil-pbc-coefficient-exchange-mates already supply the natural smaller facts; creating duplicates or clause nodes would add no mathematics.

## Not duplicates

No new nodes were created. Existing statements are cited directly. In particular the edge-section theorem is reused rather than repackaged as a Kummer-only lemma, and the categorical coefficient-exchange theorem is used rather than introducing a special comparison cube.

## Review by Q06

I read the item, the chapter and unit records, the current main-20261015 prop-pur-gm-relative-kummer proof, and the complete delivery-errors B–E checklist. The unit's route is preserved: this item implements the opening passage to the pro-etale site and the comparison aspect of Step 3; it does not replace the strict-local or affine-curve computations. I also read Stacks proetale.tex, Tag 099W (lemma-compare-cohomology) and Tag 09A6 (lemma-morphism-comparison); sites-cohomology.tex, Tag 072W (lemma-higher-direct-images) and Tag 03FD (lemma-cohomology-modules-abelian-agree); and categories.tex, Tag 0B65 (lemma-transformation-between-functors-and-adjoints). The additional normalization arguments are marked agent-written, not attributed verbatim to those tags. There are no new nodes whose sources need a separate review.

Step 1 uses the actual statements of lem-pe-left-module-derived-evaluation-forget (including its last compatibility with canonical global pullback), lem-pe-constant-left-module-inverse-image (including the forgotten-unit equation), lem-weil-pbc-comparison-global-cohomology (the precise derived-unit/final-evaluation definition), and lem-cbc-abelian-etale-proetale-cohomology-comparison (arbitrary abelian sheaves on arbitrary schemes). These statements supply both the scalar-forgetting identifications and equality of the specified maps. No claim that forgetting an injective module sheaf preserves injectivity is made: the generic theorem explicitly supplies evaluation acyclicity instead. A is finite because it is finite free over the finite ring Z/r; the ring is commutative by hypothesis. The usual small-site universes and enough injectives are those already fixed for these categories.

Step 2 uses lem-amb-kummer-any-base for exactness, with r invertible since ell is invertible in k; it uses lem-weil-pbc-site-cohomology-pullback clause (2) for coefficients, lem-weil-pbc-pullback-cohomology-long-exact-ladder clause (3) for the derived boundary, and lem-sc-p1-right-derived-triangle-connecting to identify this with the horseshoe-resolution boundary and lem-weil-pbc-right-derived-universal-delta-functor for naturality under the morphism of Kummer sequences. I wrote that morphism explicitly: local units pull back, r-th powers commute with pullback, and its root component is the canonical exponent identification. Primitive-root existence is cited from the closed node lem-sc-primitive-root; I read its blueprint statement and the two sorry-free project declarations it records. The factorization x^r-1 into pairwise comaximal factors over k justifies that identification even for disconnected, nonreduced or non-finite-type T. Tensor coordinates also check the coefficient map z -> z tensor 1. This is a short root calculation and not an unproved base-change lemma hidden behind a tag. There is no tensor product of G_m over Z/r.

Step 3 substitutes the definition of kappa^p in Step 1, then uses lem-weil-pbc-comparison-pullback and the composition and coefficient laws in lem-weil-pbc-site-cohomology-pullback. The commuting inverse-image square is part of the cited pullback-comparison statement. I checked the final paragraph of def-pur-affine-line-datum: it defines precisely this abelian comparison image of the same scalar Kummer class, so this proves equality with its actual kappa(t), without choosing an arbitrary generator or a different twist identification.

Step 4 reads the entire counit-mate normalization in lem-weil-pbc-comparison-direct-image-canonical-mate. The right mate is taken from alpha inverse, not alpha; I retained the factor Ra_p,*(alpha inverse) in the unit equation before making the specified identification. Substitution in the Mathlib-leaf statement lem-pur-mate-unit-compatibility gives exactly this equation. Both adjunctions are the constant-A module adjunctions in D+, and qcqs is imposed on a exactly where the direct-image isomorphism needs it.

Step 5 quotes lem-pur-site-comparison-edge-section with F=L_X^e, q=1 and the actual class. It states the needed equality of edge sections for this same canonical b and c; its proof is not being used as an extra conclusion. The q=1 comparison from Step 3 identifies the left class. Lem-sf-comparison-pullback-exact clause (3) gives natural cohomology-sheaf comparisons for arbitrary integer q, hence transports vanishings and maps. Invertibility of an already invertible arrow is preserved by applying a functor to both inverse equations and conjugating by the stated isomorphisms. Equality of the generator maps follows from equality on 1 and A-linearity. This step does not assert that an arbitrary abstract isomorphism preserves a generator.

Step 6 verifies every hypothesis of lem-weil-pbc-coefficient-exchange-mates: the two exchange counit equations come from sbc-def-base-change-map; the two push-comparison equations are exactly those in lem-weil-pbc-comparison-direct-image-canonical-mate; and the pull cube comes from the cartesian/composite compatibility in lem-weil-pbc-comparison-pullback. Its resulting square has the orientation in the item's displayed T C(Ex)=Ex S. Only a and a' need be qcqs, for their push comparisons. No finite-type condition is introduced for g or v, so Spec Omega with Omega of arbitrary transcendence degree is included. Invertibility follows by explicitly solving this equation for Ex_p, not from an existence-only comparison.

Small cases checked: q=0 agrees with the underived comparison unit; w=1 gives zero Kummer boundary and both sides zero; the identity morphism and identity square reduce to unit and composition identities; the empty scheme has zero cohomology groups and zero higher-image objects; disconnected and nonreduced bases still satisfy the distinct-root decomposition; the zero algebra, if allowed, gives zero module sheaves and the asserted identities and isomorphisms still hold. No algebraic closure of a finite-type residue field is required for the final geometric point. No proof step exceeds 2000 characters, and each non-elementary input is a cited node with a verbatim quote in citations.json. No new dependency reaches the item, so this split introduces no cycle.

The Mathlib searches retained from the interrupted attempt are all present in searches.jsonl, including the second LeanFinder phrasing. Their hits concern module forgetting, ordinary sheaf pullback/free modules, or formally etale algebras, rather than the normalized etale/pro-etale Kummer assertion. I checked the relevant Mathlib sheaf-module forgetting/continuous-pushforward interfaces; these do not state the item. No unrun search was added. Existing inherited searches in the item remain intact.

Generic tools from outside the unit are declared individually in split_report.tool_uses with the exact role each statement plays. They supply scalar and adjunction calculus, not replacements for the unit's geometric route. No maintainer-owned field, shared file, chapter or unit realization was changed.

## Unfinished work

None for this one-level split. The existing unsplit dependencies remain their own items. Verification and direct delivery use the required server tools; no local DAG checker is run.

## Verification

The first required server dry run exited successfully at 5e3344ccc38 (not pushed). Final citation review added the existing primitive-root theorem and the existing derived-boundary/connecting-convention statements in Step 2; no new node or search was needed. The final dry run is repeated after these changes before delivery.
