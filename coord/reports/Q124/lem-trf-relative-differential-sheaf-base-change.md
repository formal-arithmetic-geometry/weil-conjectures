# Worker report: lem-trf-relative-differential-sheaf-base-change

## Files written

- dag/nodes/sec-trace-formula/lem-trf-relative-differential-sheaf-base-change.json: split the existing statement into six proof steps; Mathlib has ring base change and finite generation, but not the complete scheme-sheaf statement.
- citations.json: 19 verbatim statement citations indexed by proof step.
- report.md and searches.jsonl: report and actual search receipts.

No new nodes, no new Mathlib leaves, no Lean files, and no statement changes.

## Attachments

None. Searching WeilConjectures for the blueprint tag and relativeDifferentials found the relative differential sheaf, affine comparison maps and smooth-specific results. Modules/Differentials.lean even lists general quasi-coherence as a TODO; no project declaration gives all the clauses here. Existing affine comparison declarations are already represented by DAG nodes and are reused through those nodes.

## WANTED

None. All source arguments needed are in the local Stacks source. The inherited reference to coord/dag-sync.md points to an absent file; the dispatched brief supplies the current live read-only repository and required delivery mechanism.

## What was wrong or missing

The item was statement-only, not a proof. Stacks 01V0 says only that this is the sheafified version of ring base change, and 01V2 invokes the finite-generation criterion. The split writes out the affine objects, map on generators, overlap calculation, gluing and the finite-generator computation. The statement is correct as written, including arbitrary schemes, arbitrary base change and the absence of flatness or finite-presentation assumptions. No STATEMENT-DISPUTED correction was needed.

## Not duplicates

No new-node pairs: this delivery creates no nodes. Whole-DAG searches by the source tags 01V0, 01UT, 01V2, ring theorem 00RV and differential/base-change concepts found the already existing ring-base-change leaf, affine pullback and affine differential section nodes. Blueprint searches for differential, Kähler, 01V0, 01V2, base-change-differentials and finite-type-differentials found no blueprint node stating the complete item; the differential-related hits concern smooth curves, tangent bundles or projective space. The item's same_as remains empty. Its nearest ancestor is lem-trf-local-term-locality, and the inherited from.place specifies the nodal-family first-Fitting formation argument in that ancestor's alteration reduction. The chapter and unit route are preserved.

## Review by Q124

I read the chapter sec-trace-formula and unit sk-i-curve-zero, the three route levels of SETUP.md and GOAL.md. This item supplies a generic scheme calculation inside the nodal alteration branch of the existing normal-cone route; it does not replace a unit step. I read local morphisms.tex at lemma-differentials-affine (01UT), the discussion of quasi-coherence, lemma-functoriality-differentials (01UV), lemma-base-change-differentials (01V0) and lemma-finite-type-differentials (01V2). I also read algebra.tex at the universal module construction and universal property (07BK/00RO), ring base change (00RV), and finite generation (00RZ); schemes.tex at affine pullback (01I9) and quasi-coherent affine reconstruction (01IA); properties.tex at the finite-type criterion (01PB); and sheaves.tex at gluing maps (04TN). There are no new-node sources to audit.

Step 1 uses exactly the affine-associated-module clause of def-sc-relative-differential-sheaf and the affine-local definition in pqf-def-coherent. Thus quasi-coherence follows from the actual definition used in this DAG, without assuming a theorem from a definition node that does not state it. The argument applies to arbitrary f and f'.

Step 2 uses def-pc-fibre-product only for its universal property. The affine tensor-ring identification and both projection maps come from lem-weil-pbc-fibre-product-affine-spectra. I checked that lemma allows arbitrary commutative rings. The sheaf models of the differentials come from def-sc-relative-differential-sheaf; the actual pullback isomorphism, including its value on the pullback unit, comes from lem-weil-pbc-associated-module-pullback. I checked its global-ring hypotheses on the affine morphism W -> U. It is not applied to an arbitrary nonaffine base with an unjustified tilde equivalence.

Step 3 uses the S'-linear version explicitly present in lem-weil-pbc-kahler-differentials-base-change, with S=A and S'=R' tensor_R A; it is not merely an R'-linear identification. The sheafification of the module isomorphism and inverse uses the functoriality in lem-weil-pbc-affine-tilde-gamma-adjunction. Neither statement requires flatness. I read the Mathlib tensorKaehlerEquiv and tensorKaehlerEquivBase sources returned by the searches; these explain the existing ring leaf but are insufficient for attaching the item.

Step 4 uses the principal-open localization statement of lem-weil-pbc-spec-module-tilde-sections, the actual defining relations and quotient generators in def-weil-pbc-kahler-differentials, compatible local derivations from def-sc-relative-differential-sheaf, and the tensor construction in def-pc-module-pullback. The quotient rule is written explicitly, so the restriction compatibility does not conceal an appeal to a missing naturality theorem. Equality is checked on pulled-back local differential generators; changing a base chart does not change the derivation of a local function. Intersections of affine opens are never assumed affine. This step is elementary relative to the cited constructions: apply the quotient rule to each generator and use linearity.

Step 5 uses clause (1), gluing morphisms, of lem-weil-pbc-glue-sheaves-of-modules, not its object-descent clause. Its hypothesis is precisely the overlap equality established in step 4. The separate lemma lem-weil-pbc-sheaf-isomorphism-local-open-cover says that a given sheaf morphism which is locally invertible is globally invertible, exactly what is taken from it. Uniqueness follows on the same generators; the affine map is consequently the canonical map of the statement.

Step 6 uses the covering definition in def-weil-finite-type-morphism, so the chosen A/R are finitely generated by hypothesis, without needing finite generation on every arbitrary affine chart. I expanded the monomial Leibniz calculation from the relations in def-weil-pbc-kahler-differentials; the quotient presentation then proves finite generation, so no additional lemma is hidden. lem-sc-relative-differentials-affine-sections identifies those modules with the actual sheaf sections. Clause (c) of lem-weil-pbc-quasi-coherent-finite-type-affine converts that affine covering into finite type of the sheaf. Finally lem-weil-pbc-module-pullback-finite-type applies to p with the already proved finite-type sheaf, and c_g transfers the property to the target. This avoids silently assuming the stability of locally finite type under base change without a cited node.

I checked the B--E return cases against the result: every citation was opened and its statement copied verbatim into citations.json; all uses occur in proof_deps; the statement introduces all objects; all new work is a proof step rather than a restatement in a new node; no cycles or new definitions are introduced. All six steps are below 2000 characters. The empty scheme/zero ring makes the local assertions vacuous or zero; identity base change gives the identity on da; a nonflat quotient R -> R/I is allowed by the ring theorem; n=0 algebra generators give the zero differential module. Rings with infinitely many relations cause no problem because the finite-type proof uses generators, not finite presentation. Off-unit sheaf tools are declared in split_report.tool_uses for independent maintainer review.

## What could not be finished

Nothing mathematical remains in this one-level split. The required server dry run and direct delivery follow this report.
