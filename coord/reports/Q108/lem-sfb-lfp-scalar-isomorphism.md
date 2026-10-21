# Worker report

Group Q108, item lem-sfb-lfp-scalar-isomorphism, stage 1, 2026-10-21.

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-lfp-scalar-isomorphism.json — existing statement, now split into four proof steps; no Mathlib match.
- citations.json — one verbatim statement excerpt for every citation in every proof step.
- report.md — this report.

No new nodes and no new Mathlib leaves. searches.jsonl is the unedited search-command log; write_split.py is a sandbox-only helper for reproducibly writing the JSON and citations.

## Attachments

None. I searched WeilConjectures for the exact blueprint tag and the local/finite-presentation notions. CategoryTheory.Mod.IsFinitelyPresented.comap (CategoryTheory/ModuleObjects/FinitelyPresentedComap.lean:63) proves preservation of finite presentation. AlgebraicGeometry.ProEtale.IsLocallyFinitelyPresented.comap (SixFunctors/ProEtale/ModuleObject/LowerShriek/Constructible.lean:83) proves preservation of local finite presentation. Their statements do not give reflection, extension, or the specified-cover-and-ranks assertion, so neither is an attachment of this item. The coefficient-specific isLocallyFinitelyPresented_mapMod_iff is not the arbitrary ring-object assertion either.

## WANTED

None. The argument follows available blueprint scalar-change and local-presentation definitions, with its extra assembly explicitly marked as agent-written. No external document or SGA is used.

## Findings and changes

The item was unsplit, with an empty proof. Its statement is correct and remains byte-for-byte unchanged. I retained its original citations, metadata, blueprint ancestry, and earlier Mathlib searches. New searches from this session are appended as actually logged. One Loogle query used the unknown unqualified identifier IsIso; its rejection is recorded as unavailable and I corrected it with the separate CategoryTheory.Mod.comap query. Two semantic phrasings, LeanSearch, Loogle, and both whole-Mathlib and targeted grep searches found ordinary Module.Presentation, SheafOfModules finite-presentation predicates, and the restriction functor, without a direct theorem about the internal module objects used here. The fixed-ring Presentation.ofIsIso result does not change the coefficient ring; using SheafOfModules would also require an equivalence with the internal encoding, so these are not one-line specializations.

The proof uses the existing lem-sfb-internal-extension-finite-presentation, whose statement explicitly includes preservation of both finite ranks and the conjugated presentation map. The similarly named lem-sfb-internal-scalar-extension-finite-presentation has a less explicit statement: I did not take the rank calculation from its proof. Neither existing node is edited.

## Not duplicates

No new nodes were created. The item is local, two-sided, and also treats restriction and extension along an isomorphism; lem-sfb-internal-extension-finite-presentation is a global, one-way extension result for an arbitrary morphism. The latter supplies the smaller calculation used in step 2 rather than restating the item.

## Review by Q108

I read the current chapter and unit records, the main-20261015 open-lower-shriek preservation proof (the phrase about each stratum being locally finitely presented and its restriction identifications), the change-of-scalars section and proof, and the local-finite-presentation definition. The parent proof needs coefficient relabelling, not a different constructibility or purity route. The four steps give that relabelling directly, with no chapter/unit changes. There are no new nodes whose sources need separate review.

In step 1 I checked sk-def-sfb-sheaf-tensor really states symmetric closed structure and preservation of colimits by tensoring. I added def-weil-pbc-proetale-site and lem-sfb-grothendieck-sheafification to justify the small-site abelian sheaf category, and def-sp-abelian to justify kernels/cokernels of differences and hence equalizers/coequalizers. This avoids assuming the existence hypotheses of change-of-scalars clause 5 without a citation. Ab is the Grothendieck abelian coefficient example expressly allowed by the sheaf-tensor setup. Both rings are commutative, so clause 5 applies in both directions. I checked the direction carefully: extension along psi = phi inverse is restriction along phi. The identity underlying double restriction follows by composing the actions with phi tensor identity and psi tensor identity; it is not an assertion about pointwise exactness. Finally, the finite-presentation definition explicitly uses an isomorphism to a cokernel, so composing that isomorphism does not change the ranks.

In step 2 I opened lem-sfb-internal-extension-finite-presentation and verified that its statement, not merely its proof, supplies the same m,n and conjugated map after extension. Apply it first to psi and then to phi. In reflection, the second application is to the R-module Res_phi N, and its output is an S-module, identified with N by the inverse restriction calculation. All hypotheses are satisfied on any scheme: commutative internal rings, a ring-object morphism, and the sheaf tensor product. There is no flatness assumption. This node is a generic tool from the qbar-colimit unit; split_report.tool_uses declares why the current unit has no replacement for this algebraic calculation.

In step 3 I opened def-sfb-finite-upper-star-monoidal, def-sfb-comap-mapmod-square and def-sfb-locally-finitely-presented. The first really asserts strong monoidality for pullbacks with these coefficients. The second is the general square, rather than a coefficient-specific comparison, so it applies with both vertical maps identity and the lower horizontal arrow u_i^* phi. Its natural isomorphism compares exactly mapMod(u_i^*) Res_phi N and Res_(u_i^* phi) mapMod(u_i^*) N. I checked the source and target rings match. Functoriality explicitly proves u_i^* phi invertible. Step 2 is applied on U_i, not to some unspecified global restriction. Composing with this comparison is enough to preserve each presentation's ranks. The cited local-presentation definition quantifies over just these mapMod restrictions. The family is fixed throughout: neither a refinement nor local finite presentation inside U_i is substituted for the required finite presentation on U_i.

In step 4 I checked the extension isomorphism in change-of-scalars clause 5 has direction Ext_phi isomorphic to Res_psi. Step 3 is applied to psi and the original R-module M. A functor preserves an isomorphism because it preserves composition and identities, so applying each local mapMod to the global comparison is enough. Finite presentation under module isomorphism is the elementary composition of the last presentation isomorphism from the definition. This step adds no tensor-base-change assertion and needs no additional hidden comparison lemma.

I checked B–E against this delivery: no new/duplicate/clause nodes, no source used in place of proof steps, all non-elementary facts cited by a node whose statement supplies them, and no reliance on a cited proof's internal construction. citations.json was built from the actual statements, including clause 5 and the explicit ranks clause, so every quote is a verbatim substring. Steps 1–3 are non-elementary applications of the cited results; only the final assembly is marked elementary. Each step is less than 2000 characters. I tested zero rings/modules, m=0, n=0, the identity ring isomorphism, the empty scheme and an empty cover when it is a cover. The calculations use no division, nonzero rank, nonempty cover, noetherian assumption, quasi-compactness, or flatness; empty families leave the same vacuous local conditions on each side. Nonempty covers are neither enlarged nor shrunk. The two generic tools (abelian sheaves and same-rank scalar extension) are recorded in split_report; neither changes the unit's proof route.

## Unfinished work

None in the stage-1 split. The existing dependencies retain their own current stage statuses. No Lean was written or compiled. Final mechanical validation and delivery are performed with the required server-side delivery command.
