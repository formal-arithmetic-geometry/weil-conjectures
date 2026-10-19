# lem-sf-proper-open-coefficient-refinement — NN

## Files written

- `dag/nodes/sec-six-functors/lem-sf-proper-open-coefficient-refinement.json`: statement, split; eight proof steps; Mathlib verdict no match. Existing statement, ancestry, source, inherited searches and other metadata retained.
- `citations.json`: a verbatim statement for every citation in every proof step.
- `searches.jsonl`: six searches run through the prescribed msearch command; all services answered. Their actual results were read and appended to the item, after its inherited searches.
- `report.md`: this report and signed review. `build_split.py` is a sandbox-only preparation script, not a delivery file.

## New nodes

None. Zero new Mathlib leaves. The existing DAG already contains the proper/open comparison normalization on injective representatives and the general tools needed to carry out the argument. No statement-only stand-in for this item's conclusion was created.

## Attachments

None. Searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the exact blueprint tag and coefficient/refinement terminology; also inspected the proper/open refinement modules under `SixFunctors/Etale/Derived/` and the open-immersion base-change module. The declarations there concern fixed coefficients and, in places, cartesian refinement squares. They do not give this B-linear coefficient square for the specified clopen-section comparison. No Lean was written or compiled. Upstream master is reference material only and was not used to claim a finished proof.

## WANTED

None. The needed source documents and all cited DAG statements are present.

## What was wrong or incomplete

The item was an unsplit statement, not a proof. Its specified maps and hypotheses are consistent, so its statement is unchanged. Tag 0GL6 asserts compatibility of scalar extension with compact support but does not spell out this equality of the normalized refinement arrows. The delivered proof is accordingly marked `proof_origin.by = agent`, with Stacks as the supporting source, not misrepresented as a verbatim proof from that remark.

I ruled out a tempting but invalid shortcut: the square $uj_1=j_2$ need not be cartesian. The correct cartesian square is the one defining $V=T_1\times_{T_2}X$; the additional component of $V$ is handled by the clopen-section projection. Another potential mismatch was that `lem-sf-open-tensor-normalization` and the strict-tower proper/open calculus are pro-etale statements: neither is used as an ordinary-etale theorem. The normalized finite ordinary-etale theorem `lem-cbc-proper-open-interchange-coherence` supplies the precise representative of the already specified alpha instead.

A boundedness shortcut was also avoided: the assumptions say that $K$ and $Q_XK$ are bounded below, not that $Q_{T_2}R_{u,A}I_{j_1,A}K$ is bounded below. The final Hom bijection is the unbounded derived adjunction from `def-kun-projection-formula-map`, whose statement explicitly supplies it. No proper coefficient comparison is assumed invertible.

## Blueprint and duplicate searches

Read the assigned chapter and unit records, the item's ancestry, and the current main-20261015 proof of `lem-coef-finite-exceptional`. The proof realizes its compact-support projection/transpose compatibility sentence and the proper-refinement issue exposed by step 7 of `lem-sf-compact-coefficient-composition`. It changes no chapter, unit, target or maintainer-owned binding.

Ran `tools/blueprint_refs.py ancestor lem-sf-proper-open-coefficient-refinement` and whole-blueprint searches for `proper open`, `clopen projection`, `extension scalars`, `proper refinement`, and `coefficient refinement`. Read the proper/open, open tensor, coefficient-change and clopen product candidates from the DAG, including `lem-sf-proper-open-tensor-compatibility`, `lem-sf-proper-open-projection-mate`, `lem-pur-etale-scalar-mate-projection`, `lem-sf-proper-open-comparison-site-normalization`, and `lem-cbc-strict-tower-proper-open-calculus`. None duplicates the item's statement; narrower or differently typed candidates were not substituted. No new node exists, so no new/existing pair requires a Not duplicates entry.

## Tool uses

The proof uses generic ordinary-etale and derived-category tools from other units. Each is declared in `split_report.tool_uses` for maintainer review, without setting maintainer-owned `tool_uses`. In particular the finite proper/open coherence theorem supplies a normalized representative, not a replacement route through another chapter; ringed-site tensor and K-flat results supply the scalar/open calculation; the clopen sheaf equivalence supplies componentwise equality detection. These are tools for the inherited compactification route, and are not pro-etale or constructible-category identifications.

## Review by NN

I read delivery-errors B through E in full and checked the actual item and all cited statements against those failure modes. I read Stacks `more-etale.tex`, Tag 0F7B (`lemma-shriek-proper-and-open`), especially its first proof paragraph; Tag 0F7I (`lemma-shriek-well-defined`), including its refinement construction; Tag 0GL6 (`remark-Rf-lower-shriek-change-of-rings`); and the proper/support composition statements, Tags 0F50 and 0F51. I also read `sites-cohomology.tex` Tags 06YS and 0G7E on K-flat resolutions and their pullbacks, and `sites-modules.tex` Tag 03DJ on exact extension by zero. No forbidden SGA source is cited. There are no new nodes requiring separate source justification.

For step 1 I opened the full definition `def-weil-pbc-proper-open-comparison` and `lem-weil-pbc-proper-open-section`. They provide exactly V, b, p, s and its clopen image. The separate cartesian square satisfies `cor-cbc-derived-extension-zero-base-change`, and `lem-cbc-extension-zero-composition` gives the b/s extension composition. The inverse-image exactness and extension exactness statements justify termwise descent, and the localization universal property justifies descending the natural identifications. No cartesianness is inferred for the original refinement square.

For step 2 I opened `lem-weil-pbc-etale-sheaf-clopen-product`: it states an equivalence of abelian sheaf categories, not already an equivalence of module derived categories. The proof explicitly extends it by componentwise module actions, complexes and localization, using `lem-weil-pbc-localization-universal-property`; it does not silently cite a stronger theorem. The extension-by-zero definition and its adjunction identify the open unit on actual open test objects. That unit stays invertible termwise, giving full faithfulness of b-extension on derived categories. This proves detection of actual derived maps, not just equality after cohomology or geometric stalks. These few-line consequences are kept as an elementary step rather than made into new nodes.

For step 3 I read `lem-pc-kflat-resolution`, `lem-weil-pbc-ringed-slice-extension-tensor`, `lem-weil-pbc-left-adjoint-preserves-colimits`, both exactness statements, `lem-pur-derived-change-of-rings`, and the explicit open adjunction. The tensor identity is an ordinary sheaf tensor identity; preservation of the direct sums in total complexes is supplied by the left-adjoint colimit theorem. The proof writes the acyclic-test argument showing a_! preserves K-flat representatives and flat terms, so it does not assume flatness of B. The resulting identification is B-linear, sends the same summand to the same summand, and its inverse has exactly the unit transpose fixed in the item.

For step 4 the K-flat pullback statement has no flatness hypothesis on the coefficient map. The tensor comparison node, tensor-descent node and module inverse-image composition node say exactly what is used: compute on flat K-flat representatives and use the canonical module pullback composition. The two sheaf maps agree on pure tensors with their B-action intact, so the proof never relies on a forgetful functor on derived categories being faithful. Descent carries the actual equal chain maps to equal derived maps. This checks the coherence needed for the first component of the projection, rather than declaring that it transports automatically.

For step 5 I opened `lem-cbc-proper-open-interchange-coherence` and checked its explicit sentence that the refinement specialization equals alpha of the specified definition. Its injective representative is the one used in the proof. The support-composition node identifies the first sheaf map by the same underlying sections. Finally `def-kun-projection-formula-map` explicitly specifies the derived Hom bijection as termwise adjunction on an injective target; it is not being cited merely for a projection-formula isomorphism. This identifies the proper-adjunction transpose with identity on the clopen section and zero on its complement. Finiteness and commutativity of both coefficient rings and the two required D+ inputs are present.

Step 6 is the elementary deduction from steps 1–5: in the two-component category the projection is (1,0); gluing pairs of K-flat resolutions shows coefficient extension acts componentwise. On the first component the named maps are the identity by step 4, and the second-component target is zero. This is a calculation of morphisms in a product derived category, not an unjustified open-local test for arbitrary derived morphisms on a cover.

For steps 7–8 the cited unbounded adjunction gives an injective Hom bijection. I checked every domain: transposition of the left side gives beta_1 Q(t_A) lambda, and transposition of the right gives t_B L_u(beta_2). Step 7 uses the specified counit definition of chi and naturality of lambda; step 8 uses the same counit on alpha_B. Step 6 is therefore exactly the needed equality. Neither chi nor alpha is cancelled using an unproved isomorphism.

Small cases checked: u=identity and j_1=j_2 (the maps reduce to the normalized open tensor comparison); the cartesian refinement case (C empty); a genuinely noncartesian case T_2=X, T_1=X disjoint-union X with the fold proper map and j_1 the first component (the transpose is (1,0)); X empty; the identity coefficient map; and the nonflat map Z/4 to F_2 with K=A in degree zero. The latter still has bounded-below coefficient extension and uses no flatness argument. For K=F_2 the same ring map can give unbounded Tor, explaining why no claim removing the Q_XK boundedness assumption is made. Empty components and zero objects make both sides zero. All cited statements' hypotheses match these uses.

There are no new unsplit nodes, no hidden existence constructions, no statement dispute, and no unused new imports. Every non-elementary input is an existing cited statement. I inspected all eight steps for hidden lemmas; none is over 2000 characters. The tensor-representative and adjunction calculations are written explicitly, and the two short componentwise consequences are kept in the proof instead of generating duplicate nodes. citations.json contains the actual statements read, verbatim, for each citation.

## Unfinished work

None in this one-level split. Existing cited unsplit facts remain their own assigned DAG items. Server dry-run diagnostics and the final delivery result are recorded after validation below.
