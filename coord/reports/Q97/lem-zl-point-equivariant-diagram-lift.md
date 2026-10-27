# Q97 — lem-zl-point-equivariant-diagram-lift

## Files written

- `dag/nodes/sec-deligne-laumon-general/lem-zl-point-equivariant-diagram-lift.json`: statement, split; the original statement and statement dependencies are retained. Eight proof steps give the lift explicitly. The new Mathlib searches find no match for this complete geometric assertion.
- No new nodes; no new Mathlib leaves. The proof reuses the existing point-heart equivalence, truncation theorem, Frobenius-transport theorems and scalar exactness leaf.
- `citations.json`: a verbatim statement extract for every use in every proof step.
- `searches.jsonl`: actual command-generated Q97 search log; preexisting Q36 searches in the item have been retained.
- `report.md`: this report. `write_split.py` is the sandbox-local script used to assemble the JSON; it is not a delivery node.

## Attachments

None. Searches of `lean/WeilConjectures/` for the item's blueprint tag, equivariant diagrams and point-heart/Frobenius names found no theorem asserting this item. `AlgebraicGeometry.Etale.pointFiberRationalEquivalence` in `PointFiberRational.lean` gives a derived equivalence, not this diagram lift with an exactly prescribed object, normalized Weil structures, exact quotients and coefficient comparisons. It is not an attachment for the item. No Lean file was written and no compiler was invoked.

## WANTED

None. The source of the item and the statements of all tools used are available locally. This categorical assembly is the worker's argument, marked `proof_origin.by = agent`; it is not attributed to an unwritten Stacks theorem.

## What was wrong or missing

The live item was statement-only and had no split or report in this sandbox. No released repair note exists for this item. The statement is valid; no statement correction or route change is made. The blueprint, `main-20261015/blueprint/sec-deligne-laumon-general/sk-i-dl-general-real/thm-zl-real-mixed-by-curves.proof.md`, paragraph 7, asserts a Jordan filtration on a zero-dimensional piece without writing the passage from an invariant vector-space flag to an actual filtration in the raw Weil heart. This item provides the diagram-lifting part of that passage. It does not reprove the point-heart equivalence or the invariant-flag theorem.

The two especially consequential details are the inverse point transport in the formula for the Weil structure, and using the actual prescribed object at the distinguished vertex. An arbitrary inverse-equivalence choice would yield only an isomorphic distinguished object. The construction instead chooses the other objects independently and recovers all relations by full faithfulness.

## What remains unfinished

Nothing within this item's one-level split. The existing unsplit `lem-zl-point-heart-finite-stage` remains its own work item. Its statement, rather than a proof sketch inside it, is what this split uses.

## Not duplicates

No new nodes are proposed. Whole-DAG and blueprint searches for the point-fibre, Frobenius and equivariant-diagram notions located the existing point-heart equivalence and transport nodes; they supply all non-elementary inputs. `tools/blueprint_refs.py ancestor` gives `thm-zl-real-mixed-by-curves` with the existing intermediate `lem-zl-point-weil-heart-flag`; the item's blueprint ancestry is retained. The blueprint search for `equivariant diagram` found no exact blueprint match. Point-fibre equivalence alone is a strictly smaller input, not a replacement statement for this item.

## Review by Q97

I read the current chapter and unit records, the three proof-route levels in SETUP.md, GOAL.md, the worker/stage-1 rules and both occurrences of delivery-errors B–E. The current unit's first step includes the dimension-zero Frobenius-eigenspace argument, and the current blueprint's paragraph 7 uses Jordan filtrations. The proof remains below that step. No SGA source or trace-route replacement is used. I read the statement of every cited node directly from its JSON, including the distinction between the derived point-fibre equivalence and the exact heart equivalence needed here.

Step 1 uses exactly the first paragraph of conclusions of `lem-zl-point-heart-finite-stage`: essential surjectivity gives objects, and fullness/faithfulness gives unique maps after choosing fibre identifications. Its hypotheses allow every finite E in the item and impose no extra condition on the linear automorphisms. I deliberately keep the prescribed M and fibre isomorphism as data rather than choosing an isomorphic replacement. The finite category has a chosen object, so the empty-index case is excluded by the item's own hypothesis, not by a new assumption.

In step 2, `prop-constructible-truncations` explicitly says automorphism pullback commutes with truncations; this puts T(M) in the heart before applying fullness. This is important: an exact equivalence of hearts alone would not prove that claim. `lem-weil-frobenius-cohomology-transport-iso` clause 1 says the specified point transport is invertible, for E as well as the other coefficients. Its general separated finite-type setup specializes to Spec k0. The exact heart equivalence then lifts b = a t^{-1} and its inverse t a^{-1}. I checked both inverse identities by their fibre images. The Weil-pair definition supplies exactly the single required isomorphism. The compatibility hypothesis at the distinguished vertex forces its lifted theta to equal theta_* by faithfulness.

Step 3 needs only fullness and faithfulness of the same equivalence. I checked the cancellation of the middle eta in a composition and the identity-arrow formula, so loops, parallel arrows, and arrows incident with the prescribed vertex introduce no extra consistency problem. This is a direct calculation, not a separate diagram-lifting existence lemma smuggled into a new node.

Step 4 uses clause 2 of `lem-weil-frobenius-point-transport-natural`, which states naturality for every morphism in the rational constructible category, not just integral arrows. It gives omega(Tf)t_i = t_j omega(f). Combining that with w a_i = a_j w gives the displayed four-term equality of images. Both sides are morphisms T(M_i) -> M_j between heart objects; faithfulness therefore applies. The morphism condition in `def-weil-weil-sheaf-complex` is precisely f theta_i = theta_j T(f), in this direction. I did not cite the transport definition for a naturality theorem it does not contain.

Step 5 uses the explicit preservation AND reflection of kernels, cokernels, zero objects and short exact sequences in `lem-zl-point-heart-finite-stage`. This is stronger than the derived equivalence alone, and proves the universal-property clause for cokernels. No exactness of a category of Weil complexes is assumed. The conclusion is exactly about the underlying heart as requested; the arrows are Weil-equivariant by step 4.

For step 6 I read the actual composite defining local Frobenius in `def-weil-local-frobenius-trace`. At Spec k0 and n=1 it is omega(theta) H^0(iota), with the identity pullback comparisons; multiplying the constructed b by t gives a. This step is elementary substitution of the cited definitions. The Weil-pair definition requires an invertible map but does not require a continuous profinite-group action. In rank one, any a in E^times works, even when its powers would not extend to a continuous Galois action. For a two-dimensional Jordan block with diagonal 1, the same inverse formula works; diagonalizability is never used. For dimension zero, the sole endomorphism of the zero object is its identity and is an automorphism, so all inverse and exactness statements still hold.

Step 7 uses the finite-coefficient/truncation compatibility in `prop-constructible-truncations` and the explicitly specified scalar/cohomology comparisons in `lem-zl-point-heart-finite-stage`. The transport naturality theorem's clause 2 expressly includes compatibility with finite scalar extension under the prescribed pullback comparison. I wrote that comparison alpha into the extended theta, used its inverse in the right direction, and chose eta_L by the specified sections comparison c. The formula for Frobenius then reduces to A tensor 1. This also verifies identities and successive extensions using the normalization clauses of the same cited statements; no arbitrary comparison is chosen.

Step 8 uses the pair-category and Weil-pair definitions to take the actual common-stage images and represent all inverse identities already at E. Stagewise truncations preserve heart membership. The point-heart equivalence at Omega identifies their fibres with scalar-extended E-fibres, and the existing Mathlib leaf `lem-weil-field-scalar-extension-exact` gives exactness of vector-space extension; reflection through the Omega heart equivalence then gives exactness of the sheaf diagram. This leaf works for E -> Omega, not only finite extensions. The scalar naturality clause includes the common-stage setting. At the distinguished vertex the resulting object is exactly the image of M_*, with its original theta and specified scalar comparison.

I recorded generic off-unit tool uses only in `split_report.tool_uses`: the truncation theorem and the two Frobenius-transport theorems. These are coefficient-category tools, not replacements for the unit's dimension-zero route. Definitions and the existing Mathlib leaf are ordinary notions/tools. There is no dependency on the parent flag node or the ancestor theorem, so the assembly introduces no backward edge. Every quoted citation is checked against the actual statement, and proof_deps is exactly the union of uses.

Against B1–B9, no new statement-only node, notation definition, source tag, leaf claim or duplicate is being introduced; the original item metadata, statement, source and existing searches are preserved, and the added searches are actual command log records with their actual service outcomes. B10 is addressed by the project-source attachment check. Against C1–C8, every non-elementary input is a named existing statement, not its proof or a tag standing in place of a node, and generic off-unit tools are declared. Against D1–D5, all eight steps carry explicit arguments, without shifting any clause into a restatement node. Against E1–E7, the exact coefficient category, heart membership of the pullback, inverse direction, prescribed object, universal cokernel property and specified scalar comparisons have each been checked, including the small cases above. No step exceeds 2000 characters; none hides a standard lemma needing extraction. No dispute remains in the original statement.
