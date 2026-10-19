# Stage-1 report: lem-trf-nodal-points-reduced-algebraically-closed

## Files written

- dag/nodes/sec-trace-formula/lem-trf-nodal-points-reduced-algebraically-closed.json: statement item, split into six steps; no Mathlib match.
- citations.json: fifteen verbatim statement quotations, one for every step/node citation.
- searches.jsonl: the seven actual searches made through msearch.py; the existing search in the imported item is retained.

No new nodes; no Mathlib leaves created. No unit record is changed.

## Attachments

None. I searched the read-only slopmaster2 project for the exact blueprint tag and for nodal/reduced/completed-local-ring terminology. No declaration states this item. The already attached AlgebraicGeometry.Smooth.geometricallyReduced supplies only the smooth-point input, not the item's nodal or closed-point-to-all-point conclusions. The upstream master source is reference material only.

## Literature

No WANTED documents. I read Stacks curves.tex Tag 0E37, lemma-facts-about-nodal-curves, especially its final reducedness paragraph; algebra.tex Tags 00MC, lemma-completion-faithfully-flat, and 05CK, lemma-faithfully-flat-universally-injective; varieties.tex Tags 0478, lemma-locally-finite-type-Jacobson, and 056T, lemma-smooth-geometrically-normal; morphisms.tex Tag 01T6, lemma-finite-type-noetherian; algebra.tex Tag 00FN, lemma-Noetherian-permanence; properties.tex Tag 01OV, definition-noetherian; and schemes.tex Tags 01HV, lemma-spec-sheaves, 01HF, example-open-subspace, and 01J0/01J1, definition-reduced/lemma-reduced.

The proof is marked agent-written: 0E37 motivates the completed-node calculation but states a more restrictive pure-dimension-one result. I do not invoke that result for this more general item. Every use of its surrounding standard theory is backed by an existing node, and the coefficient and fraction arguments are written out.

## What needed correction

The item was unsplit and its proof plan did not yet constitute a proof. Its mathematics is sound. I preserved the ring-isomorphism hypothesis (not an algebra-isomorphism hypothesis), locally finite type rather than finite type, unrestricted dimension, and the empty case. I normalized doubled backslashes in its statement to single TeX commands; this changes no mathematical assertion.

The existing lem-trf-nodal-geometric-fibres-reduced was opened and read, but is not a substitute: it assumes finite type and pure dimension one after all algebraically closed extensions, and proves geometric reducedness. It cannot be invoked to prove the present item without hypotheses we do not have. I reused its actual generic inputs instead. In particular I used pqf-lem-locnoeth-lft, whose statement gives the locally Noetherian conclusion for a locally finite type map; the finite-type-only lemma is not applied to the whole C.

I retained the historical blueprint ancestry. I read the chapter and sk-i-curve-zero unit and the current main-20261015 local-term ancestor. Its current statement concerns contracting local terms, and does not contain the older stable-modification paragraph recorded in this auxiliary item's provenance. This split supplies that existing algebraic input; it changes neither the chapter nor the unit route.

## Searches and existing-node checks

Whole-DAG searches for 00MC, 00GB, completion injectivity, Jacobson/closed points, reduced localization and the power-series model located the nodes now cited. The whole-blueprint searches were `nodal reduced`, `reduced nodal`, `reduced completion`, and `reduced closed`; the ancestor command returns lem-trf-local-term-locality. The completed-reduction-square result found by `reduced completion` concerns coefficient completions, not this algebraic scheme criterion. No blueprint node found states the present item. No new statement or definition is needed.

The item was searched through msearch.py with LeanFinder (two phrasings, one explicitly about reduced completed local rings on a locally Noetherian Jacobson scheme), LeanSearch, Loogle (two patterns), and grep (two patterns). All seven searches ran successfully; their exact queries and results are retained. I read Mathlib/AlgebraicGeometry/Properties.lean:69-123: its IsReduced definition, all-stalk criterion, open restriction and affine criterion do not infer reducedness from the specific completed local rings at closed points. The formally unramified algebra result requires a hypothesis not supplied by a node. Loogle's ext_of_apply_eq assumes reducedness; the interpolation uses of “nodal” are unrelated. These are not exact matches or one-line specializations.

## Not duplicates

No new nodes were created. The related geometric-fibre item is distinguished above and is not cited as if its extra hypotheses were available.

## Review by Q44

I checked the six steps with the source passages and all thirteen distinct cited node statements open. citations.json copies those actual statements, rather than expanding their meaning by paraphrase.

Step 1 uses pqf-def-locnoeth for the affine-cover definition, pqf-lem-locnoeth-lft for permanence under locally finite type morphisms, lem-weil-pbc-affine-open-stalk-localization for the actual localization of a chart ring at a point, and lem-weil-pbc-localization-noetherian for the ring-level Noetherian conclusion. Those statements give each assertion used. The field is Noetherian by the elementary two-ideal argument. No assumption of quasi-compactness of C enters, and the chosen affine neighbourhood comes from the Noetherian cover, so no unproved assertion about arbitrary affine opens is needed.

Step 2 uses the conclusion of sbc-lem-smooth-geometrically-reduced exactly on the given smooth neighbourhood V. The unique fibre of V over Spec F is V, and taking the identity field extension gives reducedness. def-pc-reduced-scheme then gives the reduced stalk. The open-stalk identification is justified by cofinal neighbourhoods, not by an additional smoothness or dimension hypothesis. I checked the attached slopmaster2 declaration, which is indeed the smooth-fibre assertion, with a proof and no sorry in that declaration; I do not claim it attaches the present item.

Step 3 uses only the coefficientwise construction in def-weil-pbc-multivariate-power-series and the domain conclusion in lem-weil-pbc-power-series-domain with d=1. I explicitly computed the kernel of the two axis restrictions: the shifted coefficients g_ij recover every series with zero coefficients on both axes as uv*g. The injection into the two domains kills nilpotents. This is an elementary argument from those statements, not an uncited theorem on nodal curves, and creates no redundant model-reducedness node.

Step 4 checks both hypotheses of lem-weil-pbc-local-completion-faithfully-flat: the ring is local because it is a stalk, and Noetherian by step 1. That node gives faithful flatness, while the separate lem-weil-pbc-faithfully-flat-ideal-contraction explicitly gives injectivity for I=0. A ring isomorphism to the model suffices to transport nilpotence; there is no hidden requirement that it preserve F-scalars. The dichotomy “has a smooth open neighbourhood / has none” exactly matches the given hypothesis.

Step 5 uses the full density statement of lem-sc-lft-over-field-jacobson-space for the nonempty global closed set closure{y}; it does not confuse a point closed in an affine open with one closed in C. It supplies a global closed specialization x. Any affine open containing x contains its generization y. The Zariski definition in def-weil-affine-spectrum gives q subset p, and the affine-stalk node identifies both stalks with B_q and B_p. I wrote the denominator calculation directly using def-weil-pbc-localization-at-prime: t*a^n=0 implies (ta)^n=0 in the reduced B_p, whence u*t*a=0 with u outside p. Since u and t are outside q, a/b=0 in B_q. Thus there is no hidden comparison theorem about iterated localizations. I checked the direction q subset p and all denominators; the element t need not lie outside p, which is why one applies reducedness to ta rather than incorrectly to a itself.

Step 6 uses exactly the local-ring definition in def-pc-reduced-scheme. The empty case is vacuous. For small cases I checked the smooth point Spec F, smooth affine spaces of arbitrary dimension, the ordinary nodal model (and its finite-type polynomial version), and disjoint unions with infinitely many smooth components. The doubled point Spec F[e]/(e^2) does not satisfy the premise: its sole closed point is nonsmooth and its Artinian completion is not the reduced nodal model. None of these checks imposes dimension one, a finite global affine cover, separatedness, or properness. The argument is characteristic independent.

Against delivery-errors B-E: the single changed node is self-contained; no statement-only child hides the proof, and no clause is relabelled as a new node. Every non-elementary input is the statement of a cited node, with a verbatim quotation. Source tags and labels were checked against the local Stacks tag table. The elementary model computation and the written fraction calculation replace potential hidden facts; I also corrected the tempting finite-type/locally-finite-type mismatch before writing. No step exceeds 2000 characters (the longest is 1235), no new definition is hollow, no source from the prohibited SGA route is used, and no Lean or compiler command was run. The generic locally Noetherian permanence theorem is recorded as an off-unit tool use; all other non-definition inputs are already Mathlib or closed tools.

## Unfinished work

None in this one-level split. All children already exist. Independent maintainer review remains part of the delivery process.
