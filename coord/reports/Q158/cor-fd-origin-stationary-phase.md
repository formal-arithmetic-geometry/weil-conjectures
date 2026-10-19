# Stage-1 worker report: cor-fd-origin-stationary-phase

## Files written

- `dag/nodes/sec-deligne-laumon-a1/cor-fd-origin-stationary-phase.json`: statement node, split; no exact Mathlib match. All six searches actually ran and their recorded responses were read.
- `citations.json`: one checked verbatim quotation for each of the 15 step/node pairs.
- No new nodes, no Mathlib leaves, no unit-record changes. This corollary carries the origin-identification portion of the unit step; it is not the unit's degree-one weight-bound statement.

## Attachments and Lean audit

`AlgebraicGeometry.ProEtale.finiteLowerStar_singleFunctor_of_isAffine` belongs to `lem-sf-adic-affine-direct-image-finiteness`. The existing node already records this full declaration in its `lean` field; its natural statement introduces exactly the affine source and target, the algebraically closed base field of characteristic different from l, both locally-finite-type morphisms, the constructible AdicSheaf, and the bounded constructible derived pushforward. I read LowerStar.lean:401–415, its definitions and the existing DAG statement. Thus the item's stale audit entry with `nodes: []` needs no new node. This is an audit correspondence, not a claim that the declaration is closed, and it is not a proof dependency of this corollary.

The item's recorded declaration `AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.nonempty_equiv_stalk_origin_of_isFourierPartner` was found at `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/DeligneLaumon/AffineLine/DegreeOne.lean:136–142`, and its proof is `sorry`. The origin-input declarations at lines 89–112 are also sorried in this read-only checkout. Hence ATTACH is unavailable. The inherited audit calls the item's older body `rests_on_sorry`; it does not describe the body now visible at these line numbers. I preserved maintainer-owned audit and Lean records. The Lean theorem has the current Fourier-partner hypothesis and the H_c^1/stalk and H_c^2-vanishing clauses; its type does not separately spell out the inertia-invariant identification. No claim of full exact attachment is made.

## WANTED

None: this proof is explicitly agent-written, following the available current blueprint statement and proof. No external literature claim is used in place of a DAG lemma.

## Source discrepancy and correction

The node's `blueprint_update` requires the main-20261015 statement. I followed that statement rather than the older imported irreducible/unramified/nonexceptional existence formulation. The new statement assumes a Fourier-partner isomorphism of Weil complexes between the specified two middle extensions. It does not assume purity, irreducibility, nonexceptionality, unramifiedness at infinity, or nonzero sheaves. The old proof's first paragraph still asserts these assumptions and constructs a nonzero irreducible partner. That inference is invalid under the current hypotheses: M=M'=0 on the whole lines satisfies the partner isomorphism, while its partner is not nonzero. The repair is to take the given partner isomorphism, not to add old hypotheses. This does not change the unit's route: it performs the origin-fibre comparison expressly required by the unit.

I made the inherited finite-field, coefficient, geometric compact-support and ordinary sheaf middle-extension conventions explicit. In particular, all cohomology in the displayed formula is on the geometric fibre, with the geometric Frobenius of k_0; ordinary arithmetic cohomology over the finite field would be a different object. The phrase "inertia trivial if the point lies in the open" now says that its action is trivial: the inertia group itself need not be trivial. No mathematical assertion beyond the current blueprint intent is changed.

Removed the old nonexceptionality definition and the two existence/nonexceptionality lemmas from the actual dependency lists; their imported blueprint metadata is retained untouched. Added the existing generic Weil-operation equivariance theorem to avoid taking equivariance from an origin-stalk statement which does not literally assert it. No new node merely restates a clause of the item.

## Review by Q158

I read `coord/brief-stage1.md`, `stages/1-dag.md`, the three levels in SETUP, delivery-errors B–E in full, GOAL and dag-sync; I read the chapter and unit records, the current main-20261015 corollary statement and `.proof.md`, and the current origin-input statement. The chapter's Fourier-transform route and the unit's origin formula with its two shifts remain the route here. The source proof is agent-written; I do not label it a proof from Laumon or from a forbidden source. There are no new nodes requiring independent source statements or additional Mathlib searches.

For step 1 I opened `lem-fd-stalk-at-origin`, which expressly states both H^{-1}=H_c^1 and H^0=H_c^2 for a shifted middle extension; I use those clauses rather than silently assuming any general cohomological-dimension or endpoint theorem. `def-wf-middle-extension` expressly distinguishes ordinary j_* from Rj_* and places the former in degree zero. `def-weil-ordinary-compact-cohomology` defines H_c by geometric RΓ_c. The hypotheses here are a lisse Weil sheaf on a dense open of the affine line and precisely the rank-one transform that the origin input takes. The assumed partner supplies the isomorphism, without irreducibility or unramifiedness.

For step 2 I read the statements of `def-fd-kernel` and `def-fd-artin-schreier-sheaf`. The first identifies the restriction with the sheaf for the zero pairing, and the second specifies the polynomial covering and character-isotypic projector. Substitution f=0 gives the sections T=a and a constant character line. Its character function has value 1 at 0, so Frobenius fixes the selected trivialization. This is an explicit elementary calculation in the given definition, not a new kernel lemma. The calculation works for the character allowed by the transform; no invertibility argument or nonexceptionality assumption is smuggled in.

For step 3 I read `lem-fix-weil-operations` in full at its statement, including its bounded-constructible-domain condition and its field coefficient restriction. It explicitly asserts equivariance of exchange maps and canonical Weil structures on pullback, both direct images and tensor. The two affine projections and rational origin inclusion descend to k_0 and are separated finite type. Their application is at E and Qbar_l, as required; it is not an invocation of arbitrary pro-etale base change. The origin formula already supplies the isomorphism, while this generic lemma supplies its compatibility with Weil structures. I also opened `def-fd-transform` and `def-weil-weil-sheaf-complex`, and wrote the actual morphism-of-pairs equation. The origin has residue field k_0, so no degree factor changes Frobenius.

For step 4 the two ordinary sheaves and their shift are exactly those in `def-wf-middle-extension` and `def-weil-abstract-derived-category`. I use the explicit shift convention and degreewise fibre of a single sheaf, not a claim that Rj_* has no higher cohomology. The construction of the isomorphism is displayed as H^{-1}(a) inverse followed by H^{-1}(alpha). Degree zero of the shifted single sheaf is zero, so comparison yields H_c^2=0. Equivariance follows by applying the fibre to the assumed morphism of Weil pairs, whose equation is in `def-weil-weil-sheaf-complex`. This step is elementary once the two earlier isomorphisms are provided.

For step 5 I opened `lem-wf-boundary-stalk-invariants` and checked its exact hypothesis that x is a boundary point. I apply it only in that case, on the smooth dual affine line, with a dense open and lisse sheaf. Its statement explicitly includes Frobenius-equivariance and independence of the Frobenius lift. The definitions of the local generic stalk and inertia action are in `d-real-boundary`, which I also read. Thus the step does not cite a definition for the stalk-invariants theorem.

Step 6 handles the remaining point inside the open separately. `def-pod-lisse-l-adic-sheaves` supplies finite-level locally constant trivializations and the compatible integral, rational and Qbar_l fibres. On the strict local neighbourhood these trivializations identify the special and local generic fibres, so inertia acts trivially. This is the elementary local computation from lissity, and specialization intertwines the specified Weil descent map by functoriality. The claim concerns the inertia action, not the inertia group. No boundary-only theorem is applied to an interior point.

I checked small cases: the zero sheaves give zero on every side and must be allowed; a sheaf lisse at the origin has its full generic fibre as invariants; a boundary sheaf with no inertia invariants has zero origin stalk and hence zero H_c^1; and a geometrically constant nonzero sheaf on the entire line cannot satisfy the assumed shifted-lisse-partner hypothesis (its transform is supported at a point), so it is no counterexample to H_c^2=0. The proof uses no semisimplicity or purity assumption. Rechecking B1–B10, C1–C8, D1–D5 and E1–E7 revealed the obsolete shape paragraph, the missing equivariance citation, the arithmetic/geometric ambiguity and the inertia-group/action wording; these are the corrections above.

I searched the full DAG and blueprint by `origin`, `stationary`, `inertia`, exact Lean names, and affine-finiteness concepts. The only stationary-phase blueprint theorem is the item itself; related origin and boundary lemmas are cited in their existing form. The affine-finiteness audit declaration already has its own existing exact node. All six steps are below 2000 characters; none hides a separate long comparison lemma. Every proof dependency has a quotation checked against the current DAG statement in `citations.json`.

The generic origin formula, generic Weil-equivariance theorem and boundary invariant theorem are declared under `split_report.tool_uses` because their statements are tools for the unit's fibre calculation; their proofs do not replace the unit's weight route. Definitions need no off-unit route exception.

## Not duplicates

No new node was created; there are no new/existing-node pairs.

## Unfinished work

None within this one-level split. Existing cited unsplit lemmas remain independent DAG items. Server validation and delivery are recorded below when completed.

## Validation

The required server dry run completed successfully: `deliver.py Q158 cor-fd-origin-stationary-phase --no-push` printed `OK (not pushed)` at 04f500ef64, with preflight passed. It includes the server DAG and split checks. No local checker, Lean compiler, Lake, git command, live-source write, or sub-agent was used. The final delivery repeats the same server gates after this validation note.
