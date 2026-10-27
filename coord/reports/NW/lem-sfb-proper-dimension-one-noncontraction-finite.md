# Stage-1 report: lem-sfb-proper-dimension-one-noncontraction-finite

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-proper-dimension-one-noncontraction-finite.json`: unchanged statement; seven proof steps following Stacks 0CCL. Mathlib searches give no exact match or one-line specialization for the dimension/noncontraction criterion.
- `citations.json`: one verbatim statement quote for each node used in each step (16 entries).
- `report.md`: this report. No new DAG nodes, Mathlib leaves, unit edits, or Lean edits.

## Attachments

None for the item. Searches of the project library for the exact blueprint tag, noncontraction, nonconstant curve morphisms, and proper dimension-one finiteness found no declaration stating all its hypotheses and conclusion. Existing Mathlib/project results used through their existing nodes are not claimed as attachments of this item.

## Wanted

None. All mathematical sources used are available under `literature/stacks-project/`.

## Findings and changes

The sandbox was initially empty. I copied the live unsplit item and retained its statement, inherited searches, provenance, chapter/unit, and blueprint seed-chain references. There was no repair note. Stacks `curves.tex`, Tag 0CCL, `lemma-finite`, states exactly the item, including dimension AT MOST one, arbitrary ground field, no Noetherian assumption on the separated target, and the set-theoretic condition that each one-dimensional component has image of cardinality at least two. No statement dispute or correction is needed.

The source's sentence saying that the closed fibre is finite is now explained: a chain of length one in that fibre would make its larger member a one-dimensional component of X, contracted to the base point. With no such chain, finitely many irreducible components of the closed fibre are singletons by the uniqueness of generic points. The final “enough of these points” assertion is expanded using the existing Jacobson-space statement on X, rather than assuming Y is finite type or Noetherian. To avoid an uncited finiteness-locality theorem, the finite neighbourhoods give affine inverse images on an affine cover of Y; existing affineness-locality and affine-proper-finite nodes finish the proof.

The enclosing unit record is historical and its chapter field differs from the assigned node's chapter; I preserved both, read the current `latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/` statement and proof, and made no unit changes. The item's seed chain has no imported blueprint ancestor, as the ancestor command confirms. Its role remains the geometric finiteness tool below direct-image stability.

## Unfinished work

None at this split level. No new unsplit nodes were necessary. No compiler, Lake, or local DAG/preflight checker was run.

## Not duplicates

No new nodes. Existing nodes reused include the exact proper-over-separated theorem, general finite-fibre neighbourhood theorem, finite closed-subset components, uniqueness of scheme generic points, finite-type Jacobson property, affine target locality, and the same-unit affine-proper-finite equivalence. Whole-DAG searches by titles, statements, Stacks tags and declaration names, and `blueprint_refs.py search` queries for nonconstant, proper finite, finite fibre, finite neighbourhood, Noetherian, Zariski local, finite morphism, 01W6, 0CCL and proper affine found these tools without an equivalent blueprint statement for the item. I also searched the latest blueprint text for noncontraction/nonconstant finiteness.

## Review by NW

I read the exact Stacks 0CCL statement and complete proof in `curves.tex`. I checked the invoked sources in `morphisms.tex` (01W6, `lemma-image-proper-scheme-closed`; 01T6, `lemma-finite-type-noetherian`; 01S8, `lemma-characterize-affine`; 01WN, `lemma-finite-proper`), `more-morphisms.tex` (02UP, `lemma-proper-finite-fibre-finite-in-neighbourhood`), `properties.tex` (01OZ, `lemma-Noetherian-topology`; 0BA8, `lemma-Noetherian-irreducible-components`), and `varieties.tex` (0478, `lemma-locally-finite-type-Jacobson`). There are no new nodes requiring their own source review. I opened the full statement of every cited node and copied verbatim quotations to citations.json.

Step 1 uses `lem-weil-pbc-proper-over-separated` with S=Spec k, where the morphism-over-base definition supplies the required commuting triangle. Its conclusion explicitly includes properness and universal closedness; the properness definition supplies closedness of the map, and hence closedness of images of singletons. Step 2 uses the properness and finite-type definitions to obtain finitely many affine charts of finite-type k-algebras, and `lem-wf-affine-noetherian-components` explicitly supplies both Noetherian rings and Noetherian chart topologies. The passage from a finite cover to stabilization of a global closed chain is written out and elementary.

Step 3 cites the exact chain definition of topological Krull dimension and the maximal-irreducible-component definition. It proves the dimension-zero fibre claim directly; it does not assume an unprovided dimension theorem or a generic point. A strict intermediate larger irreducible closed subset would give length two, so the maximality assertion follows from dim X <= 1. Step 4 uses `lem-sc-noetherian-closed-subset-finite-components`, whose statement covers any closed subset of a Noetherian scheme, and `lem-weil-pbc-scheme-sober`, whose statement gives existence AND uniqueness of generic points for every irreducible closed subset. Each closed fibre component is closed in X. The argument that it is a singleton is explicitly a two-line consequence of the dimension-zero result and that uniqueness; no additional theorem about finite fibres is concealed.

Step 5 uses `lem-trf-proper-finite-fibre-finite-near`, whose statement requires exactly the properness and finiteness of the underlying fibre already established, and explicitly imposes no Noetherian assumption on the target. This off-unit generic tool is declared in split_report.tool_uses: it is precisely the theorem invoked by 0CCL and does not change the unit's route. Step 6 uses `lem-sc-lft-over-field-jacobson-space`, whose statement says that closed points of X are dense in EVERY closed subset of X, not merely dense in X. Thus it applies to the closed complement preimage E. This verifies the covering assertion without assuming arbitrary target points are closed. Step 7 uses the finite-morphism definition for affineness over each affine target chart, `pqf-lem-affine-local-target` for the stated affine-cover criterion, and `lem-sfb-affine-proper-finite` for exactly the general-scheme equivalence. The empty inverse image is Spec of the zero ring.

I checked B1–B10: no unnecessary new nodes or proofs inside new statements, correct TeX and exact Stacks tags, actual logged searches only, no false Mathlib-leaf or Lean-attachment claim, and complete blueprint fields. I checked C1–C8: all non-elementary inputs are existing cited statements, no use of a cited proof in place of its statement, and the only non-leaf off-unit tool is declared. I checked D1–D5: the seven steps contain the argument, with no relabelled clause moved into another node. I checked E1–E7 against the hypotheses above. Edge cases are the empty scheme, dimension-zero X (noncontraction vacuous), reducible and nonreduced proper schemes (only closed-set topology and finite-type affine charts are used), arbitrary fields, and separated targets not locally Noetherian. A contracted proper curve fails the stated hypothesis, as it must. No step exceeds 2000 characters; no long-step extraction is needed.
