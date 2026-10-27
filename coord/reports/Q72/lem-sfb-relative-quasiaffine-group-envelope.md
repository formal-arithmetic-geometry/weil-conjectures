# Q72: lem-sfb-relative-quasiaffine-group-envelope

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-relative-quasiaffine-group-envelope.json`: statement, split; no exact Mathlib match. Nine proof steps, using existing DAG statements throughout. The inherited statement and source record are unchanged.
- `citations.json`: one verbatim statement quotation for every node cited by every proof step.
- `report.md`: this report. `searches.jsonl` retains the five actual searches made with the required command. No new node files and no Mathlib leaves were created.

## Attachments

None. I searched the project Lean source both for the exact blueprint tag and for relative-spectrum/quasi-affine/group-envelope terminology. The project contains related relative-spectrum constructions and group schemes, but no declaration giving the whole item. In particular neither an existing group-scheme definition nor a sorried relative-spectrum assertion is an attachment.

## WANTED

None. The proof is agent-written from the local Stacks sources and the existing DAG interfaces; it does not rely on the unavailable Prasad–Yu reference carried by the different, absolute flat-trait-affinization node.

## Faults and changes

The item was unsplit, with an empty proof and proof-dependency list. Its statement is correct and remains verbatim. I made explicit the substantive extra work beyond Stacks 01SM: flatness of the envelope without finite generation, preservation of the structure-unit isomorphism under successive flat base changes, and unique extension of operations into an affine morphism. I do not attribute those group assertions to 01SM itself.

The strongest useful intermediate conclusion is that the canonical unit is an isomorphism on all of H, before generic base change. This is derived from the chart identity on functions using the existing qcqs local-comparison node. It is not an extra hypothesis and is not a change of the requested conclusion.

The current blueprint's direct-images proof (3) and unit were read at `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/`. They have no relative group-envelope theorem to attach. The item is a descendant of the inherited relative-semisimple-affineness prerequisite, as its existing `blueprint.from.place` records. `tools/blueprint_refs.py ancestor` returns None, matching the inherited null `from.node`; I retained that provenance and its full via chain. Whole-blueprint searches for `quasi-affine` and `affinization` found no equivalent imported statement. No unit or chapter record was edited: this item is not the unit's key node.

## Unfinished work

None in this one-level split. The delivery does not claim to formalize any of the cited unsplit lemmas. No Lean was written, and no compiler, Lake, global build, or local preflight/check script was run.

## Not duplicates

There are no new nodes. In particular I reused the existing `lem-sfb-dedekind-torsionfree-module-flat`, `lem-trf-qcqs-relative-affinization-map`, `lem-trf-canonical-affine-charts-qc-open-immersion`, and `lem-pc-flat-base-change-cohom` instead of duplicating 0AUW, 01LY, 01SM, or 02KH. The different `lem-sfb-flat-trait-group-affinization` concerns an absolute spectrum over a DVR; it does not assert the relative envelope over a possibly nonaffine J.

## Mathlib search results

I ran the required search command five times: two distinct LeanFinder phrasings, a LeanSearch query, a Loogle pattern, and a grep restricted to `AlgebraicGeometry/Group`. Every exact tool/query pair is recorded in the item's appended `mathlib_searches` and the sandbox log. All services responded. The first semantic search returned affine-source facts and affine-space constructions; the second returned structure-sheaf multiplication and comap operations. LeanSearch included the absolute theorem `AlgebraicGeometry.Scheme.instIsOpenImmersionToSpecΓOfIsQuasiAffine`, which gives an open immersion but neither the relative group law nor the product comparison. Loogle returned no hits. Grep located `Mathlib/AlgebraicGeometry/Group/Affine.lean`; reading its introduction and construction shows it starts with a Hopf algebra, whereas constructing the operations is the substance of this item. None gives the item by a one-line specialization. The older inherited search entries were preserved separately from these appended searches.

## Review by Q72

I read Stacks `morphisms.tex`, Tag 01SM (`lemma-characterize-quasi-affine`), including its proof of (2) implies (4); `constructions.tex`, Tags 01LX and 01LY (`lemma-spec-properties`, `lemma-canonical-morphism`); `coherent.tex`, Tag 02KH (`lemma-flat-base-change-cohomology`), with the qcqs and flatness hypotheses; `more-algebra.tex`, Tag 0AUW (`lemma-dedekind-torsion-free-flat`) and the flat-implies-torsion-free argument; and `schemes.tex`, Tag 01I1 (`lemma-morphism-into-affine`). For the flat affine translation I read Tag 01U5 in `morphisms.tex`; for flat base change of morphisms, Tag 01U9; for localization flatness, Tag 00HT in `algebra.tex`. I also read the torsion-free global-section discussion in `more-morphisms.tex`, Tag 0EX8. No SGA source is used. There are no new-node sources to audit.

In step 1, `lem-weil-pbc-qcqs-over-affine` explicitly permits a separated finite-type source over an affine base. It gives qcqs for both G and J. `lem-weil-pbc-qcqs-morphism-permanence` then gives qcqs of the actual f from its source and target; it does not require f flat. `lem-trf-qcqs-relative-affinization-map` states quasi-coherence, the affine relative spectrum, qj=f, and the identity-on-functions description on all affine target charts. These are exactly its uses here.

In step 2, `lem-trf-canonical-affine-charts-qc-open-immersion` applies to the actual q and j supplied by step 1: q is affine, every G_W is quasi-affine by the item's hypothesis, and the canonical chart identities are supplied. The node's conclusion includes quasi-compactness, not just openness. `lem-weil-pbc-separated-cancellation` says open immersions are separated, and `lem-pc-separated-quasi-separated` supplies the quasi-separatedness needed later. I did not assume the potentially non-finite-type H was Noetherian.

In step 3, I opened `lem-sfb-qcqs-functions-local-comparison`. Its statement identifies the stalk of the structure unit with the localized coefficient map and tests whether the unit is invertible. The coefficient map on each H_W really is the identity of A_W. Thus localization gives the identity at every prime. The node also explicitly supplies restriction-compatible isomorphisms on arbitrary opens once the unit is invertible. Those arbitrary-open isomorphisms are the input to the affine-adjunction argument, rather than an unjustified claim that equality of global sections alone detects an arbitrary sheaf map.

In step 4, `lem-sc-flat-invertible-sections-torsion-free` assumes only a domain, a flat scheme, and an invertible module; it imposes no properness, finite presentation, or nonemptiness. Restricting G to G_W preserves the local rings defining flatness, and O has the global free basis 1, satisfying `def-sc-invertible-module`. `lem-sfb-dedekind-torsionfree-module-flat` explicitly allows dimension at most one and arbitrary modules, so it applies to A_W without finite generation and includes B a field. `lem-weil-pbc-flat-ring-map-iff-flat-affine` converts this conclusion to flatness of H_W over S. The pointwise definition `def-weil-flat-morphism` makes these chartwise flatness assertions imply flatness of H, and justifies restriction of flatness to G_W.

In step 5, `lem-pc-flat-base-change-cohom` states the sheaf base-change isomorphism for a qcqs f and a flat g, for every i; I use i=0 and the structure sheaf, not a proper-only or field-only variant. `lem-weil-pbc-flat-morphism-base-change` makes the product projections flat using precisely flatness of G and H over S; neither flatness of f nor flatness of j is needed. `lem-weil-pbc-flat-ring-map-comp`, combined with the local-ring definition of flatness, handles composite projections in the cube. `lem-weil-pbc-qcqs-morphism-permanence` states base-change stability of both qc and qs. Two successive replacements give the square, and three give the cube. Composition of direct images is evaluation on inverse images of opens, so the resulting unit is the canonical restriction map, not an arbitrarily chosen isomorphism.

In step 6, `lem-weil-pbc-morphism-into-affine-scheme` allows any scheme as source, so V need not be affine. Its bijection makes the extension and its equality over the affine W a cancellation through the known ring isomorphism. `pqf-def-affine-morphism` ensures that H_W and H_{W'} are affine for affine W and W'. The proof handles overlaps by covering W intersection W' by affine opens, rather than assuming the intersection is affine. `lem-weil-pbc-morphism-factors-through-open-subscheme` justifies the restrictions to those opens; `lem-weil-pbc-scheme-morphism-gluing` supplies existence and uniqueness of the glued map. This step is elementary relative to those interfaces: apply the affine Hom bijection, invert the ring isomorphism, and glue the resulting unique maps. No separate extension lemma was created.

Steps 7 and 8 use the previously proved extension property, with the base map specified each time. Multiplication uses m_J(q,q), inversion uses i_J q, and the identity is j e_G. Associativity is tested on G cubed; the two sides have the same prescribed map to J by associativity in J. Unit laws use base map q and inverse laws use e_J composed with the structure map of H. The restrictions agree by the group diagrams in G. These are formal substitutions and uniqueness, not appeals to topological density or an unstated result about extending group structures.

In step 9, `lem-weil-pbc-localization-flat` applies because the fraction field is localization at the nonzero elements; its three explicit conditions follow from the fraction description and injectivity of B into K. `lem-weil-pbc-flat-ring-map-iff-flat-affine` and `lem-weil-pbc-flat-morphism-base-change` give flatness of H_K to H. `lem-pc-flat-base-change-cohom` then identifies the pulled-back unit with the canonical unit for j_K. All the flat and qcqs hypotheses have already been checked.

I checked small cases: over a field no DVR or positive dimension is used; for an affine f the construction is the usual relative-spectrum identification, and the operations recover those on G; for f the identity the construction gives H=J with its original operations. Nonreduced group fibres are allowed, since the proof uses sheaf isomorphisms and ring-map uniqueness rather than reducedness or pointwise density. Empty chart preimages give the zero ring and empty spectrum and cause no exception to the cited section or affine-adjunction statements. H need not be finite type or affine over S. The proof never takes an intersection of arbitrary affine opens to be affine. Every step is shorter than 2000 characters. I checked B–E of `coord/delivery-errors.md`: no new-node restatements, no hidden literature citation in place of a node, every cited interface read as a statement, no extra hypotheses, and no route replacement. Generic tools from other units are declared individually in `split_report.tool_uses` for maintainer review.

The server-side `review_split` check passed before writing this report. The full required dry run and push are the final delivery checks.
