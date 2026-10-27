# Stage-1 report: lem-pd-conjugate-tensor-localization-counit

## Files written

- `dag/nodes/sec-poincare-duality/lem-pd-conjugate-tensor-localization-counit.json`: statement, split in five steps; no Mathlib match. The existing statement, source, blueprint ancestry and prior searches are retained. NI's actual search records are appended.
- `citations.json`: four step/node pairs, each with a verbatim statement quote (the descent theorem is used in two steps).
- `report.md`: this report. `searches.jsonl` was produced by the required msearch command.

New nodes: 0. New Mathlib leaves: 0. The needed non-elementary results already exist in the DAG.

## Attachments

None. I searched `lean/WeilConjectures/` for the exact blueprint tag and conjugate tensor/localization counit terminology, then inspected the plausible conjugate-monoidal and balanced-tensor files. The former treats mates of monoidal adjunctions; the latter treats scalar extension of modules and homology. Neither states this item's ringed-site bifunctor construction, representative formula and all-complex equation together. There is no exact project declaration to attach.

## WANTED

None. The Stacks sources and the latest blueprint material needed here are present locally.

## What needed repair

The item was statement-only. I supplied the comparison and its inverse on resolving pairs, extended both by the existing site descent theorem, computed the prescribed normalization, proved uniqueness, and wrote the entire arbitrary-complex naturality calculation. I did not weaken or correct the statement. In particular the all-complex counit identity is proved, rather than inferred from equality on derived representatives: its ordinary tensor target does not factor through the derived category on arbitrary pairs.

The item is a seeded descendant of `nt-target-poincare-isiso`, not a node imported from the blueprint; its nearest imported blueprint ancestor is null, as `blueprint_refs.py ancestor` reports. I retained that ancestry and the explicit seeded-target/parent-step provenance. I read the latest `lem-sfb-derived-monoidal.proof.md` and the latest Verdier-exchange unit. This is a tool-level resolution comparison within the prescribed tensor/duality route, not a replacement for any unit step. No chapter or unit record was edited.

## Unfinished work

None for this one-level split. Independent maintainer review and downstream formalization remain the project's normal next stages.

## Not duplicates

No new node is proposed, so there are no new/existing same-tag pairs. Existing `lem-weil-pbc-site-derived-tensor-descent` already states extension and uniqueness of arbitrary natural transformations on flat-term K-flat pairs, and `lem-pc-kflat-resolution` already states the resolution existence used at the end. I reused them. The separate `lem-pd-ringed-kflat-native-model-identification` compares two tensors on the same module category, whereas this item compares the conjugate under the specified equivalence; it is neither needed nor cited. I also inspected `lem-sfb-exact-tensor-functor-derived-normalization` and `lem-sfb-ringed-equivalence-resolving-tensor-descent`; their statements give normalized monoidal comparisons but not this item's all-complex conjugate counit equation. Blueprint searches for `derived tensor`, `conjugate tensor`, and `localization counit` found no exact blueprint statement of this item. Its `same_as` remains empty.

## Mathlib searches

NI ran leanfinder with two distinct phrasings, leansearch, loogle for `CategoryTheory.Functor.leftDerivedNatIso`, and grep for `leftDerivedNatIso|totalLeftDerivedCounit|lift₂NatIso` in `CategoryTheory`. All services answered. The exact queries and actual returned summaries are in the node and the command's log. LeanFinder returned module flatness and projective-resolution Tor facts; LeanSearch returned derived adjunction counits, unitors and exact-functor localization factors. Those do not state this theorem. I read Mathlib `CategoryTheory/Functor/Derived/LeftDerived.lean` around lines 64–140 and `CategoryTheory/Localization/Bifunctor.lean` around lines 150–200. The first constructs a unique comparison only after derived universal properties are supplied; the second lifts a natural isomorphism only after localized liftings are supplied. Establishing the present conjugate model normalization and the all-complex equation still requires the argument here, so neither is a one-line specialization giving the item. Prior NO search records have been preserved, not claimed as new NI searches.

## Review by NI

I read Stacks `sites-cohomology.tex`, Tag 06YS, label `lemma-K-flat-resolution`, including its proof, and Tag 06YU, label `definition-derived-tor`, including the construction immediately preceding it. The tags were checked against `tags/tags`. They support the resolution and localization route; the exact conjugation and counit calculation are agent-written and marked accordingly. I read `stages/1-dag.md`, the three-level rule in SETUP, the chapter and unit records, and both B–E blocks of `coord/delivery-errors.md` in full. No new lemma or definition is being deferred, so there are no new-node sources to audit.

For step 1 I checked the equation in the item's own statement, the orientation of every factor, and the hypotheses on H. Flat-term K-flat U,V have flat-term K-flat HU,HV by assumption. The internal counit is invertible there by the inverse model maps already fixed in the statement. Its E-image and the specified total and localization factors are isomorphisms. The explicit formula using the termwise equivalence counit then makes the conjugate counit invertible at U,V. This is just substitution in the given definition and naturality, not an uncited assertion that a derived functor is universal. It uses no proposition from another node.

For step 2 I opened the statement of `lem-weil-pbc-site-derived-tensor-descent`. Its last sentence explicitly extends every natural transformation on the restricted pair of resolving subcategories and states uniqueness, for arbitrary target category E. This is the clause used, with target D(R), not merely the existence of a derived tensor. The quotient of invertible counits is natural by the two displayed squares. I extend its inverse separately and use uniqueness for both composites, so invertibility of the extension is proved. The smallness condition is exactly smallness of the site relative to the module universe, already a hypothesis of the item. The potentially large homotopy category is not substituted into a theorem requiring a small indexing category.

For step 3 I checked the domains: theta starts at D(E)B_A, theta_0 ends at B_c(D(E)-,D(E)-), and v then ends at B_R(D(E)-,D(E)-). Naturality at kappa supplies B_R(kappa) on the left. The counit equation and epsilon_A = inverse r_A give the stated representative formula with inverse B_R(kappa) on its left. This is an algebraic rearrangement of given isomorphisms, so no extra comparison lemma is hidden in the step.

For step 4 I checked the explicit conjugation formula defining v' from any competing theta'. Its source is B_c(X,Y), and the two outer bifunctor maps use the localized equivalence counit in the necessary directions. The equivalence triangle identities invert the correspondence between theta' and v'. Applying the normalization at HU,HV is legal because H preserves flatness and K-flatness; on their E-images the defining counit equation gives exactly inverse epsilon_R times epsilon_c. Naturality with c_U,c_V gives that equation on every resolving pair. I reopened the site-descent statement: its uniqueness clause therefore gives v'=v. The proof does not cite the parent tensor-comparison theorem, which depends on this item and would create a cycle.

For step 5 I opened the statement of `lem-pc-kflat-resolution`: it supplies a quasi-isomorphism from a flat-term K-flat complex to every complex of sheaves of modules, without boundedness assumptions. I also read `def-weil-abstract-derived-category`: localization at quasi-isomorphisms makes q(p) and q(s) invertible. The displayed five-term equality follows in order from naturality of v, naturality of epsilon_R, the already constructed resolving-pair equation, and naturality of epsilon_c. Only B_c(q(p),q(s)) is cancelled. No quasi-isomorphism claim is made about Tot(p tensor s), and no inversion of the counit at arbitrary U,V occurs. The two cited statements say exactly these things; `citations.json` contains their verbatim text.

I checked the zero ring and zero complexes (all formulas reduce to the unique relevant maps), identity equivalence (the resolving-pair formula becomes inverse epsilon_R times epsilon_A), and identity resolutions (the last square becomes the defining equation). For nonflat U=V=Z/2 in degree zero on the point site over Z, derived tensor has an extra negative-degree Tor term whereas ordinary tensor does not. Thus neither the arbitrary-pair counit nor the tensor of resolving maps may be cancelled; our proof never cancels either. Unboundedness causes no additional operation: both existing tools are already unbounded. Object and morphism universes of the site remain independent throughout.

Against B1–B10: there are no new unsplit nodes, all existing notions and sources are retained, TeX is written once, tag/label pairs are checked, actual searches are logged, and no false Mathlib match or attachment is asserted. Against C1–C8: every external non-elementary input is one of the three cited statements, quotes are literal statement substrings, and the only off-unit theorem uses are the generic site descent and resolution tools declared in split_report.tool_uses for maintainer judgment. Against D1–D5: no clause is moved to a new node and no proof uses a parent's conclusion; the resolving comparison, inverse, normalization and final equality are written here. Against E1–E7: the preservation assumptions, smallness, map directions and resolving-subcategory membership have been checked explicitly; I found no source or statement error. No step exceeds 2000 characters.
