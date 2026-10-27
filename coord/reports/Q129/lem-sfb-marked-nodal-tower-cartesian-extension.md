## Worker report

Files written: `dag/nodes/sec-six-functors-basics/lem-sfb-marked-nodal-tower-cartesian-extension.json`, the existing statement, split into nine steps. No new nodes and no new Mathlib leaves. `citations.json` contains a verbatim statement quotation for every step/use pair. `searches.jsonl` retains the actual search log; the item retains its inherited searches and appends the five current searches.

Attachments: none. Searches of `lean/WeilConjectures` for the blueprint tag and marked/nodal/tower terminology found no declaration stating the item; cartesian extension-by-zero declarations concern a different notion.

WANTED: local archive `literature/de-jong-families-curves-alterations-1997.pdf`, Situation 5.8 and Theorem 5.9, printed pp.615--617, for this item. The primary Numdam scan at https://www.numdam.org/item/10.5802/aif.1575.pdf was read online, PDF pages 17--19, including the quasi-split definition preceding Lemma 5.7. No repository or literature file was written or downloaded. The explicit assembly proof is marked agent-written: the final paragraph of Theorem 5.9 delegates the verification to the reader.

What was wrong or missing: the item had no proof. Its statement is retained unchanged: no STATEMENT-DISPUTED issue was found. Its explicit integrality and finite-function-field hypotheses are used as hypotheses, without trying to obtain them from an arbitrary base change. The inherited blueprint ancestor is null, as confirmed by `blueprint_refs.py ancestor`; its existing provenance and via chain are preserved, and the precise Situation 5.8 / Theorem 5.9 extraction is recorded. The unit and chapter files were read and left untouched. This auxiliary node is not the key statement of the unit, so no unit realization is set.

What remains unfinished: no part of this item's stage-1 split. Dependencies retain their own current proof status. No Lean was written and no compiler, Lake, build, git command, or local preflight/check_dag/review_split was run.

## Searches and reuse

Before writing, searched the whole DAG by statements/titles and the tags and notions nodal, quasi-split, projective base change, H-projective composition, finite type composition, surjective base change, geometric integrality, and projective bundles. Read the candidate statements, especially `lem-trf-projective-nodal-family-geometry`, `lem-sfb-nodal-birational-base-change-geometry`, `lem-sfb-flat-curve-pullback-function-field` and `lem-sfb-marked-nodal-boundary-control`. The birational-base-change lemma assumes a smooth birational new base, which this item does not have. The function-field pullback lemma is unnecessary because integrality and finiteness are assumed here. Reuse the arbitrary-base-change persistence clause of the boundary-control lemma instead; its auxiliary closed subset can be empty, and its newly constructed exceptional subset is not substituted for the given D.

Ran whole-blueprint searches for nodal, projective base change, geometrically integral, marked, H-projective and free projective bundle. No imported node states the whole cartesian-extension item. The reusable definition of geometric integrality quantifies over every field extension, so its further-extension argument is elementary and needs no new stability lemma.

Current Mathlib searches used the prescribed msearch command: two semantic LeanFinder formulations, LeanSearch, Loogle on Flat and pullback, and grep of AlgebraicGeometry for quasi-split/nodal sections/marked curves. Hits were read: Weierstrass nonsingularity/base-change formulas, smooth-base-change stability, generic Flat pullback instances, pullback residue-field tensor squares and rational maps. None states the full item. The stronger pullback integrality hit requires all fibres geometrically integral, unlike nodal families here. There are no new nodes whose searches or tag-overlap distinctions remain to discharge.

## Not duplicates

No new nodes. In particular the existing marked-nodal boundary-control, H-projective composition, finite-type composition/base-change, projective-base-change, surjective-base-change, smooth-base-change and free-projective-bundle comparison statements are cited directly.

## Review by Q129

I read the primary de Jong scan at Situation 5.8 and the final cartesian construction of Theorem 5.9, together with the quasi-split definition immediately before Lemma 5.7. I checked the local Stacks texts in `curves.tex` for Tag 0C5B (`lemma-base-change-nodal-family`) and in `morphisms.tex` for 01WF (`lemma-H-projective-base-change`), 01WE (`lemma-H-projective-composition`), 01W8 (`definition-projective`), 01WC (`lemma-locally-projective-proper`), 01VB (`lemma-base-change-smooth`), 01S1 (`lemma-base-change-surjective`) and 01T3 (`lemma-composition-finite-type`). For the comparison of projective-space and bundle conventions I read the existing free-bundle comparison statement and the Stacks explanation that finite projective space is a projective bundle. There are no new nodes requiring a separate source review.

Step 1 takes exactly the existence, uniqueness and functoriality of the fibre product from `def-pc-fibre-product`. The compatibility equation is written out before the group action is defined; both group laws are checked on both projections. The same argument constructs the sections. It works for nonfaithful actions and field automorphisms, since all maps are maps of schemes with their stated compatible semilinearity.

Step 2 takes the arbitrary-base-change clause, including rational nodes and branches, from `lem-sfb-marked-nodal-boundary-control`. I checked all its family hypotheses against the item and used the empty auxiliary closed subset to discharge its generic boundary condition. I do not use its existential choice of an exceptional base subset. I corrected the draft to explicitly verify finite type of W over F: H-projectivity gives properness by `lem-kun-projective-implies-proper`; `def-weil-proper-morphism` supplies finite type; `lem-sfb-finite-type-composition-base-change` composes p with the given structure map of P. This fills a tower condition that would otherwise be only implicit. I also made closedness explicit: properness gives separatedness, and the exact statement of `lem-weil-pbc-section-separated-closed-immersion` makes every old and new section a closed immersion. Induction by finite unions and inverse images makes every boundary closed. I read its source, Schemes Tag 01KT (`lemma-section-immersion`), including the separatedness hypothesis.

Step 3 takes precisely the smoothness clause (2) of `lem-pc-proper-base-change`, both over the given good open and at the generic point. `def-sfb-dominant-function-field-map` supplies the canonical generic-field map for dominant h; `def-pc-fibre-product` identifies the iterated fibre product, and `def-pc-geometrically-irreducible` supplies integrality after every further field extension. Dominance is essential here: arbitrary base change alone does not preserve smoothness of the generic fibre. I checked that h has this hypothesis and that P and B are integral.

Step 4 uses only the fibre-product universal property and elementary inverse-image operations. Pulling back a section image really gives its pulled-back section, so the boundary calculation holds on scheme points without treating fibre-product points as plain pairs. The equality vq=hp proves the displayed inverse-image identity. Stability uses the union of the markings, allowing permutation; no individual section is asserted fixed. This step does not invoke an unjustified claim about reduced scheme structures.

Step 5 uses `lem-kun-projective-implies-proper`, the proper/finite-type definitions, and `def-pc-projective-morphism` to check the precise quasi-compactness premise of `lem-pc-projective-base-change`. That node's convention is H-projective plus quasi-compact, so its conclusion really does supply H-projectivity of q. The two projections are interchanged by the stated universal property, rather than silently using the wrong projection.

Step 6 uses the exact projection conclusion of `lem-weil-pbc-surjective-base-change` with f=h and base change v. The source h is surjective by hypothesis. `lem-trf-surjective-morphism-composition` then applies twice, because c and pi too are surjective. `def-sfb-dominant-function-field-map` fixes the induced germ maps used in the following step. Step 7 is the elementary spanning argument for finite-dimensional field extensions as defined by `def-pc-field-tower`; birational pi gives the required identification with k(X). No finiteness of k(P)/k(B), not assumed by this item, is used.

Step 8 uses exactly `lem-trf-h-projective-composition`, twice, after all three H-projectivity hypotheses are available. Step 9 uses the isomorphism in `lem-trf-free-projective-bundle-base-change-space` and the definition `def-trf-projective-bundle-morphism`; the finite free module gives an allowed finite-type quasi-coherent bundle. It does not need a global ample module on X or a general projective-bundle composition theorem with additional qcqs hypotheses.

I checked B--E of delivery-errors against the actual files: no new statement-only nodes, hollow replacement or clause relabelling; every non-elementary fact is an existing cited statement, not an inference from a definition; quotations are copied from statements and checked as substrings. The cited dependency closures were checked for a path back to this item and none was found. All steps are below 2000 characters. The steps marked elementary are the explicit universal-property/action calculation, boundary inverse images and the finite spanning-set calculation, each with its defining statement cited. Generic off-unit geometry tools are declared in split_report.tool_uses, not the maintainer-owned field.

Small cases checked: r=0 gives one curve over Spec F; no markings gives M=M'=empty and boundary p-inverse Z_r; D=empty gives smoothness everywhere; empty Z makes containment vacuous; trivial and nonfaithful groups need no faithfulness argument; permuted sections only give union stability; inseparable finite field extensions do not enter any separability argument. Integrality assumptions rule out the empty total space. Reducible nodal special fibres are allowed: only the generic fibre is geometrically integral. No regularity of W or trivial action on branches/sections was introduced.

The standalone remote review_split check passed. The first complete dry run passed at 6dc3139441b before the additional closed-boundary clarification. A final dry run is required after that clarification and before pushing.


## Repair of return at 667de3c9a65 (2026-10-23)

The return at `coord/returns/Q129.md` identifies the returned branch head as
`667de3c9a65` and reports a side-completion/live-DAG promotion failure, not a
mathematical objection. I compared the retained delivered node with the current
read clone. The current item is still `unsplit`, has an empty proof, and has no
stage-1 repair note. Its statement, statement dependencies, source, creation
record and blueprint provenance match the retained item. The delivery command
builds on current `origin/sheaf-dag`; I did not change any repository or launcher
file or run a git command.

I reread all eighteen existing proof dependencies from the current DAG, rather
than assuming that the old quotations certified their whole statements. All
24 retained step/citation quotations remain verbatim. In Step 2 the current
boundary-control statement still explicitly gives persistence under every base
change, and still allows an empty auxiliary closed subset. Thus the given D is
retained, and smoothness of the generic fibre is still checked separately using
dominance in Step 3. The properness, finite-type composition, separated-section,
smooth-base-change and projective-base-change statements have exactly the
hypotheses used in Steps 2, 3 and 5. The free-projective-bundle comparison still
provides a canonical isomorphism over any base scheme, as used in Step 9. No
retained quote became invalid on the current DAG, and no argument was removed.

The concrete adjustment to the split is reuse of the current definition
`def-sfb-quasi-split-nodal-fibres`, which the retained item had not cited. Its
statement says exactly that every nonsmooth fibre point is rational, has exactly
two points above it in the reduced normalization, and both are rational over the
base residue field. I added its reference beside the item's unchanged inline
condition, added it to `stmt_deps` and Step 2's `uses`, updated `proof_deps`, and
copied its actual statement into `citations.json`. This is an explicit definition
reference, not an added hypothesis. In particular it allows a self-node and does
not replace quasi-split by the stronger smooth-component split condition.
There are still no new nodes or Mathlib leaves. The five logged Mathlib queries
and their results were reread and retained: neither the mathematical statement
nor their search question changed, so they were not repeated.

### Continued review by Q129

For the repaired reading I reopened de Jong's primary Numdam scan, the quasi-split
definition immediately before Lemma 5.7 on pp.614--615, Situation 5.8 on pp.615--616,
and the final cartesian construction of Theorem 5.9 on p.617. The explicit
rational-node/normalization-branch definition agrees with that source and with
the item's inline definition. The source's delegated final verification is
still supplied by the retained action, boundary, generic-fibre and field-span
arguments. I also reopened Stacks curves.tex `lemma-base-change-nodal-family`
(0C5B), morphisms.tex `definition-projective` (01W8),
`lemma-locally-projective-proper` (01WC), `lemma-H-projective-composition`
(01WE), `lemma-H-projective-base-change` (01WF), `lemma-base-change-smooth`
(01VB), `lemma-base-change-surjective` (01S1),
`lemma-composition-finite-type` (01T3), and schemes.tex
`lemma-section-immersion` (01KT). These confirm the unchanged citations and
projectivity convention checks in the original review above.

I rechecked B--E: there is no new-node relabelling or duplicate; each use has a
statement quotation; Step 2 does not borrow the boundary-control proof;
Steps 3 and 7 do not infer integrality or function-field finiteness from arbitrary
base change. Steps 1 and 4 are the displayed universal-property and inverse-image
arguments. All steps remain below 2000 characters, with no hidden long-step
comparison. Empty markings, r=0, D empty, nonfaithful actions, a rational self-node
and inseparable finite field extensions require no change to any argument. The
whole item's statement remains mathematically unchanged. The initial repair dry
run, before adding this definition reference and repair report, passed at
`a843c0632ed`. A fresh final dry run follows these edits before pushing.
