## What changed
Proved `AlgebraicGeometry.FiniteSplitEtaleHypercover.exists_and_cofiltered` without changing its statement. The proof extracts the ordinary hypercover condition directly from the finite split hypercover's stored matching witnesses, applies `isEtaleHypercover_prod`, replaces the product by a finite split hypercover, and composes with its two projections. For parallel maps it takes an ordinary homotopy equalizer hypercover, replaces it by a finite split hypercover, precomposes its elementary homotopy, and inserts that homotopy into `Relation.EqvGen`.

Three separate modules isolate the missing finite split existence construction, the all-degree relative finite split replacement construction, and the ordinary endpoint path hypercover construction. These are different steps of the argument, each strictly smaller than the proved theorem; replacement is also reusable independently of cofilteredness. The original DAG node records this reduction. The two other declarations are untouched.

## Proved and sorry left
Proved `AlgebraicGeometry.FiniteSplitEtaleHypercover.exists_and_cofiltered` from the named statements, including the existing product theorem.

Sorries left in the item's module:
- `AlgebraicGeometry.FiniteSplitEtaleHypercover.exists_refinement_solving_local_requirements` (node `lem-weil-pbc-hypercover-refinement`).
- `AlgebraicGeometry.FiniteSplitEtaleHypercover.exists_truncated_refinement` (node `lem-weil-pbc-hypercover-refinement`).

New sorries:
- `AlgebraicGeometry.FiniteSplitEtaleHypercover.exists_finite_split_hypercover` (node `lem-weil-pbc-finite-split-hypercover-existence`).
- `AlgebraicGeometry.FiniteSplitEtaleHypercover.exists_finite_split_replacement` (node `lem-weil-pbc-finite-split-hypercover-replacement`).
- `AlgebraicGeometry.FiniteSplitEtaleHypercover.exists_etale_hypercover_homotopy_equalizer` (node `lem-weil-pbc-etale-hypercover-homotopy-equalizer`).

## No longer needed
Removed proof imports `Sheaf.AlgebraicGeometry.EtaleSheaves`, `Sheaf.AlgebraicGeometry.HypercoverFiniteSimplexLifting`, and `Sheaf.AlgebraicGeometry.SRMatchingObjectOneMember` from the item's module. The last two remain mathematical dependencies of the newly isolated endpoint path construction, so they are not globally pruned. The sheaf definition node `def-weil-pbc-etale-sheaves` is not needed for the sieve-valued statement: that statement already expresses its covering hypotheses directly. No globally unused module is asserted.

Complete old-minus-new direct `proof_deps` list: `def-weil-pbc-etale-sheaves`,
`def-weil-pbc-etale-site`, `lem-weil-pbc-qcqs-morphism-permanence`,
`lem-weil-pbc-hypercover-finite-simplex-lifting`, and
`lem-weil-pbc-sr-matching-object-one-member`. The site and qcqs permanence are retained
in the new existence/replacement nodes; simplex lifting and singleton comparison are
retained in the new homotopy-equalizer node. Only the sheaf node is removed from this
argument entirely. None is asserted globally unreachable.

## Where the brief, the DAG or earlier work was wrong
The existing plan declares geometric covering and finite-simplex-lifting lemmas, but lacks Lean statements supplying the inductive finite split replacement and the endpoint path hypercover itself. These constructions cannot be applications of the available covering statements alone. They have now been isolated, while their composition and the matching-witness conversion are proved in Lean.

Edge cases of the new statements were checked: empty X poses no obstruction (empty covers are allowed); an arbitrary K is not assumed quasi-compact, since relative covers are refined over the quasi-compact matching components of the new V; the endpoint construction asserts no splitting or finiteness; identical parallel maps admit a constant homotopy. The unit record `sk-prop-h2` realizes none of these nodes, so its prescribed route is not bypassed.

## New nodes
`lem-weil-pbc-finite-split-hypercover-existence`, in `Sheaf.Paper.FiniteSplitHypercoverExistence`, isolates the degree-by-degree construction with no prescribed target.

`lem-weil-pbc-finite-split-hypercover-replacement`, in `Sheaf.Paper.FiniteSplitHypercoverReplacement`, isolates relative finite split construction continued in all degrees (the original plan explicitly allows this continuation).

`lem-weil-pbc-etale-hypercover-homotopy-equalizer`, in `Sheaf.Paper.EtaleHypercoverHomotopyEqualizer`, isolates the endpoint path cover before finite replacement. It supplies an elementary homotopy, which the proved theorem precomposes and inserts into the generated equivalence relation.

## Second reading by U1

1. Compared every delivered module with the read-only repository. The three existing
   theorem signatures, binders, namespaces, and docstrings are byte-for-byte unchanged;
   only private proof imports and the body of `exists_and_cofiltered` differ. The three
   additional modules are new, and no definitions or target statements are changed.
2. All four modules compile locally in import order. Inspected all declaration bodies:
   the only five remaining sorries are precisely the named theorems listed above, and
   there are no forbidden declarations or hollow definitions. A scratch axiom check
   prints only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`; the latter
   remains because this is a reduction to open constructions, not a completed target.
3. Read each new statement and its node. Checked degree zero, the empty base, identical
   parallel maps, and non-quasi-compact terms of K. The relative construction uses finite
   covers over qcqs matching objects of V, not compactness of K. The endpoint path object
   is represented degreewise by finite limits, and its relative matching covers combine
   with U's matching covers to give absolute hypercover covers. Each new theorem isolates
   one genuine part of the argument, rather than restating cofilteredness. Repeated
   leanfinder/loogle/grep searches with different terms and inspected local Mathlib,
   Sheaf, and upstream declarations: only zero/one-step analogues were found.
4. Read the proof downward: stored matching witnesses, ordinary product, finite split
   replacement, endpoint homotopy, and `Homotopy.precomp`/`EqvGen.rel` are sufficient.
   All public imports are needed by signatures; the added construction imports are plain
   proof imports. Completed the old-minus-new dependency list under No longer needed.
   The unchanged `sk-prop-h2` unit realization contains none of these nodes, and its
   Kummer/Brauer route is preserved. No shorter existing all-degree result was found.
5. Checked the original node's proof steps and dependency union, all three new nodes'
   fields, and their verbatim Lean statements. Verdict: consistent. The two untouched
   open theorem plans remain in the original node; the new nodes account for each new
   sorry, with source and full prose argument.

Changes made in this reading: made the three new theorem docstring proofs standalone
(the existence proof lacked its geometric step, and replacement referred to absent
steps and did not spell out all-degree naturality); expanded path-object representability
and the relative-to-absolute matching-cover argument; synchronized the latter two node
proofs; recorded second-search evidence; and completed the direct pruning inventory.
The Lean proof terms and all existing signatures remain unchanged.

Source spot checks: [Stacks 0DAV](https://stacks.math.columbia.edu/tag/0DAV) for the split
extension, [Stacks 094K](https://stacks.math.columbia.edu/tag/094K) for finite index sets,
and [Stacks 01GS](https://stacks.math.columbia.edu/tag/01GS) for the endpoint pullback and
prism matching-cover argument. The cited local Stacks tex file is absent on this machine,
so these checks used the official online statements and proofs.
